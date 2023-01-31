/*	The MIT License (MIT)
 *
 *	Copyright (c) 2019-2023 Rick Workman
 *
 *	Permission is hereby granted, free of charge, to any person obtaining a copy
 *	of this software and associated documentation files (the "Software"), to deal
 *	in the Software without restriction, including without limitation the rights
 *	to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 *	copies of the Software, and to permit persons to whom the Software is
 *	furnished to do so, subject to the following conditions:
 *
 *	The above copyright notice and this permission notice shall be included in all
 *	copies or substantial portions of the Software.
 *
 *	THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 *	IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 *	FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 *	AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 *	LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 *	OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 *	SOFTWARE.
 */

%
% API function for executing primitives
%
% evalNode(+primitive_name, ?persistence_flag, +$(inputs..), -$(outputs..))
%
evalNode(Op, P, Is, R) :-
	g_inc('clpBNR:evalNode'),  % count of primitive calls
	narrowing_op(Op, P, Is, R),
	!.
evalNode(Op, _, _, _):-
	g_inc('clpBNR:evalNodeFail'),  % count of primitive call failures
	debugging(clpBNR, true),  % fail immediately unless debug=true
	current_node_(C),
	debug_clpBNR_("** fail ** ~w.",C),
	fail.

sandbox:safe_global_variable('clpBNR:evalNode').
sandbox:safe_global_variable('clpBNR:evalNodeFail').

clpStatistics :-
	g_assign('clpBNR:evalNode',0),
	g_assign('clpBNR:evalNodeFail',0),
	fail.  % backtrack to reset other statistics.

clpStatistic(narrowingOps(C)) :- g_read('clpBNR:evalNode',C).

clpStatistic(narrowingFails(C)) :- g_read('clpBNR:evalNodeFail',C).

% SWIP optimization for non_empty/2
:- if(current_predicate(system:expand_goal/2)).

goal_expansion(non_empty(L,H), L =< H).

:- endif.

%
% non-empty interval test
%
non_empty((L,H)) :- non_empty(L,H).
non_empty(L,H) :- L =< H.                      % non-empty

%
% interval category: non-negative (includes zero), non-positive, or split (contains 0)
%
intCase(C, (L,H)) :-
	( L>=0 -> C=p            % non-negative
	; H=<0 -> C=n            % non-positive
	;         C=s            % split
	).

%
% Z := X ^ Y  (interval intersection)
%
^((Xl,Xh), (Yl,Yh), (Zl,Zh)) :-
	Zl is max(Xl, Yl), Zh is min(Xh, Yh),
	non_empty(Zl,Zh).

%
% Z := X \/ Y (interval union)
%
union_((Xl,Xh),(Yl,Yh),(Zl,Zh)) :-
	Zl is min(Xl,Yl), Zh is max(Xh,Yh).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Relational Operations (narrowing operations)
%
:- discontiguous clpBNR:narrowing_op/4.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% integral (contract to integer bounds) - optimized version of (int,P,$(1,X),_)

narrowing_op(integral, P, $(X), $(NewX)) :-
	integral_(X,NewX).
	
integral_((Xl,Xh),(NXl,NXh)) :-
	NXl is ceiling(Xl), NXh is floor(Xh),
	NXl=<NXh.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z == integer(X) % (Z boolean) 
%  true if X is an integer point, false if it doesn't contain an integer
%  else if true, narrows X to integer bounds

narrowing_op(int, P, $(Z,X), $(NewZ,NewX)) :-
	int_(Z,X,P,NewZ,NewX).
	
int_(Z,X,p,NewZ,X) :-                       % persistent cases
	X = (Xl,Xh),
	(Xl == Xh                           % point value?
	 -> (integer(Xl) -> B = 1 ; B = 0)  % yes, true if integer else false
	 ;  ceiling(Xl) > floor(Xh),        % no, and X doesn't contain an integer
	    B = 0 
	),
	!,  % succeed, persistent
	^(Z,(B,B),NewZ).
	
int_(Z,X,P,NewZ,NewX) :-                    % possible narrowing case
	(Z == (1,1) 
	 -> integral_(X,NewX),              % Z true, narrow X to integers
	    NewZ = Z
	 ;  NewX = X,                       % Z false or indeterminate, no change to X
	    ^(Z,(0,1),NewZ)                 % Z boolean
	).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z==(X==Y)  % (Z boolean)

narrowing_op(eq, P, $(Z,X,Y), Out) :-
	(^(X,Y,New)                       % intersect?
	 -> (Z == (1,1)
	     -> Out = $(Z,New,New), 
	        New = (L,H),
	        (L < H -> true ; P = p)   % persistent if a point
	     ; % intersect and Z false or indeterminate, all things possible
	        ( X = (Xl,Xh), Y = (Yl,Yh), 
	          Xl =:= Xh, Yl =:= Yh, Xl =:= Yl  % X and Y same point
	         -> ^(Z,(1,1),NewZ),      % Z true
	            P = p                 % persistant
	         ;  ^(Z,(0,1),NewZ)       % ensure Z boolean
	        )
	        Out = $(NewZ,X,Y)
	    )
	 ;  % X and Y do not intersect  
	    ^(Z, (0,0), NewZ),            % fail primitive if Z cannot be false
	    Out = $(NewZ,X,Y), P = p      % persistent
	 ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z==(X<>Y)  % (Z boolean, X,Y integer)

narrowing_op(ne, P, $(Z,X,Y), Out) :-
	(^(X,Y,(L,H))
	 -> (Z = (1,1)
	     -> ne_int_(X,Y,NewX),        % narrow X if Y is a point and a bound of X (always succeeds but may not narrow
	        ne_int_(Y,NewX,NewY),     % narrow Y if NewX is a point and a bound of Y (always succeeds but may not narrow)	
	        Out = $(Z,NewX,NewY)
         ;  (X == Y, L == H -> B = (0,0), P = p ;  B = (0,1)) 
            ^(Z,B,NewZ),
            Out = $(NewZ,X,Y)
         )	
	 ;  % X and Y do not intersect
	    ^(Z, (1,1), NewZ),            % true and 
	    P = p,                        % persistent
	    Out = $(NewZ,X,Y)
	).

% narrow X and Y given Y <> X,  where Y and X are integer intervals (enforced elsewhere)
ne_int_((X,H), (X,X), (NewL,H)) :- !,  % X is a point,  and low bound of Y
	NewL is X+1, NewL=<H.
ne_int_((L,X), (X,X), (L,NewH)) :- !,  % X is a point,  and high bound of Y
	NewH is X-1, L=<NewH.
ne_int_(Y, X, Y).                      % no narrowing

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z==(X=<Y)  % (Z boolean)

narrowing_op(le, P, $(Z, X, Y), Out) :-
	X = (Xl,Xh), Y = (Yl,Yh),
	(Xh =< Yl
	 -> ^(Z,(1,1),NewZ), P = p, Out = $(NewZ,X,Y)      % persistent X =< Y
	 ;  (Yh < Xl
	     -> ^(Z,(0,0),NewZ), P = p, Out = $(NewZ,X,Y)  % persistent Y < X	
	     ;  (Z == (1,1)                                % if {X =< Y}, can narrow X and Y
	         -> ^(X, (-1.0Inf,Yh), (NXl,NXh)),         % NewX := X ^(NI,Yh) 
	            ^(Y, (NXl,1.0Inf), NewY),              % NewY := Y ^(Xl,PI)
	            Out = $(Z,(NXl,NXh),NewY)
	         ;  ^(Z,(0,1),NewZ),                       % Z false or indeterminate
	            Out = $(NewZ,X,Y)
	        )
	    )
	).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z==(X<Y)  % (Z boolean) generally unsound on reals but possibly useful for minima/maxima

narrowing_op(lt, P, $(Z, X, Y), Out) :-
	X = (Xl,Xh), Y = (Yl,Yh),
	(Xh < Yl
	 -> ^(Z,(1,1),NewZ), P = p, Out = $(NewZ,X,Y)      % persistent X < Y
	 ;  (Yh =< Xl
	     -> ^(Z,(0,0),NewZ), P = p, Out = $(NewZ,X,Y)  % persistent Y =< X	
	     ;  (Z == (1,1)                                % if {X < Y}, can narrow X and Y
	         -> next_lt_(Yh,-1,YhD),                   % YhD is next downward value from Yh
	            ^(X, (-1.0Inf,YhD), (NXl,NXh)),        % NewX := (Xl,Xh) ^(NInf,YhD)
	            next_lt_(NXl,1,NXlU),                  % NXlU is next upward value from NXl
	            ^((Yl,Yh), (NXlU,1.0Inf), (NYl,NYh)),  % NewY := (Yl,Yh) ^(NXlU,PInf)
	            (NXh < NYl -> P=p ; true),             % persistent due to increment?
	            Out = $(Z,(NXl,NXh),(NYl,NYh))
	         ;  ^(Z,(0,1),NewZ),                       % Z false or indeterminate
	            Out = $(NewZ,X,Y)
	        )
	    )
	).

% Note: can't narrow an infinite bound, minimize change to bound
% Repeat, not sound on reals (uses nexttoward, missing values between floats)
next_lt_( 1.0Inf, _,  1.0Inf) :- !.
next_lt_(-1.0Inf, _, -1.0Inf) :- !.
next_lt_(V, -1, NV) :- NV is max(V-1,nexttoward(V,-1.0Inf)).  % integers will get sorted out with `integral`
next_lt_(V,  1, NV) :- NV is min(V+1,nexttoward(V, 1.0Inf)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z==(X<=Y)  % inclusion, constrains X to be subinterval of Y (Z boolean)

narrowing_op(in, P, $(Z, X, Y), $(NewZ, NewX, Y)):-
	% Only two cases: either X and Y intersect or they don't.
	(^(X,Y,NewX)   % NewX is intersection of X and Y
	 -> ^(Z,(1,1),NewZ)      % X and Y intersect, Z must always be true going forward
	 ;  ^(Z,(0,0),NewZ),     % X and Y don't intersect, Z must be false
	 	NewX = X,            % no change in X
	    P=p                  % persistent, since X and Y can never intersect
	).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z==X+Y

narrowing_op(add, _, $((Zl,Zh), (Xl,Xh), (Yl,Yh)), $((NZl,NZh), (NXl,NXh), (NYl,NYh))) :-
	NZl is max(Zl, roundtoward( Xl+Yl,  to_negative)),       % NewZ := Z ^ (X+Y),
	NZh is min(Zh, roundtoward( Xh+Yh,  to_positive)),
	non_empty(NZl,NZh),
	% Note: subtraction done by adding minus values so rounding mode consistent
	% during any numeric type conversion.
	NXl is max(Xl, roundtoward(NZl+(-Yh),  to_negative)),    % NewX := X ^ (NZ-Y),
	NXh is min(Xh, roundtoward(NZh+(-Yl),  to_positive)),
	non_empty(NXl,NXh),
	NYl is max(Yl, roundtoward(NZl+(-NXh), to_negative)),    % NewY := Y ^ (NZ-NX).
	NYh is min(Yh, roundtoward(NZh+(-NXl), to_positive)),
	non_empty(NYl,NYh).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z==X*Y

narrowing_op(mul, _, $(Z,X,Y), $(NewZ, NewX, NewY)) :-
	intCase(Cx,X),
	intCase(Cy,Y),
	once(multCase(Cx,Cy,X,Y,Z,NewZ)),  % NewZ := Z ^ (X*Y)
	intCase(CNz,NewZ),
	odivCase(CNz,Cx,NewZ,X,Y,Yp),      % Yp := Y ^ (Z/X),
	intCase(Cyp,Yp),
	odivCase(CNz,Cyp,NewZ,Yp,X,NewX),  % NewX := X ^ (Z/Yp),
	% if X narrowed it may be necessary to recalculate Y due to non-optimal ordering.
	(Y == Yp, X \== NewX               % if Y didn't narrow and X did
	 -> intCase(CNx,NewX),
	    odivCase(CNz,CNx,NewZ,NewX,Y,NewY)  % re calculate: NewY := Y ^ NewZ/NewX
	 ;  NewY = Yp
	).

%
% * cases ("Interval Arithmetic: from Principles to Implementation", Fig. 3)
%
%multCase(z,_, X, _, _, X) :- !.  % X==0
%multCase(_,z, _, Y, _, Y).       % Y==0

multCase(p,p, (Xl,Xh), (Yl,Yh), (Zl,Zh), (NZl,NZh)):- 
    NZl is max(Zl,roundtoward(Xl*Yl,to_negative)),
    NZh is min(Zh,roundtoward(Xh*Yh,to_positive)),
    non_empty(NZl,NZh).
multCase(p,n, (Xl,Xh), (Yl,Yh), (Zl,Zh), (NZl,NZh)):- 
    NZl is max(Zl,roundtoward(Xh*Yl,to_negative)),
    NZh is min(Zh,roundtoward(Xl*Yh,to_positive)),
    non_empty(NZl,NZh).
multCase(n,p, (Xl,Xh), (Yl,Yh), (Zl,Zh), (NZl,NZh)):- 
    NZl is max(Zl,roundtoward(Xl*Yh,to_negative)),
    NZh is min(Zh,roundtoward(Xh*Yl,to_positive)),
    non_empty(NZl,NZh).
multCase(n,n, (Xl,Xh), (Yl,Yh), (Zl,Zh), (NZl,NZh)):- 
    NZl is max(Zl,roundtoward(Xh*Yh,to_negative)),
    NZh is min(Zh,roundtoward(Xl*Yl,to_positive)),
    non_empty(NZl,NZh).

multCase(p,s, (Xl,Xh), (Yl,Yh), (Zl,Zh), (NZl,NZh)):-
    NZl is max(Zl,roundtoward(Xh*Yl,to_negative)),
    NZh is min(Zh,roundtoward(Xh*Yh,to_positive)),
    non_empty(NZl,NZh).
multCase(n,s, (Xl,Xh), (Yl,Yh), (Zl,Zh), (NZl,NZh)):-
    NZl is max(Zl,roundtoward(Xl*Yh,to_negative)),
    NZh is min(Zh,roundtoward(Xl*Yl,to_positive)),
    non_empty(NZl,NZh).
multCase(s,p, (Xl,Xh), (Yl,Yh), (Zl,Zh), (NZl,NZh)):-
    NZl is max(Zl,roundtoward(Xl*Yh,to_negative)),
    NZh is min(Zh,roundtoward(Xh*Yh,to_positive)),
    non_empty(NZl,NZh).
multCase(s,n, (Xl,Xh), (Yl,Yh), (Zl,Zh), (NZl,NZh)):-
    NZl is max(Zl,roundtoward(Xh*Yl,to_negative)),
    NZh is min(Zh,roundtoward(Xl*Yl,to_positive)),
    non_empty(NZl,NZh).

multCase(s,s, (Xl,Xh), (Yl,Yh), (Zl,Zh), (NZl,NZh)):-
    NZl is max(Zl,min(roundtoward(Xl*Yh,to_negative),roundtoward(Xh*Yl,to_negative))),
    NZh is min(Zh,max(roundtoward(Xl*Yl,to_positive),roundtoward(Xh*Yh,to_positive))),
    non_empty(NZl,NZh).

%
% / cases ("Interval Arithmetic: from Principles to Implementation", Fig. 4)
% Tricky handling the "zero" cases - returns universal interval when no narowing possible:
%	1. denominator is zero or contains zero (z and s)
%	2. denominator is bounded by zero (p and n) and numerator contains zero (see numeric guards)
% Numeric guards check for 0/0, e.g., p,p -> Xh+Yh>0

odivCase(p,p, (Xl,Xh), (Yl,Yh), (Zl,Zh), (NZl,NZh)) :-
	sign(Yl)+sign(Xl) > 0, !,  % X > 0 or Y > 0
	NZl is max(Zl,roundtoward(Xl/Yh,to_negative)),
	NZh is min(Zh,roundtoward(Xh/max(0.0,Yl),to_positive)),
	non_empty(NZl,NZh).
odivCase(p,n, (Xl,Xh), (Yl,Yh), (Zl,Zh), (NZl,NZh)) :-
	sign(Xl)-sign(Yh) > 0, !,  % X > 0 or Y < 0
	NZl is max(Zl,roundtoward(Xh/min(-0.0,Yh),to_negative)),
	NZh is min(Zh,roundtoward(Xl/Yl,to_positive)),
	non_empty(NZl,NZh).
odivCase(p,s, (Xl,Xh), (Yl,Yh), (Zl,Zh), (NZl,NZh)) :-
	Xl > 0, !,     % X > 0
	ZIl is roundtoward(Xl/Yh,to_negative),
	ZIh is roundtoward(Xl/Yl,to_positive),
	(Zl > ZIh -> NZl is max(Zl,ZIl) ; NZl = Zl),  % similar to ^/3
	(Zh < ZIl -> NZh is min(Zh,ZIh) ; NZh = Zh),
	non_empty(NZl,NZh).

odivCase(n,p, (Xl,Xh), (Yl,Yh), (Zl,Zh), (NZl,NZh)):-
	sign(Yl)-sign(Xh) > 0, !,  % X < 0 or Y > 0
	NZl is max(Zl,roundtoward(Xl/max(0.0,Yl),to_negative)),
	NZh is min(Zh,roundtoward(Xh/Yh,to_positive)),
	non_empty(NZl,NZh).
odivCase(n,n, (Xl,Xh), (Yl,Yh), (Zl,Zh), (NZl,NZh)) :-
	sign(Yh)+sign(Xh) < 0, !,  % X < 0 or Y < 0
	NZl is max(Zl,roundtoward(Xh/Yl,to_negative)),
	NZh is min(Zh,roundtoward(Xl/min(-0.0,Yh),to_positive)),
	non_empty(NZl,NZh).
odivCase(n,s, (Xl,Xh), (Yl,Yh), (Zl,Zh), (NZl,NZh)) :-
	Xh < 0, !,     % X < 0
	ZIl is roundtoward(Xh/Yl,to_negative),
	ZIh is roundtoward(Xh/Yh,to_positive),
	(Zl > ZIh -> NZl is max(Zl,ZIl) ; NZl = Zl),  % similar to ^/3
	(Zh < ZIl -> NZh is min(Zh,ZIh) ; NZh = Zh),
	non_empty(NZl,NZh).

odivCase(s,p, (Xl,Xh), (Yl,Yh), (Zl,Zh), (NZl,NZh)) :-
	Yl > 0, !,     % Y > 0
	NZl is max(Zl,roundtoward(Xl/Yl,to_negative)),
	NZh is min(Zh,roundtoward(Xh/Yl,to_positive)),
	non_empty(NZl,NZh).
odivCase(s,n, (Xl,Xh), (Yl,Yh), (Zl,Zh), (NZl,NZh)) :-
	Yh < 0, !,     % Y < 0
	NZl is max(Zl,roundtoward(Xh/Yh,to_negative)),
	NZh is min(Zh,roundtoward(Xl/Yh,to_positive)),
	non_empty(NZl,NZh).

odivCase(_,_,       _,       _,       Z,         Z).                 % all other cases, no narrowing

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z==min(X,Y)    Z==max(X,Y)

narrowing_op(min, _, $((Zl,Zh),(Xl,Xh),(Yl,Yh)), New) :-
	Z1l is max(Zl,min(Xl,Yl)),  % Z1 := Z ^ min(X,Y),
	Z1h is min(Zh,min(Xh,Yh)),
	minimax((Zl,1.0Inf), $((Z1l,Z1h),(Xl,Xh),(Yl,Yh)), New).

narrowing_op(max, _, $((Zl,Zh),(Xl,Xh),(Yl,Yh)), New) :-
	Z1l is max(Zl,max(Xl,Yl)),  % Z1 := Z ^ max(X,Y),
	Z1h is min(Zh,max(Xh,Yh)),
	minimax((-1.0Inf,Zh), $((Z1l,Z1h),(Xl,Xh),(Yl,Yh)), New).

minimax(_, $(Z,X,Y), $(New, X, New)) :-          % Case 1, X not in Z1
	\+(^(Z,X,_)), !,                           % _ := Z1 \^ X,
	^(Y,Z,New).                                % New := Y ^ Z1.

minimax(_, $(Z,X,Y), $(New, New, Y)) :-          % Case 2, Y not in Z1
	\+(^(Z,Y,_)), !,                           % _ := Z1 \^ Y,
	^(X,Z,New).                                % New := X ^ Z1.

minimax(Zpartial, $(Z,X,Y), $(Z, NewX, NewY)) :- % Case 3, overlap
	^(X,Zpartial,NewX),                        % NewX := X ^ Zpartial,
	^(Y,Zpartial,NewY).                        % NewY := Y ^ Zpartial.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z==abs(X)

narrowing_op(abs, _, $(Z,X), $(NewZ, NewX)) :-
	intCase(Cx,X),
	absCase(Cx,X,Z,NewZ), !,
	non_empty(NewZ),
	intersect_regions_(X,NewZ,NewX),
	non_empty(NewX).

%
% intersect and join Z with positive and negative regions of X
%
intersect_regions_(Z,X,NewZ) :-
	(^(Z,X,ZPos) -> true ; empty_interval(ZPos)),  % positive Z region
	(-(X,Z,ZNeg) -> true ; empty_interval(ZNeg)),  % negative Z region
	union_(ZPos,ZNeg,NewZ).

% NZ := Z ^ -X (unary minus)
-((Xl,Xh), (Zl,Zh), (NZl,NZh)) :-
	NZl is max(Zl,-Xh), NZh is min(Zh,-Xl),
	NZl =< NZh.  % no infinity/overflow check required

%
% abs(X) cases
%
absCase(p, (Xl,Xh), (Zl,Zh), (NZl,NZh)) :- NZl is max(Zl,Xl),  NZh is min(Zh,Xh).
absCase(n, (Xl,Xh), (Zl,Zh), (NZl,NZh)) :- NZl is max(Zl,-Xh), NZh is min(Zh,-Xl).
absCase(s, (Xl,Xh), (Zl,Zh), (NZl,NZh)) :- NZl is max(Zl,0),   NZh is min(Zh,max(-Xl,Xh)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z== -X

narrowing_op(minus, _, $((Zl,Zh),(Xl,Xh)), $((NZl,NZh),(NXl,NXh))) :-
	NZl is max(Zl,-Xh), NZh is min(Zh,-Xl),    % NewZ := Z ^ -X, no empty check required
	NXl is max(Xl,-NZh), NXh is min(Xh,-NZl).  % NewX := X ^ -Z, no empty check required

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z== sqrt(X)  (Z is positive root of positive X)

narrowing_op(sqrt, _, $((Zl,Zh),(Xl,Xh)), $((NZl,NZh),(NXl,NXh))) :-
	Xh>=0, Xl1 is max(0,Xl),  % narrow X to positive range
	NZl is max(max(0,Zl),roundtoward(sqrt(Xl1),to_negative)),
	NZh is min(Zh,roundtoward(sqrt(Xh),to_positive)),
	non_empty(NZl,NZh),
	NXh is min(Xh,roundtoward(NZh*NZh,to_positive)),
	NXl is max(Xl,-NXh),
	non_empty(NXl,NXh).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z== exp(X)

narrowing_op(exp, _, $((Zl,Zh),(Xl,Xh)), $((NZl,NZh),(NXl,NXh))) :-
	NZl is max(Zl,roundtoward(exp(Xl),to_negative)),
	NZh is min(Zh,roundtoward(exp(Xh),to_positive)),
	non_empty(NZl,NZh),
	NXl is max(Xl,roundtoward(log(NZl),to_negative)),
	NXh is min(Xh,roundtoward(log(NZh),to_positive)),
	non_empty(NXl,NXh).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z== X**Y

narrowing_op(pow, P, $(Z,X,Y), $(NewZ,NewX,NewY)) :-
	powr_(P, Z,X,Y, NewZ,NewX,NewY).

powr_(p, Z,X,Y, NewZ,NewX,NewY) :-                  % (persistant) special cases
	Z = (Zl,Zh), X = (Xl,Xh), Y = (Yl,Yh), 
	( equals_one(Xl), equals_one(Xh) ->             % 1**Y == Z
		!, ^(Z,(1,1),NewZ), NewX = X, NewY = Y      %  ==> Z := (1,1)
	; equals_one(Zl), equals_one(Zh) ->             % X**Y == 1 , X doesn't contain 1 or -1
		((Xl =< -1,-1 =< Xh ; Xl =< 1,1 =< Xh)
		 -> fail                                    % fail to use general pt_powrCase
		 ;  !, NewZ = Z, NewX = X, ^(Y,(0,0),NewY)  %  ==> Y := (0,0)
		)
	; equals_zero(Yl), equals_zero(Yh) ->           % X**0 == Z
		!, ^(Z,(1,1),NewZ), NewX = X, NewY = Y      %  ==> Z := (1,1)
	).

powr_(_, Z,X,(R,R), NewZ,NewX,NewY) :- rational(R,N,D), !,   % R = rational point exponent
	N1 is N mod 2, D1 is D rem 2,  % use `mod` for negative N
	pt_powrCase(N1,D1,Z,X,R,NewZ), non_empty(NewZ),
	Ri is 1/R,
	pt_powrCase(D1,N1,X,NewZ,Ri,NewX), non_empty(NewX),
	NewY = (R,R).

powr_(_, Z,X,Y, NewZ,NewX,NewY) :-  % interval Y
	intCase(C,X),
	powr_intY_(C, Z,X,Y, NewZ,NewX,NewY).

equals_zero(0).
equals_zero(0.0).
equals_zero(-0.0).

equals_one(1).
equals_one(1.0).

% Assumption : even numerator and denominator can't occur (non-normalized rational).
pt_powrCase(N1,D1,Z,X,R,NewZ) :-  R < 0, !,  % R negative
	Rp is -R,
	universal_interval(UI),
	intCase(Cz,Z),
	odivCase(p,Cz,(1,1),Z,UI,Zi),      % Zi := UI ^ 1/Z
	pt_powrCase(N1,D1,Zi,X,Rp,NZi),
	intCase(CNzi,NZi),
	odivCase(p,CNzi,(1,1),NZi,Z,NewZ). % NewZ := Z ^ 1/NZi

pt_powrCase(1,0,(Zl,Zh),(Xl,Xh),R,(NZl,NZh)) :-  % R positive, numerator odd, denominator even
	% reflect about X axis to include positive and negative roots
	Xh >=0,   % some part of X must be positive
	Zl1 is max(0, roundtoward(Xl**R,to_negative)),  % neg Xl ==> nan
	Zh1 is roundtoward(Xh**R,to_positive),
	Zpl is max(Zl,Zl1),  Zph is min(Zh,Zh1),     % positive case
	Znl is max(Zl,-Zh1), Znh is min(Zh,-Zl1),    % negative case
	( Znl > Znh -> NZl is Zpl, NZh is Zph        % negative case is empty
	; Zpl > Zph -> NZl is Znl, NZh is Znh        % positive case is empty
	; NZl is min(Zpl,Znl), NZh is max(Zph,Znh)   % else union of positive and negative cases
	).

pt_powrCase(0,1,(Zl,Zh),(Xl,Xh),R,(NZl,NZh)) :-  % R positive, numerator even, denominator odd
	% reflect about Z axis
	( Xh < 0 -> Xl1 is -Xh, Xh1 is -Xl           % negative X, negate interval
	;(Xl > 0 -> Xl1 = Xl, Xh1 = Xh               % positive X, As is
	;           Xl1 = 0, Xh1 is max(-Xl,Xh)      % split
	)),
	% NZl can't be negative
	NZl is max(Zl, roundtoward(Xl1**R,to_negative)),  % Xl1 known to be positive
	NZh is min(Zh, roundtoward(Xh1**R,to_positive)).

pt_powrCase(1,1,(Zl,Zh),(Xl,Xh),R,(NZl,NZh)) :-  % R positive, numerator odd, denominator odd
	% continuous monotonic
	NZl is max(Zl, roundtoward(Xl**R,to_negative)),
	NZh is min(Zh, roundtoward(Xh**R,to_positive)).

% Y is an interval
powr_intY_(p, Z,X,Y, NewZ,NewX,NewY) :-              % positive X, interval Y 
	powr_prim_(Z,X,Y,NewZ), non_empty(NewZ),         % NewZ := X**Y
	universal_interval(UI),
	intCase(Cy,Y),
	odivCase(p,Cy,(1,1),Y,UI,Yi),                    % Yi := UI ^ 1/Y
	powr_prim_(X,NewZ,Yi,NewX), non_empty(NewX),     % NewX := NewZ**(1/Y)
	ln(NewZ,Ynum), intCase(Cyn,Ynum),
	ln(NewX,Yden), intCase(Cyd,Yden),
	odivCase(Cyn,Cyd,Ynum,Yden,Y,NewY).              % NewY := Y ^ log(NewZ)/log(NewX)

powr_intY_(n, Z,X,Y, NewZ,NewX,NewY) :-              % negative X, interval Y
	% In this case Y may contain an rational which is legal for negative X, e.g.,
	% to calculate an odd power or root. However it still may be able to bound Z.
	% This case flips X to positive, calculates upper bound Zh1, and then intersects
	% Z with (-Zh1,Zh1). 
	X = (Xl,Xh), X1l is -Xh, X1h is -Xl,
	powr_intY_(p, Z,(X1l,X1h),Y, (_,Z1h),(X2l,X2h),NewY),  % use code for positive case
	X3l is -X2h, X3h is -X2l, ^(X,(X3l,X3h),NewX),    % flip back for NewX
	Z1l is -Z1h, ^(Z,(Z1l,Z1h),NewZ).                 % maximal range = (-Z1h,Z1h)  

powr_intY_(s, Z,X,Y, NewZ,NewX,NewY):-                % split X, interval Y
	% union of positive and negative regions
	X = (Xl,Xh), Xfl is -Xl,  % flip negative to positive for calculation
	powr_intY_(p, Z,(0,Xfl),Y, (_,Znh),NXn,NYn),      % Znl always 0,  	
	powr_intY_(p, Z,(0,Xh), Y, (_,Zph),NXp,NYp),      % Zpl always 0
	% union and intersect with original
	NZl is -Znh, NZh is max(Znh,Zph), ^(Z,(NZl,NZh),NewZ),	
	union_(NXn,NXp,NX), ^(X,NX,NewX),
	union_(NYn,NYp,NY), ^(Y,NY,NewY).
	
powr_prim_((Zl,Zh), (Xl,Xh), (Yl,Yh), (NZl,NZh)) :-  % X assumed positive
	Zll is roundtoward(Xl**Yl,to_negative),
	Zlh is roundtoward(Xl**Yh,to_positive),
	Zhl is roundtoward(Xh**Yl,to_negative),
	Zhh is roundtoward(Xh**Yh,to_positive),
	NZl is max(Zl,min(Zll, min(Zlh, min(Zhl, Zhh)))), % intersect with min of all
	NZh is min(Zh,max(Zll, max(Zlh, max(Zhl, Zhh)))). % intersect with max of all

ln((Xl,Xh), (Zl,Zh)) :-
	Zl is roundtoward(log(Xl),to_negative),
	Zh is roundtoward(log(Xh),to_positive).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z== sin(X)

narrowing_op(sin, _, $(Z,X), $(NewZ, NewX)) :-
	sin_(X,S,Z1), ^(Z,Z1,NewZ),
	asin_(NewZ,S,X1), ^(X,X1,NewX).

sin_((X,X),S,NZ) :-  % point infinity special case
	abs(X) =:= 1.0Inf, !,
	S = (-10,10), NZ = (-1,1). 
sin_((Xl,Xh),(Sl,Sh),(NZl,NZh)) :-
	Sl is round(Xl/pi),                    % determine monotonic sector of width pi
	Sh is round(Xh/pi),                    % sector 0 is (-pi/2,pi/2)
	sinCase(Xl,Xh,Sl,Sh,NZl,NZh).

sinCase(Xl,Xh,S,S,NZl,NZh) :- !,           % same sector
	(S mod 2 =:= 0                         % monotonically increasing ?
	 -> NZl is roundtoward(sin(Xl), to_negative),
	    NZh is roundtoward(sin(Xh), to_positive)
	 ;  NZl is roundtoward(sin(Xh), to_negative),
	    NZh is roundtoward(sin(Xl), to_positive)
	).
sinCase(Xl,Xh,Sl,Sh,NZl,NZh) :- Sh-Sl =:= 1, !,  % adjacent sectors 
	(Sl mod 2 =:= 0                         % monotonically increasing ?
	 -> NZl is min(roundtoward(sin(Xl), to_negative),  % Z contains +1
	               roundtoward(sin(Xh), to_negative)),
	    NZh =  1          
	 ; 	NZl = -1,                                      % Z contains -1
	    NZh is max(roundtoward(sin(Xl), to_positive),
	               roundtoward(sin(Xh), to_positive))
	).
sinCase(_,_,_,_,-1,1).                      % span multiple sectors

asin_((Xl,Xh),(Sl,Sh),(NZl,NZh)) :-
	asinCase(Xl,Xh,Sl,Sh,NZl,NZh).

% Need to maintain adequate width applying offset, otherwise loss of precision
%	leads to unintentional rounding. This is done by fuzzing offset. 
asinCase(Xl,Xh,S,S,NZl,NZh) :- !,           % same sector
	Zl is roundtoward(asin(Xl),to_negative),
	Zh is roundtoward(asin(Xh),to_positive),
	Offs is S*pi,
	bounded_number(Offl,Offh,Offs),         % fuzz offset
	( S mod 2 =:= 0                         % monotonically increasing ?
	 -> NZl is roundtoward(Offl+Zl,to_negative),
	    NZh is roundtoward(Offh+Zh,to_positive)
	 ;  NZl is roundtoward(Offl-Zh,to_negative),
	    NZh is roundtoward(Offh-Zl,to_positive)
	).
asinCase(Xl,Xh,Sl,Sh,NZl,NZh) :- Sh-Sl =:= 1, !,  % adjacent sector
	Offl is nexttoward(Sl*pi,-inf), Offh is nexttoward(Sh*pi,inf),  % fuzz offset
	( Sl mod 2 =:= 0                        % monotonically increasing ?
	 -> Z is roundtoward(asin(Xl),to_negative),
	    NZl is roundtoward(Offl+Z,to_negative),
	    NZh is roundtoward(Offh-Z,to_positive)
	 ;  Z is roundtoward(asin(Xh),to_negative),
	    NZl is roundtoward(Offl-Z,to_negative),
	    NZh is roundtoward(Offh+Z,to_positive)
	).
asinCase(_,_,_,_,-1.0Inf,1.0Inf).           % span multiple sectors

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z== cos(X)

narrowing_op(cos, _, $(Z,X), $(NewZ, NewX)) :-
	cos_(X,S,Z1), ^(Z,Z1,NewZ),
	acos_(NewZ,S,X1), ^(X,X1,NewX).

cos_((X,X),S,NZ) :-  % point infinity special case
	abs(X) =:= 1.0Inf, !,
	S = (-10,10), NZ = (-1,1). 
cos_((Xl,Xh),(Sl,Sh),(NZl,NZh)) :-
	Sl is floor(Xl/pi),
	Sh is floor(Xh/pi),  % sector 0 is (0,pi)
	cosCase(Xl,Xh,Sl,Sh,NZl,NZh).

cosCase(Xl,Xh,S,S,NZl,NZh) :- !,            % same sector
	(S mod 2 =:= 1                          % monotonically increasing ?
	 -> NZl is roundtoward(cos(Xl), to_negative),
	    NZh is roundtoward(cos(Xh), to_positive)
	 ;  NZl is roundtoward(cos(Xh), to_negative),
	    NZh is roundtoward(cos(Xl), to_positive)
	).
cosCase(Xl,Xh,Sl,Sh,NZl,NZh) :- Sh-Sl =:= 1, !,  % adjacent sector
	(Sl mod 2 =:= 1                         % monotonically increasing ?
	 -> NZl is min(roundtoward(cos(Xl), to_negative),  % Z contains +1
	               roundtoward(cos(Xh), to_negative)),
	    NZh =  1          
	 ; 	NZl = -1,                                      % Z contains -1
	    NZh is max(roundtoward(cos(Xl), to_positive),
	               roundtoward(cos(Xh), to_positive))
	).
cosCase(_,_,_,_,-1,1).                      % span multiple sectors

acos_((Xl,Xh),(Sl,Sh),(NZl,NZh)) :-
	acosCase(Xl,Xh,Sl,Sh,NZl,NZh).

% Need to maintain adequate width applying offset, otherwise loss of precision
%	leads to unintentional rounding. This is done by fuzzing offset. 
acosCase(Xl,Xh,S,S,NZl,NZh) :- !,           % same sector
	Zl is roundtoward(acos(Xh),to_negative),
	Zh is roundtoward(acos(Xl),to_positive),
	( S mod 2 =:= 1                         % monotonically increasing ?
	 -> Offs is (S+1)*pi,
	 	bounded_number(Offl,Offh,Offs),     % fuzz offset
	    NZl is roundtoward(Offl-Zh,to_negative),
        NZh is roundtoward(Offh-Zl,to_positive)               
	 ;  Offs is S*pi,
	 	bounded_number(Offl,Offh,Offs),     % fuzz offset
	    NZl is roundtoward(Offl+Zl,to_negative),
	    NZh is roundtoward(Offh+Zh,to_positive)
  	).
acosCase(Xl,Xh,Sl,Sh,NZl,NZh) :- Sh-Sl =:= 1, !,  % adjacent sector
	( Sl mod 2 =:= 1                        % monotonically increasing ?
	 -> Z is roundtoward(acos(Xl),to_positive),  % acos is monotone decreasing
	    Offl is nexttoward((Sl+1)*pi,-inf), NZl is roundtoward(Offl-Z,to_negative),
	    Offh is nexttoward(Sh*pi,inf) , NZh is roundtoward(Offh+Z,to_positive)
	 ;  Z is roundtoward(acos(Xh),to_positive),  % acos is monotone decreasing
	    Offl is nexttoward(Sl*pi,-inf) , NZl is roundtoward(Offl+Z,to_negative),
	    Offh is nexttoward((Sh+1)*pi,inf), NZh is roundtoward(Offh-Z,to_positive)	
  	).
acosCase(_,_,_,_,-1.0Inf,1.0Inf).           % span multiple sectors

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z== tan(X)

narrowing_op(tan, _, $(Z,X), $(NewZ, NewX)) :-
	X = (Xl,Xh),
	Sl is round(Xl/pi),  % sector 0 is (-pi/2,pi/2)
	Sh is round(Xh/pi),
	tanCase(Z,X,Sl,Sh,NewZ,NewX).
	
% Need to maintain adequate width applying offset, otherwise loss of precision
%	leads to unintentional rounding. This is done by fuzzing offset. 
tanCase(Z,(X,X),_,_,Z,(X,X)) :-    % point infinity special case
	abs(X) =:= 1.0Inf, !.
tanCase((Zl,Zh),(Xl,Xh),S,S,(NZl,NZh),(NXl,NXh)) :-  !,   % same sector
	Z1l is roundtoward(tan(Xl),to_negative),
	Z1h is roundtoward(tan(Xh),to_positive),
	( Z1l =< Z1h
	 -> ^((Zl,Zh),(Z1l,Z1h),(NZl,NZh)),                   % good range
	 	Offs is S*pi,
	 	bounded_number(Offl,Offh,Offs),                   % fuzz offset
	    X1l is Offl+roundtoward(atan(NZl),to_negative),
	    X1h is Offh+roundtoward(atan(NZh),to_positive),
	    ^((Xl,Xh),(X1l,X1h),(NXl,NXh))
	 ;  % same sector range check failed, assume rounding crossed singularity
	 	once(Z1l =< Zh ; Z1h >= Zl),                      % disjoint ranges must intersect Z
	    NZl = Zl, NZh = Zh, NXl = Xl, NXh = Xh            % nothing changes
	).
tanCase(Z,(Xl,Xh),Sl,Sh,(NZl,NZh),(NXl,NXh)) :-  Sh-Sl =:= 1, !, % spans one singularity
	Sg is pi*(Sl+1r2),               % closest to singularity
	bounded_number(XSl,XSh,Sg),      % use bounded number to straddle
	(tanCase(Z,(Xl,XSl),Sl,Sl,(NZ1l,NZ1h),(NXl,NX1h))
	 -> (tanCase(Z,(XSh,Xh),Sh,Sh,(NZ2l,NZ2h),(_,NXh))
	     -> NZl = -1.0Inf, NZh = 1.0Inf                   % both sectors, includes singularity
	     ;  NXh = NX1h, NZl = NZ1l, NZh = NZ1h            % only lo sector
	    )
	 ;  tanCase(Z,(XSh,Xh),Sh,Sh,(NZl,NZh),(NXl,NXh))     % only hi sector
	).
tanCase(Z,X,Sl,Sh,Z,X).                                   % spans multiple singularities

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z== ~X boolean negation (Z and X boolean)

narrowing_op(not, P, $(Z,X), $(NewZ, NewX)) :-
	notB_(X,Z,Z1,P), ^(Z,Z1,NewZ),
	notB_(NewZ,X,X1,P), ^(X,X1,NewX).

notB_((0,0), _, (1,1), p) :- !.
notB_((1,1), _, (0,0), p) :- !.
notB_(    _, Z,     Z, _).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z==X and Y  boolean 'and'

narrowing_op(and, P, $(Z,X,Y), $(NewZ, NewX, NewY)) :-
	andB_rel_(Z,X,Y, NewZ, NewX, NewY, P).

andB_rel_(Z,(1,1),(1,1), NewZ,(1,1),(1,1), p) :- !, ^(Z,(1,1),NewZ).  % all cases persistent (points) except last
andB_rel_(Z,(0,0),Y,     NewZ,(0,0),Y, p)     :- !, ^(Z,(0,0),NewZ), ^(Y,(0,1),NewY).
andB_rel_(Z,X,(0,0),     NewZ,X,(0,0), p)     :- !, ^(Z,(0,0),NewZ), ^(X,(0,1),NewX).
andB_rel_((1,1),X,Y,     (1,1),NewX,NewY, p)  :- !, ^(X,(1,1),NewX), ^(Y,(1,1),NewY).
andB_rel_((0,0),X,(1,1), (0,0),NewX,(1,1), p) :- !, ^(X,(0,0),NewX).
andB_rel_((0,0),(1,1),Y, (0,0),(1,1),NewY, p) :- !, ^(Y,(0,0),NewY).
andB_rel_(Z,X,Y,         NewZ,NewX,NewY, P)   :- ^(Z,(0,1),NewZ), ^(X,(0,1),NewX), ^(Y,(0,1),NewY).  % still indeterminate

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z==X and Y  boolean 'nand'

narrowing_op(nand, P, $(Z,X,Y), $(NewZ, NewX, NewY)) :-
	nandB_rel_(Z,X,Y, NewZ, NewX, NewY, P).

nandB_rel_(Z,(1,1),(1,1), NewZ,(1,1),(1,1), p) :- !, ^(Z,(0,0),NewZ).  % all cases persistent except last
nandB_rel_(Z,(0,0),Y,     NewZ,(0,0),Y, p)     :- !, ^(Z,(1,1),NewZ), ^(Y,(0,1),NewY).
nandB_rel_(Z,X,(0,0),     NewZ,X,(0,0), p)     :- !, ^(Z,(1,1),NewZ), ^(X,(0,1),NewX).
nandB_rel_((0,0),X,Y,     (0,0),NewX,NewY, p)  :- !, ^(X,(1,1),NewX), ^(Y,(1,1),NewY).
nandB_rel_((1,1),X,(1,1), (1,1),NewX,(1,1), p) :- !, ^(X,(0,0),NewX).
nandB_rel_((1,1),(1,1),Y, (1,1),(1,1),NewY, p) :- !, ^(Y,(0,0),NewY).
nandB_rel_(Z,X,Y,         NewZ,NewX,NewY, P)   :- ^(Z,(0,1),NewZ), ^(X,(0,1),NewX), ^(Y,(0,1),NewY).  % still indeterminate

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z==X or Y  boolean 'or'

narrowing_op(or, P, $(Z,X,Y), $(NewZ, NewX, NewY)) :-
	orB_rel_(Z,X,Y, NewZ, NewX, NewY, P).

orB_rel_(Z,(0,0),(0,0), NewZ,(0,0),(0,0), p) :- !, ^(Z,(0,0),NewZ).  % all cases persistent (points) except last
orB_rel_(Z,(1,1),Y,     NewZ,(1,1),Y, p)     :- !, ^(Z,(1,1),NewZ), ^(Y,(0,1),NewY).
orB_rel_(Z,X,(1,1),     NewZ,X,(1,1), p)     :- !, ^(Z,(1,1),NewZ), ^(X,(0,1),NewX).
orB_rel_((0,0),X,Y,     (0,0),NewX,NewY, p)  :- !, ^(X,(0,0),NewX), ^(Y,(0,0),NewY).
orB_rel_((1,1),X,(0,0), (1,1),NewX,(0,0), p) :- !, ^(X,(1,1),NewX).
orB_rel_((1,1),(0,0),Y, (1,1),(0,0),NewY, p) :- !, ^(Y,(1,1),NewY).
orB_rel_(Z,X,Y,         NewZ,NewX,NewY, P)   :- ^(Z,(0,1),NewZ), ^(X,(0,1),NewX), ^(Y,(0,1),NewY).  % still indeterminate

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z==X nor Y  boolean 'nor'

narrowing_op(nor, P, $(Z,X,Y), $(NewZ, NewX, NewY)) :-
	norB_rel_(Z,X,Y, NewZ, NewX, NewY, P).

norB_rel_(Z,(0,0),(0,0), NewZ,(0,0),(0,0), p) :- !, ^(Z,(1,1),NewZ).  % all cases persistent (points) except last
norB_rel_(Z,(1,1),Y,     NewZ,(1,1),Y, p)     :- !, ^(Z,(0,0),NewZ), ^(Y,(0,1),NewY).
norB_rel_(Z,X,(1,1),     NewZ,X,(1,1), p)     :- !, ^(Z,(0,0),NewZ), ^(X,(0,1),NewX).
norB_rel_((1,1),X,Y,     (1,1),NewX,NewY, p)  :- !, ^(X,(0,0),NewX), ^(Y,(0,0),NewY).
norB_rel_((0,0),X,(0,0), (0,0),NewX,(0,0), p) :- !, ^(X,(1,1),NewX).
norB_rel_((0,0),(0,0),Y, (0,0),(0,0),NewY, p) :- !, ^(Y,(1,1),NewY).
norB_rel_(Z,X,Y,         NewZ,NewX,NewY, P)   :- ^(Z,(0,1),NewZ), ^(X,(0,1),NewX), ^(Y,(0,1),NewY).  % still indeterminate

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z==X xor Y  boolean 'xor'

narrowing_op(xor, P, $(Z,X,Y), $(NewZ, NewX, NewY)) :-
	xorB_rel_(Z,X,Y, NewZ, NewX, NewY, P).

xorB_rel_(Z,(B,B),(B,B), NewZ,(B,B),(B,B), p) :- !, ^(Z,(0,0),NewZ).  % all cases persistent (points) except last
xorB_rel_(Z,(X,X),(Y,Y), NewZ,(X,X),(Y,Y), p) :- !, ^(Z,(1,1),NewZ).
xorB_rel_((B,B),X,(B,B), (B,B),NewX,(B,B), p) :- !, ^(X,(0,0),NewX).
xorB_rel_((Z,Z),X,(Y,Y), (Z,Z),NewX,(Y,Y), p) :- !, ^(X,(1,1),NewX).
xorB_rel_((B,B),(B,B),Y, (B,B),(B,B),NewY, p) :- !, ^(Y,(0,0),NewY).
xorB_rel_((Z,Z),(X,X),Y, (Z,Z),(X,X),NewY, p) :- !, ^(Y,(1,1),NewY).
xorB_rel_(Z,X,Y,         NewZ,NewX,NewY, P)   :- ^(Z,(0,1),NewZ), ^(X,(0,1),NewX), ^(Y,(0,1),NewY).  % still indeterminate

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z==X -> Y  boolean 'implies'

narrowing_op(imB, P, $(Z,X,Y), $(NewZ, NewX, NewY)) :-
	imB_rel_(Z,X,Y, NewZ, NewX, NewY, P).

imB_rel_(Z,(1,1),Y, New,(1,1),New,   P) :- !, ^(Z,Y,New), (New=(B,B) -> P=p ; true).   % X=1, Z=Y, persistant if point
imB_rel_(Z,(0,0),Y, NewZ,(0,0),Y,    p) :- !, ^(Z,(1,1),NewZ), ^(Y,(0,1),NewY).        % X=0, Z=1, persistant
imB_rel_(Z,X,(0,0), NewZ,NewX,(0,0), P) :- !, notB_(X,Z,NewZ,P), notB_(NewZ,X,NewX,P). % Y=0, Z=~X, persistant if point
imB_rel_(Z,X,(1,1), NewZ,X,(1,1),    P) :- !, ^(Z,(1,1),NewZ).                      % Y=1, Z=1, persistant
imB_rel_((0,0),X,Y, (0,0),NewX,NewY, p) :- !, ^(X,(1,1),NewX), ^(Y,(0,0),NewY).     % Z=0,X=1,Y=0, persistant
imB_rel_(Z,X,Y,     NewZ,NewX,NewY,  P) :- ^(Z,(0,1),NewZ), ^(X,(0,1),NewX), ^(Y,(0,1),NewY).  % still indeterminate
