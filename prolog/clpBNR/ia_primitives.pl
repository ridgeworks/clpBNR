/*	The MIT License (MIT)
 *
 *	Copyright (c) 2019,2020,2021 Rick Workman
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
intCase(p, (L,H)) :- L>=0, !.            % non-negative
intCase(n, (L,H)) :- H=<0, !.            % non-positive
intCase(s, (L,H)).                       % split

%
% interval primitive functions
% X, Y and Z are intervals
%

%
% Z := X ^ Y  (intersection)
%

^((Xl,Xh), (Yl,Yh), (Zl,Zh)) :-
	Zl is max(Xl, Yl), Zh is min(Xh, Yh),
	non_empty(Zl,Zh).

%
% Z := X \/ Y (union)
%
union_((Xl,Xh),(Yl,Yh),(Zl,Zh)) :-
	Zl is min(Xl,Yl), Zh is max(Xh,Yh).

%
% wrap repeating interval onto a prime cylinder of width W and
% return projected interval and "mulipliers" to re-project
% Note: fails if interval wider than W so beware of outward rounding on ranges, e.g., 
%	range of [-pi/2,pi/2] on tan argument actually spans 3 cylinders (-1 to 1).
%
wrap_((Xl,Xh), W, (MXl,MXh), (Xpl,Xph)) :-  % project onto cylinder from -W/2 to W/2
	MXl is round(Xl/W),
	MXh is round(Xh/W),
	MXh-MXl =< 1, Xh-Xl =< W,  % MX check first to avoid overflow
	Xpl is Xl - (MXl*W), Xph is Xh-(MXh*W).

%
% unwrap projected interval back to original range
%
unwrap_((Xpl,Xph), W, (MXl,MXh), (Xl,Xh)) :-
	Xl is Xpl+W*MXl, Xh is Xph+W*MXh.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Relational Operations (narrowing operations)
%
:- discontiguous clpBNR:narrowing_op/4.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% integral (contract to integer bounds)

narrowing_op(integral, P, $((L,H)), $((NL,NH))) :-
	NL is ceiling(L), NH is floor(H),
	NL=<NH.
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z==(X==Y)  % (Z boolean)

narrowing_op(eq, P, $((1,1), X, Y), $((1,1), New, New)) :- !,      % Z is true, X and Y must intersect
	^(X,Y,New),
	(X=(Pt,Pt) -> P=p ; true).  % if a point, mark as persistent (makes a huge difference on some problems)

narrowing_op(eq, p, $(Z, X, Y), $(NewZ, X, Y)) :-                  % persistent, X and Y don't intersect, Z is false
	\+(^(X,Y,_)), !,
	^(Z, (0,0), NewZ).
	
narrowing_op(eq, p, $(Z, (X,X), (Y,Y)), $(NewZ, (X,X), (Y,Y))) :-  % if X and Y are necessarily equal, Z is true
	X =:= Y, !,
	^(Z, (1,1), NewZ).

narrowing_op(eq, _, $(Z,X,Y), $(NewZ,X,Y)) :- ^(Z,(0,1),NewZ).     % else no change, but narrow Z to boolean

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z==(X<>Y)  % (Z boolean, X,Y integer)

narrowing_op(ne, p, $(Z, X, Y), $(NewZ, X, Y)) :-                  % persistent: disjoint or necessarily equal
	not_equal_(X,Y,BZ), !,
	^(Z, (BZ,BZ), NewZ).

narrowing_op(ne, _, $((1,1), X, Y), $((1,1), NewX, NewY)) :-       % Z true, X/Y a point = bound of Y/X
	ne_int_(X,Y,NewX),        % narrow X if Y is a point and a bound of X (always succeeds but may not narrow)
	ne_int_(Y,NewX,NewY), !.  % narrow Y if NewX is a point and a bound of Y (always succeeds but may not narrow)

narrowing_op(ne, _, $(Z,X,Y), $(NewZ,X,Y)) :- ^(Z,(0,1),NewZ).     % none of the above, narrow Z to boolean

not_equal_((Xl,Xh), (Yl,Yh), 1) :-  (Xh < Yl ; Yh < Xl).     % X and Y disjoint,           Z true
not_equal_((X,X),   (Y,Y),   0) :-  X =:= Y.                 % otherwise if pt(X)=:=pt(Y), Z false

% Y <> X, where where Y and X are integer intervals (enforced elsewhere)
ne_int_((X,H), (X,X), (NewL,H)) :- !,  % X is a point,  and low bound of Y
	NewL is X+1, NewL=<H.
ne_int_((L,X), (X,X), (L,NewH)) :- !,  % X is a point,  and high bound of Y
	NewH is X-1, L=<NewH.
ne_int_(Y, X, Y).                      % no narrowing

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z==(X=<Y)  % (Z boolean)

narrowing_op(le, P, $(Z, X, Y), New) :-
	(Z=(1,1)
	 -> le_true(X,Y,New,P)             % Z true
	  ; (Z=(0,0)
	  	 -> le_false(X,Y,New,P)        % Z false
	  	  ; le_bool(X,Y,New,P)         % Z unknown
	  	)
	).
le_true(X, (Yl,Yh), $((1,1), (NXl,NXh), (NYl,NYh)), P) :-
	^(X, (-1.0Inf,Yh), (NXl,NXh)),           % NewX := (Xl,Xh) ^(NI,Yh)
	^((Yl,Yh), (NXl,1.0Inf), (NYl,NYh)),     % NewY := (Yl,Yh) ^(Xl,PI)
	(NXh =< NYl -> P=p ; true).              % will always be true?

le_false(X, Y, $((0,0), NewX, NewY), P) :-
	lt_true(Y,X,$(_,NewY,NewX),P).  % unsound but best alternative
	
le_bool((Xl,Xh), (Yl,Yh), $(NewZ, (Xl,Xh), (Yl,Yh)), P) :-
	(Yh  < Xl
	 -> (NewZ=(0,0), P=p)           % false persistant 
	  ; (Xh =< Yl
	  	 -> (NewZ=(1,1), P=p)       % true persistant
		  ; NewZ=(0,1)              % indefinite boolean
		)
	).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z==(X<Y)  % (Z boolean) generally unsound on reals but possibly useful for minima/maxima

narrowing_op(lt, P, $(Z, X, Y), New) :-
	(Z=(1,1)
	 -> lt_true(X,Y,New,P)                   % Z true
	  ; (Z=(0,0)
	  	 -> lt_false(X,Y,New,P)              % Z false
	  	  ; lt_bool(X,Y,New,P)               % Z unknown
	  	)
	).

lt_true( X, (Yl,Yh), $((1,1), (NXl,NXh), (NYl,NYh)), P) :-
	next_lt_(Yh,-1,YhD),                      % YhD is next downward value from Yh
	^(X, (-1.0Inf,YhD), (NXl,NXh)),           % NewX := (Xl,Xh) ^(NInf,YhD)
	next_lt_(NXl,1,NXlU),                     % NXlU is next upward value from NXl
	^((Yl,Yh), (NXlU,1.0Inf), (NYl,NYh)),     % NewY := (Yl,Yh) ^(NXlU,PInf)
	(NXh < NYl -> P=p ; true).                % will always be true?
	
lt_false(X, Y, $((0,0), NewX, NewY), P) :-
	le_true(Y,X,$(_,NewY,NewX),P).
		
lt_bool((Xl,Xh), (Yl,Yh), $(NewZ, (Xl,Xh), (Yl,Yh)), P) :-
	(Yh  =< Xl
	 -> (NewZ=(0,0), P=p)           % false persistant 
	  ; (Xh < Yl
	  	 -> (NewZ=(1,1), P=p)       % true persistant
		  ; NewZ=(0,1)              % indefinite boolean
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
	mul_(X,Y,Z,NewZ),          % NewZ := Z ^ (X*Y)
	odiv_(NewZ,X,Y,Yp),         % Yp := Y ^ (Z/X),
	odiv_(NewZ,Yp,X,NewX),      % NewX := X ^ (Z/Yp),
	% if X narrowed it may be necessary to recalculate Y due to non-optimal ordering.
	mul_redoY(Y,Yp,X,NewX,NewY,NewZ).

mul_redoY(Y,Y,X,NewX,NewY,NewZ) :-     % if initial Y narrowing didn't change (contain 0?)
	X \= NewX, !,                      % and X did narrow 
	%/(NewZ,NewX,Y1), ^(Y,Y1,NewY).     % recalculate Y with NewX
	odiv_(NewZ,NewX,Y,NewY).     % recalculate Y with NewX
mul_redoY(_,NewY,_,_,NewY,_).          % else keep Y as NewY

% NZ := Z ^ (X * Y)  (multiply)
mul_(X, Y, Z, NZ) :-
	intCase(Cx,X),
	intCase(Cy,Y),
	multCase(Cx,Cy,X,Y,Z,NZ), !.

% NZ := Z ^ (X / Y)  (odiv)
odiv_(X, Y, Z, NZ) :-
	intCase(Cx,X),
	intCase(Cy,Y),
	odivCase(Cx,Cy,X,Y,Z,NZ).  % !'s in odiv'

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

narrowing_op(pow, _, $(Z,X,(R,R)), $(NewZ, NewX, (R,R))) :- rational(R,N,D), !,   % R = rational point exponent
	(R = 0
	 -> ^(Z,(1,1),NewZ),
		NewX = X
	 ; 	N1 is N mod 2, D1 is D rem 2,  % use `mod` for negative N
	 	pt_powrCase(N1,D1,Z,X,R,NewZ), non_empty(NewZ),
		Ri is 1/R,
		pt_powrCase(D1,N1,X,NewZ,Ri,NewX), non_empty(NewX)
	).

narrowing_op(pow, _, $(Z,(Xl,Xh),Y), $(NewZ, NewX, NewY)) :-   % interval Y, X must be positive
	XZl is max(0,Xl), Xp = (XZl,Xh),  Xh >= 0,  % X must be positive (>=0)
	powr_(Z,Xp,Y,NewZ), non_empty(NewZ),
	universal_interval(UI), odiv_((1,1),Y,UI,Yi),
	powr_(Xp,NewZ,Yi,NewX), non_empty(NewX),
	ln(NewZ,Ynum), ln(NewX,Yden),
	odiv_(Ynum,Yden,Y,NewY).       % NY := Y ^ log(NZ)/log(NX)*/
	
% requires conservative rounding using nexttoward
% Assumption : even numerator and denominator can't occur (non-normalized rational).
pt_powrCase(N1,D1,Z,X,R,NewZ) :-  R < 0, !,  % R negative
	Rp is -R,
	universal_interval(UI),
	odiv_((1,1),Z,UI,Zi),
	pt_powrCase(N1,D1,Zi,X,Rp,NZi),
	odiv_((1,1),NZi,Z,NewZ).

pt_powrCase(1,0,(Zl,Zh),(Xl,Xh),R,NewZ) :-  % R positive, numerator odd, denominator even
	% reflect about X axis to inclide positive and negative roots
	Xh >=0,   % some part of X must be positive
	(float(Xl)
	 -> Zl1 is max(0, roundtoward(nexttoward(nexttoward(Xl,-1.0Inf),-1.0Inf)**R, to_negative))
	  ; Zl1 is max(0, roundtoward(Xl**R,to_negative))
	),
	(float(Xh)
	 -> Zh1 is roundtoward(nexttoward(nexttoward(Xh,1.0Inf),1.0Inf)**R, to_positive)
	  ; Zh1 is roundtoward(Xh**R,to_positive)
	),
	Zpl is max(Zl,Zl1),  Zph is min(Zh,Zh1),    % positive case
	(Zpl =< Zph -> Zps = (Zpl,Zph) ; empty_interval(Zps)),
	Znl is max(Zl,-Zh1), Znh is min(Zh,-Zl1),   % negative case
	(Znl =< Znh -> Zns = (Znl,Znh) ; empty_interval(Zns)),
	union_(Zps,Zns,NewZ).                       % union of positive and negative cases

pt_powrCase(0,1,(Zl,Zh),(Xl,Xh),R,(NZl,NZh)) :-  % R positive, numerator even, denominator odd
	% reflect about Z axis
	( Xh < 0 -> Xl1 is -Xh, Xh1 is -Xl           % negative X, negate interval
	;(Xl > 0 -> Xl1 = Xl, Xh1 = Xh               % positive X, As is
	;           Xl1 = 0, Xh1 is max(-Xl,Xh)      % split
	)),
	% NZl can't be negative
	(float(Xl1)
	 -> NZl is max(Zl,max(0, roundtoward(nexttoward(nexttoward(Xl1,-1.0Inf),-1.0Inf)**R, to_negative)))
	  ; NZl is max(Zl,max(0, roundtoward(Xl1**R,to_negative)))
	),
	(float(Xh1)
	 -> NZh is min(Zh, roundtoward(nexttoward(nexttoward(Xh1,1.0Inf),1.0Inf)**R, to_positive))
	  ; NZh is min(Zh, roundtoward(Xh1**R,to_positive))
	).

pt_powrCase(1,1,(Zl,Zh),(Xl,Xh),R,(NZl,NZh)) :-  % R positive, numerator odd, denominator odd
	% continuous monotonic
	(float(Xl)
	 -> NZl is max(Zl, roundtoward(nexttoward(nexttoward(Xl,-1.0Inf),-1.0Inf)**R,to_negative))
	  ; NZl is max(Zl, roundtoward(Xl**R,to_negative))
	),
	(float(Xh)
	 -> NZh is min(Zh, roundtoward(nexttoward(nexttoward(Xh,1.0Inf),1.0Inf)**R,to_positive))
	  ; NZh is min(Zh, roundtoward(Xh**R,to_positive))
	).

ln((Xl,Xh), (Zl,Zh)) :-
	Zl is roundtoward(log(Xl),to_negative), % rounding dependable?
	Zh is roundtoward(log(Xh),to_positive).

powr_((Zl,Zh), (Xl,Xh), (Yl,Yh), (NZl,NZh)) :-  % X assumed positive
	Zll is max(0,nexttoward(roundtoward(Xl**Yl,to_negative),-1.0Inf)), 
	Zlh is nexttoward(roundtoward(Xl**Yh,to_positive), 1.0Inf),
	Zhl is max(0,nexttoward(roundtoward(Xh**Yl,to_negative),-1.0Inf)),
	Zhh is nexttoward(roundtoward(Xh**Yh,to_positive), 1.0Inf),
	NZlmin is min(Zll, min(Zlh, min(Zhl, Zhh))),  % min of all
	NZl is max(Zl,NZlmin),
	NZhmax is max(Zll, max(Zlh, max(Zhl, Zhh))),  % max of all
	NZh is min(Zh,NZhmax).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z== sin(X)

narrowing_op(sin, _, $(Z,X), $(NewZ, NewX)) :-
	(wrap_(X,2*pi,MX,Xp)            % fails if X too wide
	 -> sin_(MX,Xp,Z,NMX,X1,NewZ),
	    unwrap_(X1,2*pi,NMX,X2),    % project back to original cylinder
	    non_empty(NewZ),
	    ^(X,X2,NewX)
	 ;  ^(Z,(-1,1),NewZ),           % no narrowing possible, just constrain Z
	    NewX = X
	).

sin_((MX,MX), X, Z, (MX,MX), NewX, NewZ) :- !,  % same cylinder, split into 3 interval convex sectors
	Pi_2 is pi/2,
	sin_sector_(lo, Pi_2, X, Z, NXlo,  NZlo),
	sin_sector_(mid,Pi_2, X, Z, NXmid, NZmid),
	sin_sector_(hi, Pi_2, X, Z, NXhi,  NZhi),
	union_(NXlo,NXmid,NX1), union_(NX1,NXhi,NewX), 
	union_(NZlo,NZmid,NZ1), union_(NZ1,NZhi,NewZ).

sin_((MXl,MXh), (Xl,Xh), Z, (NMXl,NMXh), NewX, NewZ) :-  % adjacent cylinders,
	Pi is pi, MPi is -pi,
	try_sin_((Xl,Pi), Z, NX1, NZ1,MXl,MXh,NMXl),
	try_sin_((MPi,Xh),Z, NX2, NZ2,MXh,MXl,NMXh),
	union_(NZ1,NZ2,NewZ),
	union_(NX1,NX2,NewX).

try_sin_(X,Z,NewX,NewZ,MXS,MXF,MX) :- 
	sin_((MXS,MXS), X, Z, _, NewX, NewZ) 
	 -> MX = MXS
	 ;  (empty_interval(NewX), NewZ = NewX, MX = MXF).

sin_sector_(lo,Pi_2,(Xl,Xh),Z,(NXl,NXh),NewZ) :-
	Xl =< -Pi_2,                 % X intersects lo sector, flip to mid
	X1l is max(-pi-Xh,-Pi_2), X1h is -pi-Xl,
	sin_prim_((X1l,X1h),Z,(NX1l,NX1h),NewZ),
	!,
	NXl is -pi-NX1h, NXh is -pi-NX1l.

sin_sector_(hi,Pi_2,(Xl,Xh),Z,(NXl,NXh),NewZ) :-
	Xh >= Pi_2,                    % X intersects hi sector, flip to mid
	X1l is pi-Xh, X1h is min(pi-Xl,Pi_2),
	sin_prim_((X1l,X1h),Z,(NX1l,NX1h),NewZ),
	!,
	NXl is pi-NX1h, NXh is pi-NX1l.

sin_sector_(mid,Pi_2,(Xl,Xh),Z,NewX,NewZ) :-
	Xl =< Pi_2, Xh >= -Pi_2,       % mid sector, valid asin function range
	X1l is max(Xl,-Pi_2), X1h is min(Xh, Pi_2),
	sin_prim_((X1l,X1h),Z,NewX,NewZ),
	!.

sin_sector_(_Any,_,_X,_Z,MT,MT) :- empty_interval(MT).

% both sin and asin monotonic, increasing in range -pi/2 to pi/2
sin_prim_((Xl,Xh),(Zl,Zh),(NXl,NXh),(NZl,NZh)) :-
	% Note 1: can't depend on transcendentals to obey rounding
	% Note 2: end result always a float interval (never precise), range limited to ± 1
	% Note 3: any precise input will be fuzzed
	% Note 4: empty ranges checked elsewhere
	(Xl = Xh -> bounded_number(X1l,X1h,Xl) ; X1l = Xl, X1h = Xh),  % See Note 3
	NZl is max(Zl,max(-1,nexttoward(sin(X1l),-1.0Inf))),           % See Note 2
	NZh is min(Zh,min( 1,nexttoward(sin(X1h), 1.0Inf))),           % See Note 2
	NZl < NZh,
	NXl is max(Xl,nexttoward(asin(NZl),-1.0Inf)),
	NXh is min(Xh,nexttoward(asin(NZh), 1.0Inf)),
	NXl < NXh.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z== cos(X)

narrowing_op(cos, _, $(Z,X), $(NewZ, NewX)) :-
	(wrap_(X,2*pi,MX,Xp)          % fails if X too wide
	 -> cos_(MX,Xp,Z,NMX,X1,NewZ),
	    unwrap_(X1,2*pi,NMX,X2),  % project back to original cylinder
	    non_empty(NewZ),
	    ^(X,X2,NewX)
	 ;  ^(Z,(-1,1),NewZ),         % no narrowing possible, just constrain Z
	    NewX = X
	).

cos_((MX,MX), X, Z, (MX,MX), NewX, NewZ) :- !,  % same cylinder, split into 2 interval convex sectors
	cos_sector_(neg, X, Z, NXneg, NZneg),
	cos_sector_(pos, X, Z, NXpos, NZpos),
	union_(NZneg,NZpos,NewZ),
	union_(NXneg,NXpos,NewX).

cos_((MXl,MXh), (Xl,Xh), Z, (NMXl,NMXh), NewX, NewZ) :-  % adjacent cylinders,
	Pi is pi, MPi is -pi,
	try_cos_((Xl,Pi), Z, NX1, NZ1,MXl,MXh,NMXl),
	try_cos_((MPi,Xh),Z, NX2, NZ2,MXh,MXl,NMXh),
	union_(NZ1,NZ2,NewZ),
	union_(NX1,NX2,NewX).

try_cos_(X,Z,NewX,NewZ,MXS,MXF,MXS) :-
	cos_((MXS,MXS), X, Z, _, NewX, NewZ) 
	 -> MX = MXS
	 ;  (empty_interval(NewX), NewZ = NewX, MX = MXF).

cos_sector_(neg,(Xl,Xh),Z,(NXl,NXh),NewZ) :-     % Lo is -pi, Hi is 0
	Xl =< 0,
	X1l is max(0,-Xh), X1h is -Xl,
	cos_prim_((X1l,X1h),Z,(NX1l,NX1h),NewZ),
	!,
	NXl is -NX1h, NXh is -NX1l.

cos_sector_(pos,(Xl,Xh),Z,NewX,NewZ) :-          % Lo is 0, Hi is pi
	Xh >=0,
	X1l is max(0,Xl),
	cos_prim_((X1l,Xh),Z,NewX,NewZ),
	!.

cos_sector_(_Any,_X,_Z,MT,MT) :- empty_interval(MT).

% both cos and acos monotonic decreasing in range 0 to pi
cos_prim_((Xl,Xh),(Zl,Zh),(NXl,NXh),(NZl,NZh)) :-
	% Note 1: can't depend on transcendentals to obey rounding
	% Note 2: end result always a float interval (never precise), range limited to ± 1
	% Note 3: any precise input will be fuzzed
	% Note 4: empty ranges checked elsewhere
	(Xl = Xh -> bounded_number(X1l,X1h,Xl) ; X1l = Xl, X1h = Xh),  % See Note 3
	NZl is max(Zl,max(-1,nexttoward(cos(X1h),-1.0Inf))),           % See Note 2
	NZh is min(Zh,min( 1,nexttoward(cos(X1l), 1.0Inf))),           % See Note 2
	NZl < NZh,
	NXl is max(Xl,nexttoward(acos(NZh),-1.0Inf)),
	NXh is min(Xh,nexttoward(acos(NZl), 1.0Inf)),
	NXl < NXh.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z== tan(X)

narrowing_op(tan, _, $(Z,X), $(NewZ, NewX)) :-
	(wrap_(X,pi,MX,Xp)            % fails if X too wide
	 -> tan_(MX,Xp,Z,NMX,X1,NewZ),
	    unwrap_(X1,pi,NMX,X2),    % project back to original cylinder
	    non_empty(NewZ),
	    ^(X,X2,NewX)
	 ;  NewZ = Z, NewX = X        % no narrowing possible, e.g., not same or adjacent cylinder.
	).

% both tan and atan monotonic, increasing in range -pi/2 to pi/2
tan_((MX,MX), (Xl,Xh), (Zl,Zh), (MX,MX), (NXl,NXh), (NZl,NZh)) :- !,  % same cylinder
	% Note 1: can't depend on transcendentals to obey rounding
	% Note 2: end result always a float interval (never a precise value)
	% Note 3: for subnormal and zero floats, X==tan(X)
	% Note 4: any precise input will be fuzzed
	(Xl = Xh -> bounded_number(X1l,X1h,Xl) ; X1l = Xl, X1h = Xh),  % See Note 4
	% See Note 3
	((rational(X1l) ; float_class(X1l,normal))
	  -> NZl is max(Zl,nexttoward(tan(X1l),-1.0Inf))
	  ;  NZl is max(Zl,X1l)
	),
	((rational(X1h) ; float_class(X1h,normal))
	 -> NZh is min(Zh,nexttoward(tan(X1h), 1.0Inf))
	 ;  NZh is min(Zh,X1h)
	),
	NZl < NZh,  % See Note 2
	((rational(NZl) ; float_class(NZl,normal))
	  -> NXl is max(Xl,nexttoward(atan(NZl),-1.0Inf))
	  ;  NXl is max(Xl,NZl)
	),
	((rational(NZh) ; float_class(NZh,normal))
	  -> NXh is min(Xh,nexttoward(atan(NZh), 1.0Inf))
	  ;  NXh is min(Xh,NZh)
	),
	NXl < NXh.  % See Note 2

% not same cylinder, must span infinite discontinuity but need to assume possibility of
%  other constraints (E.g., {X>=0,Y>=0, tan(X)==Y, X**2 + Y**2 == 5 } )
tan_((MXl,MXh), (Xl,Xh), Z, (NMXl,NMXh), NewX, NewZ) :-
%	MXl is MXh-1,  % adjacent cylinders, Z spans discontinuity, so can't narrow further
	PiBy2 is pi/2, MPiBy2 is -PiBy2,
	try_tan_((Xl,PiBy2),  Z, NX1, NZ1, MXl,MXh,NMXl),  % lower cylinder: 0 to pi/2
	try_tan_((MPiBy2,Xh), Z, NX2, NZ2, MXh,MXl,NMXh),  % upper cylinder: -pi/2 to 0
	union_(NX1,NX2,NewX),
	union_(NZ1,NZ2,NewZ).

try_tan_(X,Z,NewX,NewZ,MXS,MXF,MX) :-  % depends on tan_/6 failure
	tan_((MXS,MXS), X, Z, _, NewX, NewZ)
	 -> MX = MXS
	 ;  (empty_interval(NewX), NewZ = NewX, MX = MXF).

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
