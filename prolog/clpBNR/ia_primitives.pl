/*	The MIT License (MIT)
 *
 *	Copyright (c) 2019-2025 Rick Workman
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
	g_inc('$clpBNR:evalNode'),  % count of primitive calls
	narrowing_op(Op, P, Is, R),
	!.
evalNode(_Op, _, _, _):-
	g_inc('$clpBNR:evalNodeFail'),  % count of primitive call failures
	debugging(clpBNR),              % fail immediately unless debug=true
	current_node_(C),
	debug_clpBNR_("** fail ** ~w.",C),
	fail.

sandbox:safe_global_variable('$clpBNR:evalNode').
sandbox:safe_global_variable('$clpBNR:evalNodeFail').

clpStatistics :-
	g_assign('$clpBNR:evalNode',0),
	g_assign('$clpBNR:evalNodeFail',0),
	fail.  % backtrack to reset other statistics.

clpStatistic(narrowingOps(C)) :- g_read('$clpBNR:evalNode',C).

clpStatistic(narrowingFails(C)) :- g_read('$clpBNR:evalNodeFail',C).

%
% non-empty interval test
%
goal_expansion(non_empty(L,H), 1 =\= cmpr(L,H)).  % SWIP inline optimization for non_empty/2

non_empty((L,H)) :- non_empty(L,H).
non_empty(L,H) :- 1 =\= cmpr(L,H).

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
	Zl is maxr(Xl, Yl), Zh is minr(Xh, Yh),  % eliminates NaN's, prefers rationals
	non_empty(Zl,Zh).

%
% Z := X \/ Y (interval union)
%
union_((Xl,Xh),(Yl,Yh),(Zl,Zh)) :-
	Zl is minr(Xl,Yl), Zh is maxr(Xh,Yh).  % eliminates NaN's, prefers rationals

%
% to_float/2 converts an non-float bounds to floats
%  useful when when float arguments will be produced on narrowing, e.g., elementary functions
%  avoids incorrect rounding on argument conversion (monotonic decreasing segments)
%
to_float((L,H),(FL,FH)) :-
	( float(L) -> FL = L ; FL is roundtoward(float(L), to_negative) ), 
	( float(H) -> FH = H ; FH is roundtoward(float(H), to_positive) ). 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Relational Operations (narrowing operations)
%
:- discontiguous clpBNR:narrowing_op/4.
:- style_check(-singleton).  % for narrowing_op
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% integral (contract to integer bounds) - optimized version of (int,P,$(1,X),_)

narrowing_op(integral, P, $(X), $(NewX)) :-
	integral_(X,NewX).
	
integral_((Xl,Xh),(NXl,NXh)) :-
	NXl is ceiling(Xl), NXh is floor(Xh),
	non_empty(NXl,NXh).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z == integer(X) % (Z boolean) 
%  true if X is an integral point, false if it doesn't contain an integer
%  else if true, narrows X to integer bounds

narrowing_op(int, P, $(Z,X), $(NewZ,NewX)) :-
	int_(Z,X,P,NewZ,NewX).
	
int_(Z,X,p,NewZ,X) :-                       % persistent cases
	X = (Xl,Xh),
	(0 is cmpr(Xl,Xh)                   % point value?
	 -> (0 is cmpr(Xl,integer(Xl)) -> B = 1 ; B = 0)  % yes, true if integer else false
	 ;  ceiling(Xl) > floor(Xh),        % no, and X doesn't contain an integer
	    B = 0 
	),
	!,  % succeed, persistent
	^(Z,(B,B),NewZ).
	
int_(Z,X,P,NewZ,NewX) :-                % possible narrowing case
	(Z == (1,1) 
	 -> integral_(X,NewX),              % Z true, narrow X to integers
	    (NewX = (N,N) -> P=p ; true),   % persistent if a point
	    NewZ = Z
	 ;  NewX = X,                       % Z false or indeterminate, no change to X
	    ^(Z,(0,1),NewZ)                 % Z boolean
	).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Z==sgn(X)  % (Z integer(-1,1))

narrowing_op(sgn, P, $(Z,X), $((NZl,NZh),NewX)) :-
	X = (Xl,Xh),
	SXl is cmpr(Xl,0), SXh is cmpr(Xh,0),
	^(Z,(SXl,SXh),(NZl,NZh)),
	(NZl >= 0 -> ^(X, (0,1.0Inf), X1)   ; X1=X),
	(NZh =< 0 -> ^(X1,(-1.0Inf,0),NewX) ; NewX = X1),
	(NZl == NZh -> P=p ; true).  % sgn is a point

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z==(X==Y)  % (Z boolean)

narrowing_op(eq, P, $(Z,X,Y), Out) :-
	(^(X,Y,New)                       % intersect?
	 -> (Z = (1,1)
	     -> Out = $(Z,New,New), 
	        New = (L,H),
	        (0 is cmpr(L,H) -> P = p ; true)   % persistent if a point
	     ; % intersect and Z false or indeterminate, all things possible
	        ( X = (Xl,Xh), Y = (Yl,Yh),
	         0 is cmpr(Xl,Xh) \/ cmpr(Yl,Yh) \/ cmpr(Xl,Yl)  % X and Y same point
	         -> ^(Z,(1,1),NewZ),      % Z true
	            P = p                 % persistant
	         ;  ^(Z,(0,1),NewZ)       % ensure Z boolean
	        ),
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
	     ;  (X = Y, L = H -> B = (0,0), P = p ;  B = (0,1)),
	        ^(Z,B,NewZ),
	        Out = $(NewZ,X,Y)
	     )
	 ;  % X and Y do not intersect
	    ^(Z, (1,1), NewZ),            % true and 
	    P = p,                        % persistent
	    Out = $(NewZ,X,Y)
	).

% narrow X and Y given Y <> X,  where Y and X are integer intervals (enforced elsewhere)
% integers so standard comparison works.
ne_int_((X,H), (X,X), (NewL,H)) :- !,  % X is a point,  and low bound of Y
	NewL is X+1, NewL=<H.
ne_int_((L,X), (X,X), (L,NewH)) :- !,  % X is a point,  and high bound of Y
	NewH is X-1, L=<NewH.
ne_int_(Y, _X, Y).                      % no narrowing

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z==(X=<Y)  % (Z boolean)

narrowing_op(le, P, $(Z, X, Y), Out) :-
	X = (Xl,Xh), Y = (Yl,Yh),
	(non_empty(Xh,Yl)                                  % Xh =< Yl
	 -> ^(Z,(1,1),NewZ), P = p, Out = $(NewZ,X,Y)      % persistent X =< Y
	 ;  (-1 is cmpr(Yh,Xl)                             % Yh < Xl
	     -> ^(Z,(0,0),NewZ), P = p, Out = $(NewZ,X,Y)  % persistent Y < X
	     ;  le_int_(Z,Xl,Xh,Yl,Yh,P,Out)               % possibly non-persistent narrowing cases
	    )
	).
	
le_int_((1,1),Xl,Xh,Yl,Yh,P,$((1,1),(Xl,NXh),(NYl,Yh))) :- !,  % common case, narrow X and Y
	NXh is minr(Xh,Yh),                               % NewX := (Xl,NXh) 
	NYl is maxr(Xl,Yl),                               % NewY := (NYl,Yh)
	(non_empty(NXh,NYl) -> P=p ; true).               % now persistant?
le_int_(Z,Xl,Xh,Yl,Yh,P,$(NewZ,NewX,NewY)) :- !,
	(Z == (0,0)
	 -> le_int_((1,1),Yl,Yh,Xl,Xh,P,$(_,NewY,NewX)),  % false so Y =< X (Y < X is unsafe)
	 	NewZ = Z
	 ;  NewX = (Xl,Xh), NewY = (Yl,Yh),               % indeterminate, X and Y unchanged
	   ^(Z,(0,1),NewZ)                                % Z::boolean
	).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z==(X<Y)  % (Z boolean) generally unsound on reals but possibly useful for minima/maxima

narrowing_op(lt, P, $(Z, X, Y), Out) :-
	X = (Xl,Xh), Y = (Yl,Yh),
	(-1 is cmpr(Xh,Yl)                                 % Xh < Yl
	 -> ^(Z,(1,1),NewZ), P = p, Out = $(NewZ,X,Y)      % persistent X < Y
	 ;  (1 =\= cmpr(Yh,Xl)                             % Yh =< Xl
	     -> ^(Z,(0,0),NewZ), P = p, Out = $(NewZ,X,Y)  % persistent Y =< X	
	     ;  lt_int_(Z,Xl,Xh,Yl,Yh,P,Out)               % possibly non-persistent narrowing cases
	    )
	).

lt_int_((1,1),Xl,Xh,Yl,Yh,P,$((1,1),(Xl,NXh),(NYl,Yh))) :- !,  % common case, narrow X and Y
	next_lt_(Yh,-1,YhD),                              % YhD is next downward value from Yh
	NXh is minr(Xh,YhD),                              % NewX := (Xl,NXh) 
	next_lt_(Xl,1,XlU),                               % NXlU is next upward value from NXl
	NYl is maxr(XlU,Yl),                              % NewY := (NYl,Yh)
	(non_empty(NXh,NYl) -> P=p ; true).               % now persistent?
lt_int_(Z,Xl,Xh,Yl,Yh,P,$(NewZ,NewX,NewY)) :- !,
	(Z == (0,0)
	 -> lt_int_((1,1),Yl,Yh,Xl,Xh,P,$(_,NewY,NewX)),  % false so Y < X
	    NewZ = Z
	 ;  NewX = (Xl,Xh), NewY = (Yl,Yh),               % indeterminate, X and Y unchanged
	   ^(Z,(0,1),NewZ)                                % Z::boolean
	).

% Note: can't narrow an infinite bound, minimize change to bound
% Repeat, not sound on reals (uses nexttoward, missing values between floats)
next_lt_( 1.0Inf, _,  1.0Inf) :- !.
next_lt_(-1.0Inf, _, -1.0Inf) :- !.
next_lt_(V, -1, NV) :- NV is maxr(V-1,nexttoward(V,-1.0Inf)).  % integers will get sorted out with `integral`
next_lt_(V,  1, NV) :- NV is minr(V+1,nexttoward(V, 1.0Inf)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z==(X<=Y)  % inclusion, constrains X to be subinterval of Y (Z boolean)

narrowing_op(in, P, $(Z, X, Y), $(NewZ, NewX, Y)):-
	% Only two cases: either X and Y intersect or they don't.
	(^(X,Y,X1)               % X1 is intersection of X and Y
	 -> (Z == (1,1) 
	     -> NewX = X1        % Z true, X must be subinterval of Y
	     ;  NewX = X,        % Z is false or indeterminate, X unchanged
	        ^(Z,(0,1),NewZ)  % Z boolean
	    )
	 ;  ^(Z,(0,0),NewZ),     % X and Y don't intersect, Z must be false
	 	NewX = X,            % no change in X
	    P=p                  % persistent, since X and Y can never intersect
	).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z==X+Y

narrowing_op(add, _, $((Zl,Zh), (Xl,Xh), (Yl,Yh)), $((NZl,NZh), (NXl,NXh), (NYl,NYh))) :-
	NZl is maxr(Zl, roundtoward( Xl+Yl,  to_negative)),       % NewZ := Z ^ (X+Y),
	NZh is minr(Zh, roundtoward( Xh+Yh,  to_positive)),
	non_empty(NZl,NZh),
	% Note: subtraction done by adding minus values so rounding mode consistent
	% during any numeric type conversion.
	NXl is maxr(Xl, roundtoward(NZl+(-Yh),  to_negative)),    % NewX := X ^ (NZ-Y),
	NXh is minr(Xh, roundtoward(NZh+(-Yl),  to_positive)),
	non_empty(NXl,NXh),
	NYl is maxr(Yl, roundtoward(NZl+(-NXh), to_negative)),    % NewY := Y ^ (NZ-NX).
	NYh is minr(Yh, roundtoward(NZh+(-NXl), to_positive)),
	non_empty(NYl,NYh).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z==X*Y

narrowing_op(mul, _, $(Z,X,Y), $(NewZ, NewX, NewY)) :-
	intCase(Cx,X),
	intCase(Cy,Y),
	multCase(Cx,Cy,X,Y,Z,NewZ),                       % NewZ := Z ^ (X*Y)
	intCase(CNz,NewZ),
	odivCase(CNz,Cx,NewZ,X,Y,Yp),                     % Yp := Y ^ (Z/X),
	intCase(Cyp,Yp),
	odivCase(CNz,Cyp,NewZ,Yp,X,NewX),                 % NewX := X ^ (Z/Yp),
	% if X narrowed it may be necessary to recalculate Y due to non-optimal ordering.
	(Y == Yp, X \== NewX                              % if Y didn't narrow and X did
	 -> intCase(CNx,NewX),
	    odivCase(CNz,CNx,NewZ,NewX,Y,NewY)            % re calculate: NewY := Y ^ NewZ/NewX
	 ;  NewY = Yp
	).
/*  general case, but sub-par performance since some re-calculations unnecessary
narrowing_op(mul, _, $(Z,X,Y), New) :-
	...
	Nxt = $(NewZ,NewX,Yp),
	($(Z,X,Y) == Nxt                   
	 -> New = Nxt                       % no change, exit
	 ;  narrowing_op(mul, _, Nxt, New)  % something narrowed, repeat until no change
	). 
*/

%
% * cases ("Interval Arithmetic: from Principles to Implementation", Fig. 3)
%
% Note: for mixed sign, mixed mode, one of the rounding directions will be incorrect.
%  For now assume(?) this will at worst cancel outward rounding
%multCase(z,_, X, _, _, X) :- !.  % X==0
%multCase(_,z, _, Y, _, Y).       % Y==0

multCase(p,p, (Xl,Xh), (Yl,Yh), (Zl,Zh), (NZl,NZh)):- 
	NZl is maxr(Zl,roundtoward(Xl*Yl,to_negative)),
	NZh is minr(Zh,roundtoward(Xh*Yh,to_positive)),
	non_empty(NZl,NZh).
multCase(p,n, (Xl,Xh), (Yl,Yh), (Zl,Zh), (NZl,NZh)):- 
	NZl is maxr(Zl,roundtoward(Xh*Yl,to_negative)),
	NZh is minr(Zh,roundtoward(Xl*Yh,to_positive)),
	non_empty(NZl,NZh).
multCase(n,p, (Xl,Xh), (Yl,Yh), (Zl,Zh), (NZl,NZh)):- 
	NZl is maxr(Zl,roundtoward(Xl*Yh,to_negative)),
	NZh is minr(Zh,roundtoward(Xh*Yl,to_positive)),
	non_empty(NZl,NZh).
multCase(n,n, (Xl,Xh), (Yl,Yh), (Zl,Zh), (NZl,NZh)):-
	NZl is maxr(Zl,roundtoward(-Xh * -Yh,to_negative)),  % negate for any conversion rounding 
	NZh is minr(Zh,roundtoward(-Xl * -Yl,to_positive)),
	non_empty(NZl,NZh).

multCase(p,s, (Xl,Xh), (Yl,Yh), (Zl,Zh), (NZl,NZh)):-
	NZl is maxr(Zl,roundtoward(Xh*Yl,to_negative)),
	NZh is minr(Zh,roundtoward(Xh*Yh,to_positive)),
	non_empty(NZl,NZh).
multCase(n,s, (Xl,Xh), (Yl,Yh), (Zl,Zh), (NZl,NZh)):-
	NZl is maxr(Zl,roundtoward(Xl*Yh,to_negative)),
	NZh is minr(Zh,roundtoward(-Xl * -Yl,to_positive)),  % negate for any conversion rounding
	non_empty(NZl,NZh).
multCase(s,p, (Xl,Xh), (Yl,Yh), (Zl,Zh), (NZl,NZh)):-
	NZl is maxr(Zl,roundtoward(Xl*Yh,to_negative)),
	NZh is minr(Zh,roundtoward(Xh*Yh,to_positive)),
	non_empty(NZl,NZh).
multCase(s,n, (Xl,Xh), (Yl,Yh), (Zl,Zh), (NZl,NZh)):-
	NZl is maxr(Zl,roundtoward(Xh*Yl,to_negative)),
	NZh is minr(Zh,roundtoward(-Xl * -Yl,to_positive)),  % negate for any conversion rounding
	non_empty(NZl,NZh).

multCase(s,s, (Xl,Xh), (Yl,Yh), (Zl,Zh), (NZl,NZh)):-
	NZl is maxr(Zl,minr(roundtoward(Xl*Yh,to_negative),roundtoward(Xh*Yl,to_negative))),
	NZh is minr(Zh,maxr(roundtoward(-Xl* -Yl,to_positive),roundtoward(Xh*Yh,to_positive))),
	non_empty(NZl,NZh).

%
% / cases ("Interval Arithmetic: from Principles to Implementation", Fig. 4)
% Tricky handling the "zero" cases - returns universal interval when no narowing possible:
%	1. denominator is zero or contains zero (z and s)
%	2. denominator is bounded by zero (p and n) and numerator contains zero (see numeric guards)
% Numeric guards check for 0/0, e.g., p,p -> Xh+Yh>0

odivCase(p,p, (Xl,Xh), (Yl,Yh), (Zl,Zh), (NZl,NZh)) :-
	sign(Yl)+sign(Xl) > 0  % X > 0 or Y > 0
	 -> NZl is maxr(Zl,roundtoward(Xl/Yh,to_negative)),
	    NZh is minr(Zh,roundtoward(Xh/max(0.0,Yl),to_positive)),
	    non_empty(NZl,NZh)
	 ;  NZl = Zl, NZh = Zh.
odivCase(p,n, (Xl,Xh), (Yl,Yh), (Zl,Zh), (NZl,NZh)) :-
	sign(Xl)-sign(Yh) > 0  % X > 0 or Y < 0
	 -> NZl is maxr(Zl,roundtoward(-Xh / -min(-0.0,Yh),to_negative)),  % use min to preserve sign
	    NZh is minr(Zh,roundtoward(-Xl / -Yl          ,to_positive)),
	    non_empty(NZl,NZh)
	 ;  NZl = Zl, NZh = Zh.
odivCase(p,s, (Xl,Xh), (Yl,Yh), (Zl,Zh), (NZl,NZh)) :-
	Xl > 0     % X > 0
	 -> ZIh is roundtoward(Xl/Yh,to_negative),  % (ZIh,inf)
	    ZIl is roundtoward(Xl/Yl,to_positive),  % (-inf,ZIl)
	    ( 1 is cmpr(Zl,ZIl) -> NZl is maxr(Zl,ZIh) ; NZl = Zl),  % Zl > ZIl ?
	    (-1 is cmpr(Zh,ZIh) -> NZh is minr(Zh,ZIl) ; NZh = Zh),  % Zh > ZIl ?
	    non_empty(NZl,NZh)
	 ;  NZl = Zl, NZh = Zh.

odivCase(n,p, (Xl,Xh), (Yl,Yh), (Zl,Zh), (NZl,NZh)):-
	sign(Yl)-sign(Xh) > 0  % X < 0 or Y > 0
	 -> NZl is maxr(Zl,roundtoward(-Xl / -max(0.0,Yl),to_negative)),  % if Yx=0, preserve sign
	    NZh is minr(Zh,roundtoward(-Xh / -max(0.0,Yh),to_positive)),
	    non_empty(NZl,NZh)
	 ;  NZl = Zl, NZh = Zh.
odivCase(n,n, (Xl,Xh), (Yl,Yh), (Zl,Zh), (NZl,NZh)) :-
	sign(Yh)+sign(Xh) < 0  % X < 0 or Y < 0
	 -> NZl is maxr(Zl,roundtoward(Xh/Yl,to_negative)),
	    NZh is minr(Zh,roundtoward(Xl/min(-0.0,Yh),to_positive)),  % use min to preserve sign
	    non_empty(NZl,NZh)
	 ;  NZl = Zl, NZh = Zh.
odivCase(n,s, (Xl,Xh), (Yl,Yh), (Zl,Zh), (NZl,NZh)) :-
	Xh < 0     % X < 0
	 -> ZIh is roundtoward( Xh /  Yl,to_negative),  % (ZIh,inf)
	    ZIl is roundtoward(-Xh / -Yh,to_positive),  % (-inf,ZIl)
	    ( 1 is cmpr(Zl,ZIh) -> NZl is maxr(Zl,ZIl) ; NZl = Zl),  % Zl > ZIh ?
	    (-1 is cmpr(Zh,ZIl) -> NZh is minr(Zh,ZIh) ; NZh = Zh),  % Zh > ZIl ?
	    non_empty(NZl,NZh)
	 ;  NZl = Zl, NZh = Zh.

odivCase(s,p, (Xl,Xh), (Yl,Yh), (Zl,Zh), (NZl,NZh)) :-
	Yl > 0     % Y > 0
	 -> NZl is maxr(Zl,roundtoward(-Xl / -Yl,to_negative)),
	    NZh is minr(Zh,roundtoward( Xh /  Yl,to_positive)),
	    non_empty(NZl,NZh)
	 ;  NZl = Zl, NZh = Zh.
odivCase(s,n, (Xl,Xh), (Yl,Yh), (Zl,Zh), (NZl,NZh)) :-
	Yh < 0     % Y < 0
	 -> NZl is maxr(Zl,roundtoward(Xh/Yh,to_negative)),
	    NZh is minr(Zh,roundtoward(Xl/Yh,to_positive)),
	    non_empty(NZl,NZh)
	 ;  NZl = Zl, NZh = Zh.

odivCase(s,s,       _,       _,       Z,         Z).  % both contain 0, no narrowing

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z==min(X,Y)    Z==max(X,Y)

narrowing_op(min, _, $((Zl,Zh),(Xl,Xh),(Yl,Yh)), New) :-
	Z1l is maxr(Zl,minr(Xl,Yl)),  % Z1 := Z ^ min(X,Y),
	Z1h is minr(Zh,minr(Xh,Yh)),
	minimax((Zl,1.0Inf), (Z1l,Z1h),(Xl,Xh),(Yl,Yh), New).

narrowing_op(max, _, $((Zl,Zh),(Xl,Xh),(Yl,Yh)), New) :-
	Z1l is maxr(Zl,maxr(Xl,Yl)),  % Z1 := Z ^ max(X,Y),
	Z1h is minr(Zh,maxr(Xh,Yh)),
	minimax((-1.0Inf,Zh), (Z1l,Z1h),(Xl,Xh),(Yl,Yh), New).

minimax(_, Z1,X,Y, NewXYZ) :-                  % Case 1, X not in Z1
	\+(^(Z1,X,_)), !,                          % _ := Z1 \^ X,
	NewXYZ = $(New, X, New),
	^(Y,Z1,New).                               % New := Y ^ Z1.

minimax(_, Z1,X,Y, NewXYZ) :-                  % Case 2, Y not in Z1
	\+(^(Z1,Y,_)), !,                          % _ := Z1 \^ Y,
	NewXYZ = $(New, New, Y),
	^(X,Z1,New).                               % New := X ^ Z1.

minimax(Zpartial, Z1,X,Y, $(Z1, NewX, NewY)) :- % Case 3, overlap
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
	NZl is maxr(Zl,-Xh), NZh is minr(Zh,-Xl),
	non_empty(NZl,NZh).

%
% abs(X) cases
%
absCase(p, (Xl,Xh), (Zl,Zh), (NZl,NZh)) :- NZl is maxr(Zl,Xl),  NZh is minr(Zh,Xh).
absCase(n, (Xl,Xh), (Zl,Zh), (NZl,NZh)) :- NZl is maxr(Zl,-Xh), NZh is minr(Zh,-Xl).
absCase(s, (Xl,Xh), (Zl,Zh), (NZl,NZh)) :- NZl is maxr(Zl,0),   NZh is minr(Zh,maxr(-Xl,Xh)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z== -X

narrowing_op(minus, _, $((Zl,Zh),(Xl,Xh)), $((NZl,NZh),(NXl,NXh))) :-
	NZl is maxr(Zl,-Xh), NZh is minr(Zh,-Xl),    % NewZ := Z ^ -X, no empty check required
	NXl is maxr(Xl,-NZh), NXh is minr(Xh,-NZl).  % NewX := X ^ -Z, no empty check required

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z== sqrt(X)  (Z is positive root of positive X)

narrowing_op(sqrt, _, $((Zl,Zh),(Xl,Xh)), $((NZl,NZh),(NXl,NXh))) :-
	Xh>=0, Xl1 is maxr(0,Xl),  % narrow X to positive range
	NZl is maxr(maxr(0,Zl),roundtoward(sqrt(Xl1),to_negative)),
	NZh is minr(Zh,roundtoward(sqrt(Xh),to_positive)),
	non_empty(NZl,NZh),
	NXh is minr(Xh,roundtoward(NZh*NZh,to_positive)),
	NXl is maxr(Xl,-NXh),
	non_empty(NXl,NXh).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z== exp(X)

narrowing_op(exp, _, $((Zl,Zh),(Xl,Xh)), $((NZl,NZh),(NXl,NXh))) :-
	NZl is maxr(Zl,roundtoward(exp(Xl),to_negative)),
	NZh is minr(Zh,roundtoward(exp(Xh),to_positive)),
	non_empty(NZl,NZh),
	NXl is maxr(Xl,roundtoward(log(NZl),to_negative)),
	NXh is minr(Xh,roundtoward(log(NZh),to_positive)),
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
pt_powrCase(N1,D1,Z,X,R,NewZ) :-  R < 0, !,      % R negative
	Rp is -R,
	universal_interval(UI),
	intCase(Cz,Z),
	odivCase(p,Cz,(1,1),Z,UI,Zi),                % Zi := UI ^ 1/Z
	pt_powrCase(N1,D1,Zi,X,Rp,NZi),
	intCase(CNzi,NZi),
	odivCase(p,CNzi,(1,1),NZi,Z,NewZ).           % NewZ := Z ^ 1/NZi

pt_powrCase(1,0,(Zl,Zh),(Xl,Xh),R,(NZl,NZh)) :-  % R positive, numerator odd, denominator even
	% reflect about X axis to include positive and negative roots
	Xh >=0,   % some part of X must be positive
	Zl1 is maxr(0, roundtoward(Xl**R,to_negative)),  % neg Xl ==> nan
	Zh1 is roundtoward(Xh**R,to_positive),
	Zpl is maxr(Zl,Zl1),  Zph is minr(Zh,Zh1),       % positive case
	Znl is maxr(Zl,-Zh1), Znh is minr(Zh,-Zl1),      % negative case
	( 1 is cmpr(Znl,Znh) -> NZl is Zpl, NZh is Zph   % Znl > Znh -> negative case is empty
	; 1 is cmpr(Zpl,Zph) -> NZl is Znl, NZh is Znh   % Zpl > Zph -> positive case is empty
	; NZl is minr(Zpl,Znl), NZh is maxr(Zph,Znh)     % else union of positive and negative cases
	).

pt_powrCase(0,1,(Zl,Zh),(Xl,Xh),R,(NZl,NZh)) :-  % R positive, numerator even, denominator odd
	% reflect about Z axis
	( Xh < 0 -> Xl1 is -Xh, Xh1 is -Xl           % negative X, negate interval
	;(Xl > 0 -> Xl1 = Xl, Xh1 = Xh               % positive X, As is
	;           Xl1 = 0, Xh1 is maxr(-Xl,Xh)     % split
	)),
	% NZl can't be negative
	NZl is maxr(Zl, roundtoward(Xl1**R,to_negative)),  % Xl1 known to be positive
	NZh is minr(Zh, roundtoward(Xh1**R,to_positive)).

pt_powrCase(1,1,(Zl,Zh),(Xl,Xh),R,(NZl,NZh)) :-  % R positive, numerator odd, denominator odd
	% continuous monotonic
	NZl is maxr(Zl, roundtoward(Xl**R,to_negative)),
	NZh is minr(Zh, roundtoward(Xh**R,to_positive)).

% Y is an interval
powr_intY_(p, Z,X,Y, NewZ,NewX,NewY) :-              % positive X, interval Y 
	powr_prim_(Z,X,Y,NewZ),                          % NewZ := X**Y
	universal_interval(UI),
	intCase(Cy,Y),
	odivCase(p,Cy,(1,1),Y,UI,Yi),                    % Yi := UI ^ 1/Y 
	powr_prim_(X,NewZ,Yi,NewX),                      % NewX := NewZ**(1/Y) (no narrow if 0 in Y)
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
	NZl is -Znh, NZh is maxr(Znh,Zph), ^(Z,(NZl,NZh),NewZ),
	union_(NXn,NXp,NX), ^(X,NX,NewX),
	union_(NYn,NYp,NY), ^(Y,NY,NewY).
	
powr_prim_((Zl,Zh), (Xl,Xh), (Yl,Yh), NewZ) :-        % X assumed positive
	Zll is roundtoward(Xl**Yl,to_negative),
	Zlh is roundtoward(Xl**Yh,to_positive),
	Zhl is roundtoward(Xh**Yl,to_negative),
	Zhh is roundtoward(Xh**Yh,to_positive),
	NZl is maxr(Zl,minr(Zll, minr(Zlh, minr(Zhl, Zhh)))), % intersect with min of all
	NZh is minr(Zh,maxr(Zll, maxr(Zlh, maxr(Zhl, Zhh)))), % intersect with max of all
	(non_empty(NZl,NZh) -> NewZ = (NZl,NZh) ; NewZ = (Zl,Zh)).  % on empty, no narrowing 

ln((Xl,Xh), (Zl,Zh)) :-
	Zl is roundtoward(log(Xl),to_negative),
	Zh is roundtoward(log(Xh),to_positive).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z== sin(X)

narrowing_op(sin, _, $(Z,X), $(NewZ, NewX)) :-
	sin_(X,S,Z,NewZ),
	asin_(NewZ,S,X,NewX).

sin_((Xl,Xh),(Sl,Sh),Z,NZ) :-
	(Xl == Xh, abs(Xl) =:= 1.0Inf
	 -> Sl = -10, Sh = 10,                 %  point infinity special case
	    ^(Z,(-1.0,1.0),NZ)
	 ;  Sl is floor(roundtoward(Xl/pi+0.5,to_positive)), % determine monotonic sector of width pi
	    Sh is floor(roundtoward(Xh/pi+0.5,to_negative)), % sector 0 is (-pi/2,pi/2) - see asin(x)
	    ( Sh-Sl =< 2                       % more than 2 sectors -> no narrowing
	     -> to_float((Xl,Xh),FX),          % convert now to float
	        sinCase_(FX,Sl,Sh,Z,(1,-1),NZ),
	        non_empty(NZ)
	     ; ^(Z,(-1.0,1.0),NZ) 
	    )
	).

sinCase_(X,Sl,Sh,Z,ZIn,NZ) :-
	(Sl == Sh
	 -> sinSector_(Sl,X,Z,ZIn,NZ)          % single/last sector 
	 ;  XSh is pi*(Sl+0.5),                % spanning sectors =<2
	    X = (Xl,Xh),
	    sinSector_(Sl,(Xl,XSh),Z,ZIn,ZOut),
	    SNl is Sl+1,
	    sinCase_((XSh,Xh),SNl,Sh,Z,ZOut,NZ)
	).

sinSector_(S,(Xl,Xh),(Zl,Zh),(ZlIn,ZhIn),(ZlOut,ZhOut)) :-
	( 0 is S mod 2                         % monotonically increasing ?
	 -> ZSl is roundtoward(sin(Xl), to_negative),
	    ZSh is roundtoward(sin(Xh), to_positive)
	 ;  ZSl is roundtoward(sin(Xh), to_negative),
	    ZSh is roundtoward(sin(Xl), to_positive)
	),
	( ^((Zl,Zh),(ZSl,ZSh),(Z1l,Z1h)) % union with previous Z*In
	 -> ZlOut is minr(ZlIn,Z1l), ZhOut is maxr(ZhIn,Z1h)
	 ;  ZlOut = ZlIn,            ZhOut = ZhIn 
	).

asin_(Z,S,X,NX) :- 
	( Z == (-1.0,1.0)
	 -> NX = X                             % no narrowing of X possible based on Z
	 ;  S = (Sl,Sh),
	    (Sl == Sh
	     -> asinSector_(Sl,Z,XS),          % same sector
	        ^(X,XS,NX)
	     ;  ( Sh-Sl =< 2                   % X spans sectors
	         -> asinCaseLo_(Sl,Z,X,XSl),
	            asinCaseHi_(Sh,Z,X,XSh),
	            ^(X,(XSl,XSh),NX)
	         ;  NX = X
	        )
	    ) 
	).

asinCaseLo_(S,Z,X,NXl) :-
	asinSector_(S,Z,XS),
	( ^(X,XS,(NXl,_))
	 -> true
	 ;  X = (_,Xh), Xh >= pi*(S+0.5),      % next sector in range 
	    S1 is S+1,
	    asinCaseLo_(S1,Z,X,NXl)
	).

asinCaseHi_(S,Z,X,NXh) :-
	asinSector_(S,Z,XS),
	( ^(X,XS,(_,NXh))
	 -> true
	 ;  X = (Xl,_), Xl =< pi*(S-0.5),      % previous sector in range 
	    S1 is S-1, 
	    asinCaseHi_(S1,Z,X,NXh)
	).

asinSector_(S,(Zl,Zh),(XSl,XSh)) :-
	Offs is S*pi,
    bounded_number(Offl,Offh,Offs),     % fuzz offset
%%	Offl is nexttoward(S*pi,-inf), Offh is nexttoward(S*pi,inf),  % fuzz offset
%%	Offl is roundtoward(S*pi,to_negative), Offh is roundtoward(S*pi,to_positive),  % fuzz offset
	(0 is S mod 2
	 -> XSl is roundtoward(Offl+asin(Zl),to_negative),  % monotonically increasing
	    XSh is roundtoward(Offh+asin(Zh),to_positive)
	 ;  XSl is roundtoward(Offl-asin(Zh),to_negative),  % monotonically decreasing
	    XSh is roundtoward(Offh-asin(Zl),to_positive)
	).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z== cos(X)

narrowing_op(cos, _, $(Z,X), $(NewZ, NewX)) :-
	cos_(X,S,Z,NewZ),
	acos_(NewZ,S,X,NewX).

cos_((Xl,Xh),(Sl,Sh),Z,NZ) :-
	(Xl == Xh, abs(Xl) =:= 1.0Inf
	 -> Sl = -10, Sh = 10,                 %  point infinity special case
	    ^(Z,(-1.0,1.0),NZ)
	 ;  Sl is floor(roundtoward(Xl/pi,to_positive)),  % determine monotonic sector of width pi
	    Sh is floor(roundtoward(Xh/pi,to_negative)),  % sector 0 is (0,pi) - see acos(x)
	    ( Sh-Sl =< 2                           % more than 2 sectors -> no narrowing
	     -> to_float((Xl,Xh),FX),       % convert now to float
	        cosCase_(FX,Sl,Sh,Z,(1,-1),NZ),
	        non_empty(NZ)
	     ; ^(Z,(-1.0,1.0),NZ)
	    )
	).

cosCase_(X,Sl,Sh,Z,ZIn,NZ) :- 
	( Sl == Sh
	 -> cosSector_(Sl,X,Z,ZIn,NZ)          % single/last sector 
	 ;  SNl is Sl+1,                       % spanning sectors =<2
	    XSh is pi*(Sl+1),
	    X = (Xl,Xh),
	    cosSector_(Sl,(Xl,XSh),Z,ZIn,ZOut),
	    cosCase_((XSh,Xh),SNl,Sh,Z,ZOut,NZ)
	).

cosSector_(S,(Xl,Xh),(Zl,Zh),(ZlIn,ZhIn),(ZlOut,ZhOut)) :-
	( 1 is S mod 2                         % monotonically increasing ?
	 -> ZSl is roundtoward(cos(Xl), to_negative),
	    ZSh is roundtoward(cos(Xh), to_positive)
	 ;  ZSl is roundtoward(cos(Xh), to_negative),
	    ZSh is roundtoward(cos(Xl), to_positive)
	),
	( ^((Zl,Zh),(ZSl,ZSh),(Z1l,Z1h)) % union with previous Z*In
	 -> ZlOut is minr(ZlIn,Z1l), ZhOut is maxr(ZhIn,Z1h)
	 ;  ZlOut = ZlIn,            ZhOut = ZhIn 
	).

acos_(Z,S,X,NX) :- 
	( Z == (-1.0,1.0)
	 -> NX = X                             % no narrowing of X possible based on Z
	 ;  S = (Sl,Sh),
	    (Sl == Sh
	     -> acosSector_(Sl,Z,XS),          % same sector
	        ^(X,XS,NX)
	     ;  ( Sh-Sl =< 2                   % X spans sectors
	         -> acosCaseLo_(Sl,Z,X,XSl),
	            acosCaseHi_(Sh,Z,X,XSh),
	            ^(X,(XSl,XSh),NX)
	         ;  NX = X
	        )
	    ) 
	).

acosCaseLo_(S,Z,X,NXl) :-
	acosSector_(S,Z,XS),
	( ^(X,XS,(NXl,_))
	 -> true
	 ;  S1 is S+1,                         % next sector in range 
	    X = (_,Xh), Xh >= pi*S1,
	    acosCaseLo_(S1,Z,X,NXl)
	).

acosCaseHi_(S,Z,X,NXh) :-
	acosSector_(S,Z,XS),
	( ^(X,XS,(_,NXh))
	 -> true
	 ;  X = (Xl,_), Xl =< pi*S,            % previous sector in range 
	    S1 is S-1,
	    acosCaseHi_(S1,Z,X,NXh)
	).

acosSector_(S,(Zl,Zh),(XSl,XSh)) :-
	X1l is roundtoward(acos(Zh),to_negative),
	X1h is roundtoward(acos(Zl),to_positive),
	(1 is S mod 2
	 -> Offs is (S+1)*pi,
	    bounded_number(Offl,Offh,Offs),     % fuzz offset
	    XSl is roundtoward(Offl-X1h,to_negative),  % monotonically increasing
	    XSh is roundtoward(Offh-X1l,to_positive)
	 ;  Offs is S*pi,
	    bounded_number(Offl,Offh,Offs),     % fuzz offset
	    XSl is roundtoward(Offl+X1l,to_negative),  % monotonically decreasing
	    XSh is roundtoward(Offh+X1h,to_positive)
	).

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
tanCase((Zl,Zh),(Xl,Xh),S,S,(NZl,NZh),NX) :-  !,          % same sector
	Z1l is roundtoward(tan(Xl),to_negative),
	Z1h is roundtoward(tan(Xh),to_positive),
	( non_empty(Z1l,Z1h)
	 -> ^((Zl,Zh),(Z1l,Z1h),(NZl,NZh)),                   % good range
	    atan_((NZl,NZh),S,X1),
	    ^((Xl,Xh),X1,NX)
	 ;  % same sector range check failed, assume rounding crossed singularity
	    ((Z1l =< Zh ; Z1h >= Zl) -> true),                % disjoint ranges must intersect Z
	    NZl = Zl, NZh = Zh, NX = (Xl,Xh)                  % nothing changes
	).
tanCase(Z,(Xl,Xh),Sl,Sh,(NZl,NZh),(NXl,NXh)) :-  Sh-Sl =:= 1,  % spans one singularity
	Sg is pi*(Sl+0.5),               % closest to singularity (integer Sl and 0.5 is precise float)
	bounded_number(XSl,XSh,Sg),      % use bounded number to straddle
	(tanCase(Z,(Xl,XSl),Sl,Sl,(NZ1l,NZ1h),(NXl,NX1h))
	 -> (tanCase(Z,(XSh,Xh),Sh,Sh,_NZ2,(_,NXh))
	     -> fail                                          % both sectors, includes singularity
	     ;  NXh = NX1h, NZl = NZ1l, NZh = NZ1h            % only lo sector
	    )
	 ;  tanCase(Z,(XSh,Xh),Sh,Sh,(NZl,NZh),(NXl,NXh))     % only hi sector
	),
	!.
tanCase(Z,X,Sl,Sh,Z,NX) :-  Sh-Sl =:= 2, %% spans two singularities due to rounding
	% X is odd multiple of (-pi/2,pi/2)	?
	X = (Xl,Xh),
	LB is rational(roundtoward(Xl/pi + 0.5, to_positive)), integer(LB),	
	UB is rational(roundtoward(Xh/pi + 0.5, to_negative)), integer(UB),
	!,
	S is (Sl+Sh)/2,
	atan_(Z,S,X1), ^(X,X1,NX).
tanCase(Z,X,Sl,Sh,Z,X).                                   % spans multiple singularities

atan_((Zl,Zh),S,(Xl,Xh)) :-
	Offs is S*pi,
	bounded_number(Offl,Offh,Offs),                       % fuzz offset
	Xl is Offl+roundtoward(atan(Zl),to_negative),
	Xh is Offh+roundtoward(atan(Zh),to_positive).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Z== ~X boolean negation (Z and X boolean)

narrowing_op(not, P, $(Z,X), $(NewZ, NewX)) :-
	notB_(X,Z,Z1,P), ^(Z,Z1,NewZ),
	notB_(NewZ,X,X1,P), ^(X,X1,NewX).

notB_((0,0), _, (1,1), p) :- !.
notB_((1,1), _, (0,0), p) :- !.
notB_(    _, Z, NewZ,  _) :- ^(Z,(0,1),NewZ).

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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- style_check(+singleton).  % for narrowing_op

% User defined IA primitives

narrowing_op(user(Prim), P, InArgs, OutArgs) :-
	call_user_primitive(Prim, P, InArgs, OutArgs).  % from main module body
