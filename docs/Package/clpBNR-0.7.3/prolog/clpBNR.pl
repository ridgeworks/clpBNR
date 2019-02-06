%%%% Package file:
%
% CLP(BNR) == Constraints On Boolean, Integer, and Real Intervals
%
:- module(clpBNR,          % SWI module declaration
	[
	op(700, xfx, ::),
	(::)/2,                % declare interval
	{}/1,                  % define constraint
	interval/1,            % filter for clpBNR constrained var
	numeric/1,             % filter for numeric Prolog terms: (integer;float;rational)
	list/1,                % for compatibility
	domain/2, range/2,     % for compatibility
	lower_bound/1,         % narrow interval to point equal to lower bound
	upper_bound/1,         % narrow interval to point equal to upper bound

	% additional constraint operators
	op(200, fy, ~),        % boolean 'not'
	op(500, yfx, and),     % boolean 'and'
	op(500, yfx, or),      % boolean 'or'
	op(500, yfx, nand),    % boolean 'nand'
	op(500, yfx, nor),     % boolean 'nor'
	op(500, yfx, xor),     % boolean 'xor'
	op(700, xfx, <>),      % integer not equal
	op(700, xfx, <=),      % set inclusion
	op(700, xfx, =>),      % set inclusion

	% utilities
	print_interval/1,      % print interval as list of two numbers (for compatability)
	solve/1, solve/2,      % solve (list of) intervals using split to find point solutions
	splitsolve/1, splitsolve/2,   % solve (list of) intervals using split
	absolve/1, absolve/2,  % absolve (list of) intervals, narrows by nibbling bounds
	minimize/3,            % minimize interval using user defined Solver
	maximize/3,            % maximize interval using user defined Solver
	enumerate/1,           % "enumerate" integers
	simplify/2,            % general purpose predicate for simplifying expressions of variables
	clpStatistics/0,       % reset
	clpStatistic/1,        % get selected
	clpStatistics/1        % get all defined in a list
	]).

	
/* missing(?) functionality:

1. arithmetic functions on intervals (delta, median, midpoint). Requires hooking is/2.
	
2. utility accumulate/2.

*/

/* supported interval relations:

+	-	*	/	**                    %% arithmetic
**                                    %% includes real exponent, odd/even integer
abs                                   %% absolute value
sqrt                                  %% square root (needed?)
min	max                               %% binary min/max
==	is	<>	=<	>=	<	>             %% comparison
<=	=>                                %% inclusion
and	or	nand	nor	xor	->            %% boolean
-	~                                 %% unary negate and not
exp	log                               %% exp/ln
sin	asin	cos	acos	tan	atan      %% trig functions

*/

:- style_check([-singleton, -discontiguous]).

%
% list(X) for compatability
%
list(X) :- is_list(X).

% numeric test (number or rational)
%
numeric(C) :- number(C), !.
numeric(C) :- rational(C).

%%%%:- include(ia_primitives).  % interval arithmetic relations via evalNode/4.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  SWI-Prolog implementation
%
%
% Arithmetic "eval" with specified rounding direction.
% Assumes underlying IEEE 754 with rounding to nearest FP value (1/2 ulp).
% This will be wrong 50% of the time: rounding down/up for upper/lower bound.
% Therefore, an additional "outward" rounding is done to be safe.
% Calculation based on normalized machine "epsilon" which is twice the distance between
% 1.0 and the next highest FP value. Therefore the maximum rounding "error" for a 
% calculated FP value X is abs(X)*epsilon. The bound is adjusted by this amount.
%
%
% Rounding "out" evaluation for a single FP operation.
%
:- op(700, xfx, 'isL').  % adjust result toward -Infinity
:- op(700, xfx, 'isH').  % adjust result toward +Infinity

% Exp is single FP operation, e.g.,  X+Y, X*Y, sin(X), etc.
% Multiple ops in Exp could violate assumptions about bit accuracy.
% Assumes IEEE 754 compliance in evaluating Exp.
% Note that arguments of catch are kept simple to minimize meta-call overheads.

Z isL Exp :- catch(evalDown(Z,Exp), Error, recover(Exp,Error,Z)), !.

Z isH Exp :- catch(evalUp(Z,Exp),   Error, recover(Exp,Error,Z)), !.

evalDown(Z,Exp) :-
	R is Exp, roundDown(R,Z,Exp).
	
roundDown(R,Z,Exp) :-
	rational(R),  %integer(R),
	(current_prolog_flag(bounded,true) -> chkIResult(Exp,R,Z) ; Z=R).
roundDown(0.0,SmallestNeg,_) :-
	SmallestNeg is -(2**(-1022)).
roundDown(R,Z,_) :-  % check if R can be rounded without overflow
	Z is R - abs(R)*epsilon.  % could overflow to -infinity

evalUp(Z,Exp) :-
	R is Exp, roundUp(R,Z,Exp).

roundUp(R,Z,Exp) :-
	rational(R),  %integer(R),
	(current_prolog_flag(bounded,true) -> chkIResult(Exp,R,Z) ; Z=R).
roundUp(0.0,SmallestPos,_) :-
	SmallestPos is (2**(-1022)).
roundUp(R,Z,_) :-  % check if R can be rounded without overflow
	Z is R + abs(R)*epsilon.  % could overflow to +infinity

recover(Exp,error(evaluation_error(Error),C),Z) :-  % unwraps evaluation errors
	recover_(Exp,Error,Z),!.             % generate various infinities
recover(Exp,error(Error,context(P,_)),Z) :-
	throw(error(Error,context(P,Exp))).  % no recovery possible, rethrow with expression

% recover_/3 mainly converts floating point overflows to infinite values depending 
%	on the signs of the operands. Straight forward in most cases but add and subtract
%	are a bit tricky; a table of sign(X) vs. sign(Y) identifies the cases. (Note that
%	sign(X)=sign(Y)=0 can't happen.)
%
% Assumes simple expressions - one or two numeric operands
% Some expressions, e.g., inf-inf or inf/inf, will generate undefined which results in an exception

recover_(X+Y, float_overflow, Z)       :- S is sign(X)+sign(Y), S=\=0, Z is copysign(inf,S).
recover_(X+Y, float_overflow, Z)       :- (abs(X) > abs(Y) -> Z is copysign(inf,X) ; Z is copysign(inf,Y)).
recover_(X+Y, undefined, X)            :- abs(X) =:= inf, abs(Y) =:= inf.  % OK as a upper/lowerbound

recover_(X-Y, float_overflow, Z)       :- S is sign(X)-sign(Y), S=\=0, Z is copysign(inf,S).
recover_(X-Y, float_overflow, Z)       :- (abs(X) > abs(Y) -> Z is copysign(inf,X) ; Z is copysign(inf,-Y)).
recover_(X-Y, undefined, X)            :- abs(X) =:= inf, abs(Y) =:= inf.  % OK as a upper/lowerbound

recover_(log(X), float_overflow, 1.0Inf).
recover_(log(X)/N, float_overflow, 1.0Inf).
recover_(log(X), undefined, -1.0Inf)   :- X =:= 0.

recover_(X*Y, float_overflow, Z)       :- Z is copysign(inf,sign(X)*sign(Y)).
recover_(X*Y, undefined, Z)            :- Z is copysign(inf,sign(X)+sign(Y)).    % must be 0*inf ?

recover_(X/Y, float_overflow, Z)       :- Z is copysign(inf,sign(X)*sign(Y)).
recover_(X/Y, zero_divisor, Z)         :- Z is copysign(inf,X).
recover_(InfN/InfD, undefined, InfN)   :- abs(InfN) =:= inf, abs(InfD) =:= inf.  % OK as a upper/lowerbound

recover_(X**Y, float_overflow, 1.0Inf) :- Z is copysign(inf,X).

recover_(exp(X), float_overflow, 1.0Inf).

recover_(Inf, float_overflow, FPinf)  :- abs(Inf) =:= inf, FPinf is Inf.

%
% integer overflow checking : (platform requires prolog flag 'bounded'.)
%

chkIResult(X*Y,0,0)       :- !.
chkIResult(X*Y,Z,Z)       :- X is Z//Y, !.             % overflow if inverse op fails, convert to infinity
chkIResult(X*Y,Z,1.0Inf)  :- 1 is sign(X)*sign(Y), !.
chkIResult(X*Y,Z,-1.0Inf) :- !.

chkIResult(X+Y,Z,Z)       :- sign(X)*sign(Y) =< 0, !.  % overflow not possible
chkIResult(X+Y,Z,Z)       :- sign(X)*sign(Z) >= 0, !.  % no overflow if result consistent with operands
chkIResult(X+Y,Z,1.0Inf)  :- sign(X) >= 0, !.
chkIResult(X+Y,Z,-1.0Inf) :- !.

chkIResult(X-Y,Z,Z)       :- sign(X)*sign(Y) >= 0, !.  % overflow not possible
chkIResult(X-Y,Z,Z)       :- sign(X)*sign(Z) >= 0, !.  % no overflow if result consistent with operands
chkIResult(X-Y,Z,1.0Inf)  :- sign(X) >= 0, !.
chkIResult(X-Y,Z,-1.0Inf) :- !.

chkIResult(  _,Z,Z). % otherwise OK.

%
% statistics
%

clpStatistics :-
	% garbage_collect,  % ? do gc before time snapshots
	T is cputime, nb_setval(userTime_,T), 
	statistics(inferences,I), nb_setval(inferences_,I),
	statistics(garbage_collection,[_,_,G,_]), nb_setval(gc_time_,G),
	fail.  % backtrack to reset other statistics.

clpStatistic(userTime(T)) :- T1 is cputime, nb_getval(userTime_,T0), T is T1-T0.

clpStatistic(gcTime(G)) :- statistics(garbage_collection,[_,_,G1,_]), nb_getval(gc_time_,G0), G is (G1-G0)/1000.

clpStatistic(globalStack(U/T)) :- statistics(globalused,U), statistics(global,T).

clpStatistic(trailStack(U/T)) :- statistics(trailused,U), statistics(trail,T).

clpStatistic(localStack(U/T)) :- statistics(localused,U), statistics(local,T).

clpStatistic(inferences(I)) :- statistics(inferences,I1), nb_getval(inferences_,I0), I is I1-I0.

% zero/increment/read global counter
g_zero(G)   :- nb_setval(G,0).
g_inc(G)    :- nb_getval(G,N), succ(N,N1), nb_linkval(G,N1).
g_read(G,C) :- nb_getval(G,C).

%
%  End of SWI defintions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%
% Interval constants
%
universal_interval([-1.0Inf,1.0Inf]).

% Finite intervals - 64 bit IEEE reals, 
%finite_interval(real,    [-1.7976931348623157e+308,1.7976931348623157e+308]).  % ? from Wikipedia IEEE doubles
finite_interval(real,    [-1.0e+154,1.0e+154]).  % approx. the sqrt of max float
finite_interval(integer, [L,H]) :-  %% SWIP:
	current_prolog_flag(bounded,false),!,  % integers are unbounded, but use tagged limits for finite default
	current_prolog_flag(min_tagged_integer,L),
	current_prolog_flag(max_tagged_integer,H).
finite_interval(integer, [L,H]) :-
	current_prolog_flag(bounded,true),
	current_prolog_flag(min_integer,L),
	current_prolog_flag(max_integer,H).
%finite_interval(boolean, [0,1]).

% Empty (L>H)
%empty_interval([L,H]) :- universal_interval([H,L]).

%
% API function for executing primitives
%
% evalNode(+primitive_name, ?persistence_flag, +list_of_inputs, ?list_of_outputs)
%
evalNode(Op, P, Is, R) :-
	g_inc(evalNode),  % count of primitive calls
	narrowing_op(Op, P, Is, R),
	!.
evalNode(Op, P, Is, _):-
	g_inc(evalNodeFail),  % count of primitive call failures
%	evalfail_(Op,Is),
	fail.

evalfail_(Op,Is) :- nl,write(evalNode_fail(Op,Is)),nl.

clpStatistics :-
	g_zero(evalNode),
	g_zero(evalNodeFail),
	fail.  % backtrack to reset other statistics.

clpStatistic(narrowingOps(C)) :- g_read(evalNode,C).

clpStatistic(narrowingFails(C)) :- g_read(evalNodeFail,C).


%
% interval primitive functions
% X, Y and Z are intervals
%

% Z := X ^ Y  (intersection)
^([Xl,Xh], [Yl,Yh], [Zl,Zh]) :-
	Zl is max(Xl, Yl),
	Zh is min(Xh, Yh),
	Zl =< Zh.
	
% Z <> X, where where Z and X are integer intervals, fails if not an integer
<>([L,H], [X,X], [NewL,H]) :- integer(L), L =:= X, !,
	NewL is L+1, NewL=<H.  % X is a point,  and low bound of Z
<>([L,H], [X,X], [L,NewH]) :- integer(H), H =:= X, !,
	NewH is H-1, L=<NewH.  % X is a point,  and high bound of Z
<>(Z, X, Z).

% Z := X + Y  (add)
+([Xl,Xh], [Yl,Yh], [Zl,Zh]) :-
	Zl isL Xl+Yl, Zh isH Xh+Yh.            % Z := [Xl+Yl, Xh+Yh].

% Z := X - Y  (subtract)
-([Xl,Xh], [Yl,Yh], [Zl,Zh]) :-
	Zl isL Xl-Yh, Zh isH Xh-Yl.            % Z := [Xl-Yh, Xh-Yl].

% Z := -X (unary minus)
-([Xl,Xh], [Zl,Zh]) :-
	Zl is -Xh, Zh is -Xl.

% Z := X * Y  (multiply)
*(X, Y, Z) :-
	intCase(Cx,X),
	intCase(Cy,Y),
	multCase(Cx,Cy,X,Y,Z).
	
% Z := X / Y  (odiv)
/([Xl,Xh], [Yl,Yh], Z) :-
	Xl=<0,Xh>=0,Yl=<0,Yh>=0,!,  % both X and Y contain 0
	universal_interval(Z).

/(X, Y, Z) :-
	chkDiv(Y,X),     % if Y is 0, X must contain 0
	intCase(Cx,X),
	intCase(Cy,Y),
	odivCase(Cx,Cy,X,Y,Z).
	
% Z := min(X,Y)  (minimum)
min([Xl,Xh], [Yl,Yh], [Zl,Zh]) :-
	Zl is min(Xl,Yl), Zh is min(Xh,Yh).    % Z := [min(Xl,Yl), min(Xh,Yh)].

% Z := max(X,Y)  (maximum)
max([Xl,Xh], [Yl,Yh], [Zl,Zh]) :-
	Zl is max(Xl,Yl), Zh is max(Xh,Yh).    % Z := [max(Xl,Yl), max(Xh,Yh)].
	
% Z := abs(X)
abs(X, Z) :-
	intCase(Cx,X),
	absCase(Cx,X,Z).
	
% Z := exp(X)  (e^X)
exp([Xl,Xh], [Zl,Zh]) :-                   % Zl can never be negative due to rounding
	Zlx isL exp(Xl), Zl is max(Zlx,0),     % Z := [exp(Xl), exp(Xh)].
	Zh isH exp(Xh).

% Z := log(X)  (ln(X))
log([Xl,Xh], [Zl,Zh]) :-
	Xh > 0,
	Zl isL log(max(0,Xl)), Zh isH log(Xh). % Z := [log(Xl), log(Xh)].

% Z:= X**N for integer(N)
intpow(X,[N,N],Z) :-
	Odd is abs(N) rem 2,
	intCase(Cx,X),
	intCase(Cn,[N,N]),
	ipCase(Cx, Cn, Odd, N, X, Z), !.
	
% Z := root(X,N) , i.e., Nth root of X where integer(N)<>0 
% Uses current value of Z for separating even N casescases
nthroot(X,[N,N],Z,NewZ) :-
	Odd is abs(N) rem 2,
	intCase(Cx,X),
	intCase(Cz,Z),
	intCase(Cn,[N,N]),
	nthrootCase(Cx,Cn,Cz,Odd,N,X,Z,NewZ), !.
	
% Z:= sin(X), -pi/2=<X=<pi/2
sin([Xl,Xh],Z) :-
	Z1l isL sin(Xl), Z1h isH sin(Xh),
	^([Z1l,Z1h],[-1,1],Z).  % limit outward rounding

% Z := arcsin(X), -1 =< X =<1, -pi/2=<Z=<pi/2
arcsin([Xl,Xh], [Zl,Zh]) :-
	Zl isL asin(Xl), Zh isH asin(Xh).  % asin is monotonic and increasing in range

% Z:= cos(X), 0=<X=<pi
cos([Xl,Xh],Z) :-
	Z1l isL cos(Xh), Z1h isH cos(Xl),
	^([Z1l,Z1h],[-1,1],Z).  % limit outward rounding

% Z := arccos(X), -1 =< X =<1, 0=<Z=<pi
arccos([Xl,Xh], [Zl,Zh]) :-
	Zl isL acos(Xh), Zh isH acos(Xl).  % acos is monotonic and decreasing in range


% Z:= tan(X) -pi/2=<X=<pi/2
tan([Xl,Xh], [Zl,Zh]) :-
	Zl isL tan(Xl), Zh isH tan(Xh).  % tan is monotonic and increasing in range

% Z := arctan(X)
arctan([Xl,Xh], [Zl,Zh]) :-
	Zl isL atan(Xl), Zh isH atan(Xh).  % atan is monotonic and increasing in range

%
% wrap repeating interval onto a prime cylinder of width W, return projected interval and "mulipliers" to re-project
%
wrap_([Xl,Xh], W, [MXl,MXh], [Xpl,Xph]) :-  % project onto cylinder from -W/2 to W/2, fails if interval wider than W.
	FMl isL Xl/W, FMh isL Xh/W,  % use same rounding at both ends so points always answer Yes
	catch((MXl is round(FMl), MXh is round(FMh)),_,fail),  % fail if unable to calculate MXl,MXh, e.g., due to infinite bound(s)
	MXh-MXl =< 1, Xh-Xl =< W,  % MX check first to avoid overflow
	Xpl isL Xl - (MXl*W), Xph isH Xh-(MXh*W).
	
%
% unwrap projected interval back to original range
%
unwrap_([Xpl,Xph], W, [MXl,MXh], [Xl,Xh]) :-
	Xl isL Xpl+W*MXl, Xh isH Xph+W*MXh.

% Z := ~X (boolean not)
~([B,B], [N,N]) :- !,
	N is (B+1) mod 2.
~([0,1], [0,1]).

%
%  set intersection (Can be []) and union.
intersection_(X,Y,Z) :- ^(X,Y,Z), !.
intersection_(X,Y,[]).

union_(X,[],X) :-!.
union_([],Y,Y) :-!.
union_([Xl,Xh],[Yl,Yh],[Zl,Zh]) :- Zl is min(Xl,Yl), Zh is max(Xh,Yh).

%
% interval is positive, negative, or split (contains 0)
%
intCase(p, [L,_]) :- L>=0,!.
intCase(n, [_,H]) :- H=<0,!.
intCase(s, I).

%
% abs(X) cases
%
absCase(p, X, X) :- !.
absCase(n, X, Z) :- -(X,Z), !.
absCase(s, [Xl,Xh], [0,Zh]) :- Zh is max(-Xl,Xh), !.

%
% Special case check for X/Y.
%      if Y is 0, X must contain 0
%
chkDiv([Yl,Yh],[Xl,Xh]) :-
	Yl =:= 0, Yh =:= 0, !, Xl =< 0, Xh >= 0.
chkDiv(_,_).  % Y non-zero

%
% * cases
%
multCase(p,p, [Xl,Xh], [Yl,Yh], [Zl,Zh]):- !, Zl isL Xl*Yl, Zh isH Xh*Yh.
multCase(p,n, [Xl,Xh], [Yl,Yh], [Zl,Zh]):- !, Zl isL Xh*Yl, Zh isH Xl*Yh.
multCase(p,s, [Xl,Xh], [Yl,Yh], [Zl,Zh]):- !, Zl isL Xh*Yl, Zh isH Xh*Yh.
multCase(n,p, [Xl,Xh], [Yl,Yh], [Zl,Zh]):- !, Zl isL Xl*Yh, Zh isH Xh*Yl.
multCase(n,n, [Xl,Xh], [Yl,Yh], [Zl,Zh]):- !, Zl isL Xh*Yh, Zh isH Xl*Yl.
multCase(n,s, [Xl,Xh], [Yl,Yh], [Zl,Zh]):- !, Zl isL Xl*Yh, Zh isH Xl*Yl.
multCase(s,p, [Xl,Xh], [Yl,Yh], [Zl,Zh]):- !, Zl isL Xl*Yh, Zh isH Xh*Yh.
multCase(s,n, [Xl,Xh], [Yl,Yh], [Zl,Zh]):- !, Zl isL Xh*Yl, Zh isH Xl*Yl.
multCase(s,s, [Xl,Xh], [Yl,Yh], [Zl,Zh]):-
	L1 isL Xl*Yh, L2 isL Xh*Yl,	Zl is min(L1,L2),
	H1 isH Xl*Yl, H2 isH Xh*Yh, Zh is max(H1,H2).


%
% / cases
%
odivCase(p,p, [Xl,Xh], [Yl,Yh], [Zl,Zh]):- !, odiv(lo,Xl,Yh,Zl,1),  odiv(hi,Xh,Yl,Zh,1).   % Zl isL Xl/Yh, Zh isH Xh/Yl.
odivCase(p,n, [Xl,Xh], [Yl,Yh], [Zl,Zh]):- !, odiv(lo,Xh,Yh,Zl,-1), odiv(hi,Xl,Yl,Zh,-1).  % Zl isL Xh/Yh, Zh isH Xl/Yl.
odivCase(p,s, X,       Y,       Z      ):- !, universal_interval(Z).
odivCase(n,p, [Xl,Xh], [Yl,Yh], [Zl,Zh]):- !, odiv(lo,Xl,Yl,Zl,1),  odiv(hi,Xh,Yh,Zh,1).   % Zl isL Xl/Yl, Zh isH Xh/Yh.
odivCase(n,n, [Xl,Xh], [Yl,Yh], [Zl,Zh]):- !, odiv(lo,Xh,Yl,Zl,-1), odiv(hi,Xl,Yh,Zh,-1).  % Zl isL Xh/Yl, Zh isH Xl/Yh.
odivCase(n,s, X,       Y,       Z      ):- !, universal_interval(Z).
odivCase(s,p, [Xl,Xh], [Yl,Yh], [Zl,Zh]):- !, odiv(lo,Xl,Yl,Zl,1),  odiv(hi,Xh,Yl,Zh,1).   % Zl isL Xl/Yl, Zh isH Xh/Yl.
odivCase(s,n, [Xl,Xh], [Yl,Yh], [Zl,Zh]):- !, odiv(lo,Xh,Yh,Zl,-1), odiv(hi,Xl,Yh,Zh,-1).  % Zl isL Xh/Yh, Zh isH Xl/Yh.
odivCase(s,s, X,       Y,       Z      ):-    universal_interval(Z).
	
% check for divide by zero, sign of inf resulting depends on sign of zero.
odiv(_,  X, Y, Z, Zsgn) :- Y =:= 0, !, Xsgn is sign(float(X)),odivInfinityVal(Zsgn,Xsgn,Z).
odiv(_,  X, Y, X, Zsgn) :- X =:= 0, !.
odiv(lo, X, Y, Z, _)  :- Z isL X/Y.
odiv(hi, X, Y, Z, _)  :- Z isH X/Y.

odivInfinityVal( 1,-1.0,-1.0Inf).
odivInfinityVal( 1, 0.0, 1.0Inf).
odivInfinityVal( 1, 1.0, 1.0Inf).
odivInfinityVal(-1, 1.0,-1.0Inf).
odivInfinityVal(-1, 0.0,-1.0Inf).
odivInfinityVal(-1,-1.0, 1.0Inf).


%
% integer power cases:  ipCase(Cx,Cn,Odd,N,X,Z) N<>0
%
ipCase(p,p,_,N, [Xl,Xh], [Zl,Zh]) :- ipowLo(Xl,N,Zl), ipowHi(Xh,N,Zh).                        % X pos, N pos,any
ipCase(p,n,_,N, [Xl,Xh], [Zl,Zh]) :- ipowLo(Xh,N,Zl), ipowHi(Xl,N,Zh).                        % X pos, N neg,any
ipCase(n,p,0,N, X,       [Zl,Zh]) :- -(X,[Xl,Xh]), ipowLo(Xl,N,Zl), ipowHi(Xh,N,Zh).                % X neg, N pos,even
ipCase(n,n,0,N, X,       [Zl,Zh]) :- -(X,[Xl,Xh]), ipowLo(Xh,N,Zl), ipowHi(Xl,N,Zh).                % X neg, N neg,even
ipCase(n,p,1,N, X,       Z)       :- -(X,[Xl,Xh]), ipowLo(Xl,N,Zl), ipowHi(Xh,N,Zh), -([Zl,Zh],Z).  % X neg, N pos,odd
ipCase(n,n,1,N, X,       Z)       :- -(X,[Xl,Xh]), ipowLo(Xh,N,Zl), ipowHi(Xl,N,Zh), -([Zl,Zh],Z).  % X neg, N neg,odd
ipCase(s,p,0,N, [Xl,Xh], [0,Zh])  :- Xmax is max(-Xl,Xh), ipowHi(Xmax,N,Zh).                        % X split, N pos,even
ipCase(s,p,1,N, [Xl,Xh], [Zl,Zh]) :- Xlp is -Xl, ipowHi(Xlp,N,Zlp), Zl is -Zlp, ipowHi(Xh,N,Zh).    % X split, N pos,odd
ipCase(s,n,0,N, X,       [0,1.0Inf]).                                                         % X split, N neg,even
ipCase(s,n,1,N, X,       [-1.0Inf,1.0Inf]).                                                   % X split, N neg,odd

ipowLo(X,N,X) :- X=:=0.  % avoid rounding at 0
ipowLo(X,N,Z) :- Z isL X**N.

ipowHi(X,N,X) :- X=:=0.  % avoid rounding at 0
ipowHi(X,N,Z) :- Z isH X**N.

%
% Nth root cases:  nthrootCase(Cx,Cn,Cz,Odd,N,X,Z), N<>0
%
nthrootCase(p,p,p,0, N, [Xl,Xh], _, [Zl,Zh]) :- nthRootLo(N,Xl,Zl), nthRootHi(N,Xh,Zh).      % X pos, N pos,even, Z pos
nthrootCase(p,p,n,0, N, [Xl,Xh], _, Z)       :- nthRootLo(N,Xl,Zl), nthRootHi(N,Xh,Zh), -([Zl,Zh],Z).  % X pos, N pos,even, Z neg
nthrootCase(p,p,s,0, N, [Xl,Xh], [Zl,Zh], NewZ) :-                                           % X pos, N pos,even, Z split
	                                            nthRootLo(N,Xl,Z1l),nthRootHi(N,Xh,Z1h),
	                                            -([Z1l,Z1h],[Z1nl,Z1nh]),
	                                            intersection_([Z1l,Z1h],[0,Zh],PosZ), intersection_([Z1nl,Z1nh],[Zl,0],NegZ),
	                                            union_(NegZ,PosZ,NewZ).

nthrootCase(p,p,_,1, N, [Xl,Xh], _, [Zl,Zh]) :- nthRootLo(N,Xl,Zl), nthRootHi(N,Xh,Zh).      % X pos, N pos,odd

nthrootCase(p,n,p,0, N, [Xl,Xh], _, [Zl,Zh]) :- nthRootLo(N,Xh,Zl), nthRootHi(N,Xl,Zh).      % X pos, N neg,even, Z pos
nthrootCase(p,n,n,0, N, [Xl,Xh], _, Z)       :- nthRootLo(N,Xh,Zl), nthRootHi(N,Xl,Zh), -([Zl,Zh],Z).  % X pos, N neg,even, Z neg
nthrootCase(p,n,s,0, N, [Xl,Xh], [Zl,Zh], NewZ) :-
	                                            nthRootLo(N,Xh,Z1l), nthRootHi(N,Xl,Z1h),    % X pos, N neg,even, Z split
	                                            -([Z1l,Z1h],[Z1nl,Z1nh]),
	                                            intersection_([Z1l,Z1h],[0,Zh],PosZ), intersection_([Z1nl,Z1nh],[Zl,0],NegZ),
	                                            union_(NegZ,PosZ,NewZ). % X pos, N pos,even, Z split

nthrootCase(p,n,_,1, N, [Xl,Xh], _, [Zl,Zh]) :- nthRootLo(N,Xh,Zl), nthRootHi(N,Xl,Zh).      % X pos, N neg,odd

% nthrootCase(n,_,_,0, N, X,      _, Z) :- fail.                                              % X neg, N even FAIL
nthrootCase(n,p,_,1, N, X,       _, Z)       :- -(X,[Xl,Xh]), nthRootLo(N,Xl,Zl), nthRootHi(N,Xh,Zh), -([Zl,Zh],Z).  % X neg, N pos,odd
nthrootCase(n,n,_,1, N, X,       _, Z)       :- -(X,[Xl,Xh]), nthRootLo(N,Xh,Zl), nthRootHi(N,Xl,Zh), -([Zl,Zh],Z).  % X neg, N neg,odd
% nthrootCase(s,_,_,0, N, X,      _, Z) :- fail.                                              % X split, N even FAIL
nthrootCase(s,p,_,1, N, [Xl,Xh], _, [Zl,Zh]) :- Xl1 is -Xl, nthRootHi(N,Xl1,Zl1), Zl is -Zl1, nthRootHi(N,Xh,Zh).    % X split, N pos,odd
nthrootCase(s,n,_,1, N, X,       _, [-1.0Inf,1.0Inf]).                                       % X split, N neg,odd

nthRootLo(N,X,Z) :- X =:= 0, !, ((N < 0 -> Z= -1.0Inf);Z=0).
nthRootLo(N,X,Z) :- integer(X), nth_integer_root_and_remainder(N,X,Z,0), !.  % try pure integer solution
nthRootLo(N,X,Z) :- Z1 isL log(X)/N, Z isL exp(Z1).  % round at each step (?? avoid second rounding)

nthRootHi(N,X,Z) :- X =:= 0, !, ((N < 0 -> Z=  1.0Inf);Z=0).
nthRootHi(N,X,Z) :- integer(X), nth_integer_root_and_remainder(N,X,Z,0), !.  % try pure integer solution
nthRootHi(N,X,Z) :- Z1 isH log(X)/N, Z isH exp(Z1).  % round at each step (?? avoid second rounding)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Relational Operations (narrowing operations)
%
:- discontiguous clpBNR:narrowing_op/4.

% integral(X) - convert float/rational bounds to integers (rounds inward)
narrowing_op(integral, _, [[Xl,Xh]], [[Il,Ih]]) :-
	(abs(Xl) =:= inf -> Il=Xl ; Il is ceiling(Xl)),  % SWIP ceiling and floor incorrect for infinities
	(abs(Xh) =:= inf -> Ih=Xh ; Ih is floor(Xh)).


% Z==(X==Y)  % (Z boolean)
narrowing_op(eq, _, [[1,1], X, Y], [[1,1], New, New]) :- !,  % Z is true, X and Y must intersect
	^(X,Y,New) .

narrowing_op(eq, p, [Z, X, Y], [NewZ, X, Y]) :-              % persistent, X and Y don't intersect, Z is false
	\+(^(X,Y,_)), !,
	^(Z, [0,0], NewZ).
	
narrowing_op(eq, _, [Z, X, Y], [NewZ, X, Y]) :-              % if X and Y are necessarily equal, Z is true
	necessEqual(X,Y), !,
	^(Z, [1,1], NewZ).

narrowing_op(eq, _, [Z,X,Y], [NewZ,X,Y]) :- ^(Z,[0,1],NewZ).   % else no change, but narrow Z to boolean


% Z==(X<>Y)  % (Z boolean, X,Y integer)
narrowing_op(ne, _, [[1,1], X, Y], [[1,1], NewX, NewY]) :-     % Z is true, try to narrow to not intersect
	<>(X,Y,NewX),
	<>(Y,NewX,NewY), !.

narrowing_op(ne, p, [Z, X, Y], [NewZ, X, Y]) :-                % persistent,  X and Y don't intersect, Z is true
	\+(^(X,Y,_)), !,
	^(Z, [1,1], NewZ).

narrowing_op(ne, _, [Z, X, Y], [NewZ, X, Y]) :-                % if X and Y are necessarily equal, Z is false
	necessEqual(X,Y), !,
	^(Z, [0,0], NewZ).

narrowing_op(ne, _, [Z,X,Y], [NewZ,X,Y]) :- ^(Z,[0,1],NewZ).   % else no change, but narrow Z to boolean


% Z==(X=<Y)  % (Z boolean)
narrowing_op(le, p, [Z, X, Y], [NewZ,X,Y]):-          % persistent case, set Z, X,Y unchanged
	le_disjoint_(X,Y,Z1), !,
	^(Z, Z1, NewZ).

narrowing_op(le, _, [[1,1], [Xl,Xh], [Yl,Yh]], [[1,1], [NXl,NXh], NewY]):-
	^([Xl,Xh], [-1.0Inf,Yh], [NXl,NXh]),     % NewX := [Xl,Xh] ^[NI,Yh]
	^([Yl,Yh], [NXl,1.0Inf], NewY),
	!.        % NewY := [Yl,Yh] ^[Xl,PI]

narrowing_op(le, P, [[0,0], X, Y], [[0,0], NewX, NewY]):-  % not le not closed, i.e., integer op
	narrowing_op(lt, P, [[1,1], Y, X], [[1,1], NewY, NewX]), !.

narrowing_op(le, _, [Z,X,Y], [NewZ,X,Y]) :- ^(Z,[0,1],NewZ).  % narrow Z to Bool if necessary

le_disjoint_([Xl,Xh], [Yl,Yh], [1,1]) :- Xh =< Yl.   % necessarily true
le_disjoint_([Xl,Xh], [Yl,Yh], [0,0]) :- Yh < Xl.    % necessarily false, only 1 point =


% Z==(X<Y)  % (Z boolean) generally unsound on reals but possibly useful for minima/maxima
narrowing_op(lt, p, [Z, X, Y], [NewZ, X, Y]):-              % persistent case, set Z, X,Y unchanged
	lt_disjoint_(X,Y,Z1), !,
	^(Z, Z1, NewZ).

narrowing_op(lt, _, [[1,1], [Xl,Xh], [Yl,Yh]], [[1,1], [NXl,NXh], NewY]):-
	Yh1 is float(Yh), YhD isL Yh1,            % if Z true, can possibly narrow X and Y
	^([Xl,Xh], [-1.0Inf,YhD], [NXl,NXh]),     % NewX := [Xl,Xh] ^[NI,YhD]
	Xl1 is float(NXl), XlD isH Xl1,
	^([Yl,Yh], [XlD,1.0Inf], NewY),
	!.

narrowing_op(lt, P, [[0,0], X, Y], [[0,0], NewX, NewY]):-  % if Z false, Y=<X must be true
	narrowing_op(le, P, [[1,1], Y, X], [[1,1], NewY, NewX]), !.

narrowing_op(lt, _, [Z,X,Y], [NewZ,X,Y]) :- ^(Z,[0,1],NewZ).  % else just narrow Z to Bool if necessary

lt_disjoint_([Xl,Xh], [Yl,Yh], [1,1]) :- Xh < Yl.   % necessarily true
lt_disjoint_([Xl,Xh], [Yl,Yh], [0,0]) :- Yh =< Xl.  % necessarily false, only 1 point =


% Z==(X<=Y)  % inclusion, constrains X to be subinterval of Y (Z boolean)
% Only two cases: either X and Y intersect or they don't.
narrowing_op(sub, _, [Z, X, Y], [NewZ, NewX, Y]):-
	^(X,Y,NewX), !,   % NewX is intersection of X and Y
	^(Z,[1,1],NewZ).

narrowing_op(sub, p, [[0,0], X, Y], [[0,0], NewX, Y]):-    % persistent, X and Y don't intersect'
	^(Z,[0,0],NewZ).


% Z==X+Y
narrowing_op(add, _, [Z, X, Y], [NewZ, NewX, NewY]):-
	+(X,Y,R1), ^(Z,R1,NewZ),   % NewZ := Z ^ (X+Y),
	-(NewZ,Y,R2), ^(X,R2,NewX),         %%% -(Z,Y,R2), ^(X,R2,NewX),   % NewX := X ^ (Z-Y),
	-(NewZ,NewX,R3), ^(Y,R3,NewY).      %%% -(Z,X,R3), ^(Y,R3,NewY).   % NewY := Y ^ (Z-X).


% Z==X*Y
narrowing_op(mul, _, [Z,X,Y], [NewZ, NewX, NewY]) :-
	*(X,Y,Z1), ^(Z,Z1,NewZ),
	intersect_odiv(X,Y,NewZ,NewY),
	intersect_odiv(NewY,X,NewZ,NewX).

% Y:= Y ^ Z/X  % used in mul relation
intersect_odiv([Xl,Xh],Y,[Zl,Zh],Y) :-
	% no narrowing of Y if 0 elementOf X^Z
	max(Xl, Zl) =< 0,
	min(Xh, Zh) >= 0,
	!.
intersect_odiv(X,Y,Z,NewY) :-
	/(Z,X,Y1), ^(Y,Y1,NewY).


% Z==min(X,Y)
narrowing_op(min, _, [[Zl,Zh],X,Y], New) :-
	min(X,Y,R), ^([Zl,Zh],R,Z1),          % Z1 := Z ^ min(X,Y),
	minimax(Z1, [Zl,1.0Inf], [Z,X,Y], New).


% Z==max(X,Y)
narrowing_op(max, _, [[Zl,Zh],X,Y], New) :-
	max(X,Y,R), ^([Zl,Zh],R,Z1),          % Z1 := Z ^ max(X,Y),
	minimax(Z1, [-1.0Inf,Zh], [Z,X,Y], New).
	
minimax(Z1, _, [Z,X,Y], [New, X, New]) :- % Case 1, X not in Z1
	\+(^(Z1,X,_)),!,                      % _ := Z1 \^ X,
	^(Y,Z1,New).                          % New := Y ^ Z1.

minimax(Z1, _, [Z,X,Y], [New, New, Y]) :- % Case 2, Y not in Z1
	\+(^(Z1,Y,_)),!,                         % _ := Z1 \^ Y,
	^(X,Z1,New).                          % New := X ^ Z1.

minimax(Z1, Zpartial, [Z,X,Y], [Z1, NewX, NewY]) :- % Case 3, overlap
	^(X,Zpartial,NewX),                   % NewX := X ^ Zpartial,
	^(Y,Zpartial,NewY).                   % NewY := Y ^ Zpartial.


% Z==abs(X)
narrowing_op(abs, _, [Z,X], [NewZ, NewX]) :-
	abs(X,Z1), ^(Z,Z1,NewZ),
	-(NewZ,NegZ),
	intersection_(NegZ,X,NegX),
	intersection_(NewZ,X,PosX),
	union_(NegX,PosX,NewX).

% Z== -X
narrowing_op(minus, _, [Z,X], [NewZ, NewX]) :-
	-(X,NegX), ^(Z,NegX,NewZ),            % NewZ := Z ^ -X
	-(NewZ,NegZ), ^(X,NegZ,NewX).         % NewX := X ^ -Z


% Z== exp(X)
narrowing_op(exp, _, [Z,X], [NewZ, NewX]) :-
	exp(X,X1), ^(Z,X1,NewZ),              % NewZ := Z ^ exp(X)
	log(NewZ,Z1), ^(X,Z1,NewX).              %%% log(Z,Z1), ^(X,Z1,NewX).              % NewX := X ^ log(X)


% Z== X**Y
narrowing_op(pow, _, [Z,X,[Yl,Yh]], New) :-  % exponent is zero
	Yl=:=0, Yh=:=0, !,
	New = [[1,1], X, [Yl,Yh]].
narrowing_op(pow, _, [Z,X,[N,N]], [NewZ, NewX, [N,N]]) :-    % exponent is an integer <>0
	integer(N), !,
	intpow(X,[N,N],Z1), ^(Z,Z1,NewZ),
	nthroot(NewZ,[N,N],X,X1), ^(X,X1,NewX).
narrowing_op(pow, _, [Z,[Xl,Xh],Y], [NewZ, NewX, NewY]) :-              % lots of rounding for this operation
	^([0,Xh], [Xl,Xh], Xn),  % X must be positive (>=0)
	log(Xn,LogXn), *(LogXn,Y,LogZ1), exp(LogZ1,Z1), ^(Z,Z1,NewZ),       % Z:=X**Y
	log(NewZ,LogZ), /(LogZ,Y,LogX1), exp(LogX1,X1), ^(Xn,X1,NewX),      % X:=Z**(1/Y)
	log(NewX,LogX), /(LogZ,LogX,Y1), (^(Y,Y1,NewY) -> true ; NewY=Y).   % Y:=log(Z)/log(X)


% Z== sin(X)
narrowing_op(sin, _, [Z,X], [NewZ, NewX]) :-
	wrap_(X,2*pi,MX,Xp), !,       % fails if X too wide
	sin_(MX,Xp,Z,NMX,X1,NewZ),
	unwrap_(X1,2*pi,NMX,X2),      % project back to original cylinder
	^(X,X2,NewX).

narrowing_op(sin, _, [Z,X], [NewZ,X]) :- % no narrowing possible, just constrain Z
	^(Z,[-1,1],NewZ).

sin_([MX,MX], X, Z, [MX,MX], NewX, NewZ) :-
	!,             % same cylinder, split into 3 interval convex sectors
	Pi is pi, PiBy2 is pi/2, NPiBy2 is -PiBy2, NPi is -pi,  % boundaries
	sin_sector_(lo,  NPi, NPiBy2,   X, Z, NXlo,  NZlo),
	sin_sector_(mid, NPiBy2, PiBy2, X, Z, NXmid, NZmid),
	sin_sector_(hi,  PiBy2, Pi,     X, Z, NXhi,  NZhi),
	union3_(NXlo,NXmid,NXhi, NewX),  % fails if result empty
	union3_(NZlo,NZmid,NZhi, NewZ).

sin_([MXl,MXh], [Xl,Xh], Z, [NMXl,NMXh], NewX, NewZ) :-
	% adjacent cylinders,
	Pi is pi, MPi is -pi,
	try_sin_([Xl,Pi], Z, NX1, NZ1,MXl,MXh,NMXl),
	try_sin_([MPi,Xh],Z, NX2, NZ2,MXh,MXl,NMXh),
	union_(NZ1,NZ2,NewZ),                % fails if both empty
	union_(NX1,NX2,NewX).

try_sin_(X,Z,NewX,NewZ,MXS,MXF,MXS) :- sin_([MXS,MXS], X, Z, _, NewX, NewZ),!.
try_sin_(X,Z,[],[],MXS,MXF,MXF).  % if sin_ fails, return empty X interval for union

sin_sector_(lo,Lo,Hi, X,Z,[NXl,NXh],NewZ) :-  % Lo is -pi, Hi is -pi/2, 
	^(X,[Lo,Hi],[X1l,X1h]), !,
	X2l isL Lo-X1h, X2h isH Lo-X1l,    % flip to mid range (rounding?)
	sin_prim_([X2l,X2h],Z,[Xpl,Xph],NewZ),
	NXl isH Lo-Xph, NXh isL Lo-Xpl.    % flip back and round outwards

sin_sector_(hi,Lo,Hi, X,Z,[NXl,NXh],NewZ) :-  % Lo is pi/2, Hi is pi, 
	^(X,[Lo,Hi],[X1l,X1h]), !,
	X2l isL Hi-X1h, X2h isH Hi-X1l,    % flip to mid range (rounding?)
	sin_prim_([X2l,X2h],Z,[Xpl,Xph],NewZ),
	NXl isH Hi-Xph, NXh isL Hi-Xpl.    % flip back and round outwards
	
sin_sector_(mid,Lo,Hi, X,Z,NewX,NewZ) :-      % Lo is -pi/2, Hi is pi/2, 
	^(X,[Lo,Hi],X1), !,
	sin_prim_(X1,Z,NewX,NewZ).
	
sin_sector_(_Any,_Lo,_Hi,_X,_Z,[],[]).
	
sin_prim_(X,Z,NewX,NewZ) :-
	sin(X,Z1), ^(Z,Z1,NewZ),
	arcsin(NewZ,X1), ^(X,X1,NewX).

union3_([],[],[], U) :- !, fail.
union3_([],X2,X3, U) :- !, union_(X2,X3,U).
union3_(X1,[],X3, U) :- !, union_(X1,X3,U).
union3_(X1,X2,X3, U) :- union_(X1,X2,U1),union_(U1,X3,U).


% Z== cos(X)
narrowing_op(cos, _, [Z,X], [NewZ, NewX]) :-
	wrap_(X,2*pi,MX,Xp), !,       % fails if X too wide
	cos_(MX,Xp,Z,NMX,X1,NewZ),
	unwrap_(X1,2*pi,NMX,X2),      % project back to original cylinder
	^(X,X2,NewX).

narrowing_op(cos, _, [Z,X], [NewZ,X]) :- % no narrowing possible, just constrain Z
	^(Z,[-1,1],NewZ).

cos_([MX,MX], X, Z, [MX,MX], NewX, NewZ) :-
	!,             % same cylinder, split into 2 interval convex sectors
	Pi is pi, NPi is -pi,  % boundaries
	cos_sector_(neg, NPi, 0, X, Z, NXneg, NZneg),
	cos_sector_(pos, 0, Pi,  X, Z, NXpos, NZpos),
	union_(NZneg,NZpos,NewZ),             % fails if both empty
	union_(NXneg,NXpos,NewX).

cos_([MXl,MXh], [Xl,Xh], Z, [NMXl,NMXh], NewX, NewZ) :-
	% adjacent cylinders,
	Pi is pi, MPi is -pi,
	try_cos_([Xl,Pi], Z, NX1, NZ1,MXl,MXh,NMXl),
	try_cos_([MPi,Xh],Z, NX2, NZ2,MXh,MXl,NMXh),
	union_(NZ1,NZ2,NewZ),                % fails if both empty
	union_(NX1,NX2,NewX).

try_cos_(X,Z,NewX,NewZ,MXS,MXF,MXS) :- cos_([MXS,MXS], X, Z, _, NewX, NewZ),!.
try_cos_(X,Z,[],[],MXS,MXF,MXF).  % if cos_ fails, return empty X interval for union

cos_sector_(neg,Lo,Hi, X,Z,NewX,NewZ) :-      % Lo is 0, Hi is pi, 
	^(X,[Lo,Hi],X1), !,
	-(X1,X2),    % flip X to positive range
	cos_prim_(X2,Z,X3,NewZ),
	-(X3,NewX).  % and flip back

cos_sector_(pos,Lo,Hi, X,Z,NewX,NewZ) :-      % Lo is 0, Hi is pi, 
	^(X,[Lo,Hi],X1), !,
	cos_prim_(X1,Z,NewX,NewZ).

cos_sector_(_Any,_Lo,_Hi,_X,_Z,[],[]).
	
cos_prim_(X,Z,NewX,NewZ) :-
	cos(X,Z1), ^(Z,Z1,NewZ),
	arccos(NewZ,X1), ^(X,X1,NewX).

% Z== tan(X)
narrowing_op(tan, _, [Z,X], [NewZ, NewX]) :-
	wrap_(X,pi,MX,Xp), !,     % fails if X too wide
	tan_(MX,Xp,Z,NMX,X1,NewZ),
	unwrap_(X1,pi,NMX,X2),    % project back to original cylinder
	^(X,X2,NewX).

narrowing_op(tan, _, ZX, ZX).      % no narrowing possible, e.g., not same or adjacent cylinder.

tan_([MX,MX], X, Z, [MX,MX], NewX, NewZ) :-
	!,             % same cylinder
	tan(X,Z1),     % monotonic, increasing
	^(Z,Z1,NewZ),  %^(Z,[Z1l,Z1h],NewZ),
	arctan(NewZ, NewX).
	
tan_([MXl,MXh], [Xl,Xh], Z, [NMXl,NMXh], NewX, NewZ) :-
%	MXl is MXh-1,  % adjacent cylinders
	PiBy2 is pi/2, MPiBy2 is -PiBy2,
	try_tan_([Xl,PiBy2],  Z, NX1, NZ1,MXl,MXh,NMXl),
	try_tan_([MPiBy2,Xh], Z, NX2, NZ2,MXh,MXl,NMXh),
	union_(NZ1,NZ2,NewZ),             % fails if both empty
	union_(NX1,NX2,NewX).
	
try_tan_(X,Z,NewX,NewZ,MXS,MXF,MXS) :- tan_([MXS,MXS], X, Z, _, NewX, NewZ),!.
try_tan_(X,Z,[],[],MXS,MXF,MXF).  % if tan_ fails, return empty X interval for union


% Z== ~X boolean negation (Z and X boolean)
narrowing_op(not, _, [Z,X], [NewZ, NewX]) :-
	booleanVal_(Z,ZB), booleanVal_(X,XB),
	~(Z,X1), ^(X,X1,NewX),
	~(NewX,Z1), ^(Z,Z1,NewZ).


% Z==X and Y  boolean 'and'
narrowing_op(and, _, [Z,X,Y], [NewZ, NewX, NewY]) :-
	booleanVal_(Z,ZB), booleanVal_(X,XB), booleanVal_(Y,YB),
	andB_rel_(ZB,XB,YB, NewZ, NewX, NewY),!.
	
andB_rel_(Z,[1,1],[1,1], NewZ,[1,1],[1,1]) :- !, ^(Z,[1,1],NewZ).
andB_rel_(Z,[0,0],Y,     NewZ,[0,0],Y)     :- !, ^(Z,[0,0],NewZ).
andB_rel_(Z,X,[0,0],     NewZ,X,[0,0])     :- !, ^(Z,[0,0],NewZ).
andB_rel_([1,1],X,Y,     [1,1],NewX,NewY)  :- !, ^(X,[1,1],NewX), ^(Y,[1,1],NewY).
andB_rel_([0,0],X,[1,1], [0,0],NewX,[1,1]) :- !, ^(X,[0,0],NewX).
andB_rel_([0,0],[1,1],Y, [0,0],[1,1],NewY) :- !, ^(Y,[0,0],NewY).
andB_rel_(Z,X,Y,         Z,X,Y).  % still indeterminate


% Z==X and Y  boolean 'nand'
narrowing_op(nand, _, [Z,X,Y], [NewZ, NewX, NewY]) :-
	booleanVal_(Z,ZB), booleanVal_(X,XB), booleanVal_(Y,YB),
	nandB_rel_(ZB,XB,YB, NewZ, NewX, NewY),!.
	
nandB_rel_(Z,[1,1],[1,1], NewZ,[1,1],[1,1]) :- !, ^(Z,[0,0],NewZ).
nandB_rel_(Z,[0,0],Y,     NewZ,[0,0],Y)     :- !, ^(Z,[1,1],NewZ).
nandB_rel_(Z,X,[0,0],     NewZ,X,[0,0])     :- !, ^(Z,[1,1],NewZ).
nandB_rel_([0,0],X,Y,     [0,0],NewX,NewY)  :- !, ^(X,[1,1],NewX), ^(Y,[1,1],NewY).
nandB_rel_([1,1],X,[1,1], [1,1],NewX,[1,1]) :- !, ^(X,[0,0],NewX).
nandB_rel_([1,1],[1,1],Y, [1,1],[1,1],NewY) :- !, ^(Y,[0,0],NewY).
nandB_rel_(Z,X,Y,         Z,X,Y).  % still indeterminate


% Z==X or Y  boolean 'or'
narrowing_op(or, _, [Z,X,Y], [NewZ, NewX, NewY]) :-
	booleanVal_(Z,ZB), booleanVal_(X,XB), booleanVal_(Y,YB),
	orB_rel_(ZB,XB,YB, NewZ, NewX, NewY),!.
	
orB_rel_(Z,[0,0],[0,0], NewZ,[0,0],[0,0]) :- !, ^(Z,[0,0],NewZ).
orB_rel_(Z,[1,1],Y,     NewZ,[1,1],Y)     :- !, ^(Z,[1,1],NewZ).
orB_rel_(Z,X,[1,1],     NewZ,X,[1,1])     :- !, ^(Z,[1,1],NewZ).
orB_rel_([0,0],X,Y,     [0,0],NewX,NewY)  :- !, ^(X,[0,0],NewX), ^(Y,[0,0],NewY).
orB_rel_([1,1],X,[0,0], [1,1],NewX,[0,0]) :- !, ^(X,[1,1],NewX).
orB_rel_([1,1],[0,0],Y, [1,1],[0,0],NewY) :- !, ^(Y,[1,1],NewY).
orB_rel_(Z,X,Y,         Z,X,Y).  % still indeterminate


% Z==X nor Y  boolean 'nor'
narrowing_op(nor, _, [Z,X,Y], [NewZ, NewX, NewY]) :-
	booleanVal_(Z,ZB), booleanVal_(X,XB), booleanVal_(Y,YB),
	norB_rel_(ZB,XB,YB, NewZ, NewX, NewY),!.
	
norB_rel_(Z,[0,0],[0,0], NewZ,[0,0],[0,0]) :- !, ^(Z,[1,1],NewZ).
norB_rel_(Z,[1,1],Y,     NewZ,[1,1],Y)     :- !, ^(Z,[0,0],NewZ).
norB_rel_(Z,X,[1,1],     NewZ,X,[1,1])     :- !, ^(Z,[0,0],NewZ).
norB_rel_([1,1],X,Y,     [1,1],NewX,NewY)  :- !, ^(X,[0,0],NewX), ^(Y,[0,0],NewY).
norB_rel_([0,0],X,[0,0], [0,0],NewX,[0,0]) :- !, ^(X,[1,1],NewX).
norB_rel_([0,0],[0,0],Y, [0,0],[0,0],NewY) :- !, ^(Y,[1,1],NewY).
norB_rel_(Z,X,Y,         Z,X,Y).  % still indeterminate


% Z==X xor Y  boolean 'xor'
narrowing_op(xor, _, [Z,X,Y], [NewZ, NewX, NewY]) :-
	booleanVal_(Z,ZB), booleanVal_(X,XB), booleanVal_(Y,YB),
	xorB_rel_(ZB,XB,YB, NewZ, NewX, NewY).
	
xorB_rel_(Z,[B,B],[B,B], NewZ,[B,B],[B,B]) :- !, ^(Z,[0,0],NewZ).
xorB_rel_(Z,[X,X],[Y,Y], NewZ,[X,X],[Y,Y]) :- !, ^(Z,[1,1],NewZ).
xorB_rel_([B,B],X,[B,B], [B,B],NewX,[B,B]) :- !, ^(X,[0,0],NewX).
xorB_rel_([Z,Z],X,[Y,Y], [Z,Z],NewX,[Y,Y]) :- !, ^(X,[1,1],NewX).
xorB_rel_([B,B],[B,B],Y, [B,B],[B,B],NewY) :- !, ^(Y,[0,0],NewY).
xorB_rel_([Z,Z],[X,X],Y, [Z,Z],[X,X],NewY) :- !, ^(Y,[1,1],NewY).
xorB_rel_(Z,X,Y,         Z,X,Y).  % still indeterminate


% Z==X -> Y  boolean 'implies'
narrowing_op(imB, _, [Z,X,Y], [NewZ, NewX, NewY]) :-
	booleanVal_(Z,ZB), booleanVal_(X,XB), booleanVal_(Y,YB),
	imB_rel_(ZB,XB,YB, NewZ, NewX, NewY),!.
	
imB_rel_(Z,[B,B],[B,B], NewZ,[B,B],[B,B]) :- !, ^(Z,[1,1],NewZ).
imB_rel_(Z,[X,X],[Y,Y], NewZ,[X,X],[Y,Y]) :- !, ^(Z,[Y,Y],NewZ).
imB_rel_([B,B],[1,1],Y, [B,B],[1,1],NewY) :- !, ^(Y,[B,B],NewY).
imB_rel_([1,1],[0,0],Y, [1,1],[0,0],NewY) :- !, ^(Y,[0,1],NewY).
imB_rel_([B,B],X,[0,0], [B,B],NewX,[0,0]) :- !, N is B+1 mod 2,^(X,[N,N],NewX).
imB_rel_([1,1],X,[1,1], [1,1],NewX,[1,1]) :- !, ^(X,[0,1],NewX).
imB_rel_(Z,X,Y,         Z,X,Y).  % still indeterminate


% two point intervals are necessarily equal if bounds are arithmetically equivalent.
necessEqual([X,X],[Y,Y]) :- X =:= Y.

% optimize if already boolean, forces all intervals to boolean range
booleanVal_([0,0],[0,0]).
booleanVal_([1,1],[1,1]).
booleanVal_([0,1],[0,1]).
booleanVal_(V,[0,1]):- ^(V,[0,1],[0,1]).   % constrain non-booleans to [0,1]

%
% Intervals are constrained (attributed) variables.
%
% Current interval bounds updates via setarg(Val) which is backtrackable
%

interval_object(Int, Type, Val, Nodelist) :-
	get_attr(Int, clpBNR, interval(Type, Val, Nodelist)).       %%SWIP

% get current value
getValue(Num, Val) :-
	number(Num), !,         % floats and integers
	Val=[Num,Num].
getValue(Int, Val) :-       % an interval, get value from attribute
	get_attr(Int, clpBNR, interval(_, Val, _)), !.     %% optimized for SWIP
getValue(Num, [Num,Num]) :-
	rational(Num).          % rationals (rarest case) 

% set current value (assumes bounds check has already been done)
putValue_(Val, Int, Nodelist) :-      % update bounds and return node list
	get_attr(Int, clpBNR, Def),       %%SWIP
	setarg(2,Def,Val),                % write new value, undone on backtracking
	arg(3,Def,Nodelist).              %% Def = interval(_Type, _Prev, Nodelist)

%
% Test for interval:
%
%
%  interval(X)  - filter
%
interval(X) :- interval_object(X,_,_,_).

%
% SWIP hooks (ignores the constraint network, i.e., node lists)
%
attribute_goals(X) -->
	{
	 interval_object(X, Type, Val, _Nodelist),
	 interval_domain_(Type, Val, Dom)
	},
	[X::Dom].

attr_portray_hook(interval(T,Val,NL),_Int) :-
	interval_domain_(T,Val,Dom),
	write(Dom).

interval_domain_(integer,[0,1],boolean) :- !.  % integer(0,1) is synonomous with boolean
interval_domain_(T,[L,H],Dom) :-
	interval_bound_(L,LB),
	interval_bound_(H,HB),
	Dom=..[T,LB,HB].

interval_bound_(B,B)   :- number(B),!.
interval_bound_(R,M/N) :- rational(R,M,N). % SWIP - may change if rational fraction ever becomes a number
%%%%

%
%  range(Int, Bounds) for compatability 
%
% for interval(Int) and numeric(Int), check if value is (always) in specified range, unifying any vars with current value
range(Int, [L,H]) :- getValue(Int, [IL,IH]), !,  % existing interval
	(var(L) -> L=IL ; L=<IL),  % range check, no narrowing
	(var(H) -> H=IH ; IH=<H).
% for var(Int), constrain it to be an interval with specified bounds (like a declaration)
range(Int, [L,H]) :- var(Int),  % new interval
	int_decl_(real, [L,H], Int),
	getValue(Int, [L,H]).       % will bind any intput var's to values

%
%  domain(Int, Dom) for interval(Int) for compatability 
%
domain(Int, Dom) :- 
	interval_object(Int, Type, Val, _),
	interval_domain_(Type, Val, Dom).

%
% Interval declarations
%
Ints::Dom :- is_list(Ints),!,
	intervals_(Ints,Dom).
	
R::Dom :- var(R), var(Dom), !,  % declare R = real(L,H), Note: R can be interval 
	int_decl_(real,[L,H],R),
	domain(R,Dom).

R::Dom :-  var(Dom), !,         % domain query (if interval(R) else fail)
	domain(R,Dom). % "domain" query, unify interval Type and Bounds

R::Dom :-                       % interval(R) or numeric(R) and nonvar(Dom) 
	Dom=..[Type|Bounds],
	int_decl_(Type,Bounds,R).

int_decl_(boolean,_,R) :- !,                % boolean is integer; 0=false, 1=true, ignore any bounds.
	int_decl_(integer,[0,1],R).
	
int_decl_(Type,[L,H],R) :- interval_object(R,IType,Current,_NL), !,  % already interval
	lower_bound_val_(Type,L,IL),  % changing type,bounds?
	upper_bound_val_(Type,H,IH),
	applyType_(Type, IType, R, T/T, Agenda),              % coerce reals to integers (or no-op).
	^(Current,[IL,IH],New),       % low level functional primitive
	updateValue_(Current, New, R, 1, Agenda, NewAgenda),  % update value
	stable_(NewAgenda).           % then execute Agenda

int_decl_(Type,[L,H],R) :- var(R), !,        % new interval (R can't be existing interval)
	lower_bound_val_(Type,L,IL),
	upper_bound_val_(Type,H,IH),
	IL=<IH,           % valid range
	(IL=IH -> R=IL ;  % point range, can unify now
		(put_attr(R, clpBNR, interval(Type, [IL,IH], _NL)),  % attach clpBNR attribute
		 constrainInteger_(Type,R,_)         % creation, so no need to stabilize constraint network
		)
	).

int_decl_(Type,[L,H],R) :- (Type=integer -> integer(R) ; numeric(R)), !,    % R already a point value, check range
	lower_bound_val_(Type,L,IL), IL=<R,
	upper_bound_val_(Type,H,IH), R=<IH.

int_decl_(Type,[],R) :- !,                   % no bounds, fill with vars
	int_decl_(Type,[L,H],R).

intervals_([],_Def).
intervals_([Int|Ints],Def) :-
	Int::Def, !,
	intervals_(Ints,Def).

lower_bound_val_(Type,L,IL) :- var(L), !,  % unspecified bound, make it finite
	finite_interval(Type,[IL,IH]).
lower_bound_val_(real,M/N,IL) :- integer(M), integer(N), !,   % fraction, convert to rational
	IL is M rdiv N.
lower_bound_val_(real,L,IL) :-             % real: evaluate and round outward (if float)
	IL isL L.
lower_bound_val_(integer,L,IL) :-          % integer: evaluate, fail if infinite else make integer
	catch(V is L,_,fail),                  % any evaluation error is failure
	%abs(V)=\=1.0Inf, IL is ceiling(V).
	(abs(V) =:= inf -> IL=V ; IL is ceiling(V)).  % SWIP calculation of ceiling(inf) incorrect

upper_bound_val_(Type,H,IH) :- var(H), !,  % unspecified bound, make it finite
	finite_interval(Type,[IL,IH]).
upper_bound_val_(real,M/N,IH) :- integer(M), integer(N), !,   % fraction, convert to rational
	IH is M rdiv N, !.
upper_bound_val_(real,H,IH) :-             % real: evaluate and round outward (if float)
	IH isH H.
upper_bound_val_(integer,H,IH) :-          % integer: evaluate, fail if infinite else make integer
	catch(V is H,_,fail),                  % any evaluation error is failure
	%abs(V)=\=1.0Inf, IH is floor(V).
	(abs(V) =:= inf -> IH=V ; IH is floor(V)).  % SWIP calculation of floor(inf) incorrect

applyType_(boolean, real, Int, Agenda, NewAgenda) :- !,     % narrow real to boolean
	applyType_(integer, real, Int, Agenda, NewAgenda).
applyType_(integer, real, Int, Agenda, NewAgenda) :- !,     % narrow real to integer
	get_attr(Int, clpBNR, Def),   %% SWIP
	setarg(1,Def,integer),               % set Type (only case allowed)
	constrainInteger_(integer, Int, Nodes),  % add integral constraint
	linkNodeList_(Nodes, Agenda, NewAgenda).
applyType_(Type,IType,Int, Agenda, Agenda).                       % anything else: no change

constrainInteger_(integer,R,[Node]) :- !, Node=node(integral,P,L,R), addNode_([R],Node).
constrainInteger_(_,_,[]).

%
% this goal gets triggered whenever an interval is unified, valid for a numeric value or another interval
%
attr_unify_hook(interval(Type,[L,H],Nodelist), V) :-     % unify an interval with a numeric
	(Type=integer -> integer(V) ; numeric(V)), !,        % check that V is consistent with Type
	L=<V, V=<H,              % in range
	linkNodeList_(Nodelist, T/T, Agenda),
	stable_(Agenda).         % broadcast change

attr_unify_hook(interval(Type1,V1,Nodelist1), Int) :-    % unifying two intervals
	get_attr(Int, clpBNR, Def),         %%SWIP Def = interval(Type, Val, Nodelist)
	Def = interval(Type2, V2, Nodelist2),  % fails on Type mismatch,
	mergeType_(Type1, Type2, NewType),  % unified Type=integer if either is an integer
	^(V1,V2,V),                         % unified range is intersection (from ia_primitives),
	mergeNodes_(Nodelist2,Nodelist1,Newlist),  % unified node list is a merge of two lists
	setarg(1,Def,NewType),              % update new type, value and constraint list, undone on backtracking
	setarg(2,Def,V),
	setarg(3,Def,Newlist),
	linkNodeList_(Newlist, T/T, Agenda),
	stable_(Agenda).         % broadcast change

mergeType_(real, real, real) :- !.
mergeType_(_,    _,    integer).

mergeNodes_([N],NodeList,NodeList) :- var(N),!.
mergeNodes_([N|Ns],NodeList,[N|NewList]) :-
	N=..[node,Op,_,_|Ops],
	notIn_(NodeList,Op,Ops), !,  % test for equivalent node already in NodeList
	mergeNodes_(Ns,NodeList,NewList).
mergeNodes_([N|Ns],NodeList,NewList) :-
	mergeNodes_(Ns,NodeList,NewList).

notIn_([N|Ns],Op,Ops) :-  % equivalent node(Op, _, _|Ops) ==> failure 
	nonvar(N),  % avoids exception in =../2
	N=..[node,Op,_,_|NOps],
	NOps==Ops,  % avoid unification of operands
	!, fail.
notIn_([N|Ns],Op,Ops) :-  % keep searching
	nonvar(N), !,
	notIn_(Ns,Op,Ops).
notIn_(_,_,_).            % end of search

%
% New Constraints use { ... } syntax.
%
{}.
{Cons} :-
	addConstraints_(Cons,T/T,Agenda),         % add constraints
%	traceNew_(Cons),
	stable_(Agenda).                          % then execute Agenda

addConstraints_((C1,C2),Agenda,NewAgenda) :-  % Note: comma as operator
	!,
	constraint_(C1),   % a constraint is a boolean expression that evaluates to true
	simplify(C1,CS1),  % optional
	build_(CS1, 1, boolean, Agenda, NextAgenda),
	addConstraints_(C2,NextAgenda,NewAgenda).
addConstraints_(C,Agenda,NewAgenda) :-
	constraint_(C),    % a constraint is a boolean expression that evaluates to true
	simplify(C,CS),    % optional
	build_(CS, 1, boolean, Agenda, NewAgenda).

%%%%:- include(ia_simplify).  % simplifies constraints to a hopefully more efficient equivalent
%
% Expression variables are Prolog var's; numeric constants are precise.
% Note floats are treated like variables and no arithmetic is performed on them
%
constant_(C) :- rational(C).  % (integers or rationals)

% works for print and listener but may be misleading
% user:portray(M rdiv N) :- print(M/N).

% used for sorting expressions and terms.
sort_exp_(List, Sorted) :- sort(0, @=<, List, Sorted).

% negatable operators
negate_op_(+,-).
negate_op_(-,+).

% power operators
invert_op_(*,/).
invert_op_(/,*).

% signed multiplier and power values
sign_val_(+,C,C) :- C>=0.
sign_val_(-,C,N) :- N is -C.

pwr_val_(*,C,C) :- C>=0.
pwr_val_(/,C,N) :- N is -C.

equality_op_(==).
equality_op_(<>).
equality_op_(=<).
equality_op_(>=).
equality_op_(<).
equality_op_(>).

% utility to distribute A*(B1+B2) if they have variables in common or A is a constant
distribute_(C,B,Exp) :-
	constant_(C), !,
	negate_op_(AddOp,_), B=..[AddOp,B1,B2],  % watch out for vars
	DExp=..[AddOp,C*B1,C*B2],
	simplify(DExp,Exp).
distribute_(A,B,Exp) :-
	negate_op_(AddOp,_), B=..[AddOp,B1,B2],  % watch out for vars
	shared_vars_(A,B),  % any shared vars
	!,
	DExp=..[AddOp,A*B1,A*B2],
	simplify(DExp,Exp).

% utility for (in)equality reduction 
normalize_(A,B,Op,ROp,Exp) :-
	rational(B,0,_), !,           % RHS = 0
	n_build_(Op, A, 0, Exp).
normalize_(A,B,Op,ROp,Exp) :-
	rational(A,0,_), !,           % LHS = 0
	n_build_(ROp, B, 0, Exp).
normalize_(A,B,Op,ROp,Exp) :-
	occurs_in_(A,B), !,           % RHS is shared var
	n_build_(Op, A-B, 0, Exp).
normalize_(A,B,Op,ROp,Exp) :-
	occurs_in_(B,A), !,           % LHS is shared var
	n_build_(ROp, B-A, 0, Exp).
normalize_(A,B,Op,ROp,Exp) :-
	compound(A), compound(B),     % LHS and RHS are expressions with shared vars
	shared_vars_(A,B), !,
	n_build_(Op, A-B, 0, Exp).
normalize_(A,B,Op,ROp,Exp) :-     % everything else, leave LHS and RHS alone
	simplify(B,RHS),
	n_build_(Op, A, RHS, Exp).

occurs_in_(Exp, V) :- var(V), term_variables(Exp,Vs), shared_var_(Vs,V).

n_build_(Op, L, RHS, Exp) :- simplify(L,LHS), Exp=..[Op,LHS,RHS].

shared_vars_(A,B) :-
	term_variables(A,AVs),
	term_variables(B,BVs),
	shared_vars_in_(AVs,BVs).

shared_vars_in_([AV|_AVs],BVs) :-
	shared_var_(BVs,AV), !.
shared_vars_in_([_AV|AVs],BVs) :-
	shared_vars_in_(AVs,BVs).

shared_var_([BV|_BVs],AV) :-
	AV == BV, !.
shared_var_([_BV|BVs],AV) :-
	shared_var_(BVs,AV).


%
% simplify/2
%
simplify(A,A) :- var(A),!.

simplify(C,C) :- rational(C),!.  % includes integers

% possible distribute
simplify(A*B,Exp) :-
	compound(B),
	distribute_(A,B,Exp), !.
simplify(A*B,Exp) :-
	compound(A),
	distribute_(B,A,Exp), !.

% simplify equalities and inequalities
simplify(A==B,Exp) :-
	normalize_(A,B,==,==,Exp), !.

simplify(A=<B,Exp) :-
	normalize_(A,B,=<,>=,Exp), !.

simplify(A>=B,Exp) :-
	normalize_(A,B,>=,=<,Exp), !.

simplify(A<B,Exp) :-
	normalize_(A,B,<,>,Exp), !.

simplify(A>B,Exp) :-
	normalize_(A,B,>,<,Exp), !.

% simplify "cascaded" divisions
simplify(A/B,Exp) :- 
	compound(B), B=Bn/Bd, !,
	simplify(A*Bd/Bn,Exp).

%
% General purpose simplify
%
simplify(E,Exp) :-
	collect_exp_(E, L/L, Es/[]),  % collect terms in a difference list
	collect_exp_items(Es,Is),     % collect like terms
	reduce_exp_items_(Is,Exp),    % and reduce back to expression
	!.
	
collect_exp_(A, List/[term(+,A,1)|NewT], List/NewT) :-
	var(A), !.
	
collect_exp_(C, List/[C|NewT], List/NewT) :-
	rational(C), !.

collect_exp_(A, List/[term(Op,F,1)|NewT], List/NewT) :-    % floats as terms, can collect but not do arithmetic
	float(A), !,
	(A<0 -> Op = - ; Op = +),
	F is abs(A).

collect_exp_(N*A, List/[Term|NewT], List/NewT) :-  % user written terms
	mul_term_(N,A,Term), !.

collect_exp_(A*N, List/[Term|NewT], List/NewT) :-  % user written terms
	mul_term_(N,A,Term), !.

collect_exp_(-A,List/T, List/NewT) :-
	simplify(A,AT), collect_exp_(AT,P/P,ListA),
	negate_exp_(ListA,T/NewT).

collect_exp_(A-B,List,NewList) :-
	simplify(A,AT), collect_exp_(AT,List,ListA),
	collect_exp_(-B,ListA,NewList).
	
collect_exp_(A+B, List, NewList) :-
	simplify(A,AT), collect_exp_(AT,List,ListA),
	simplify(B,BT), collect_exp_(BT,ListA,NewList).

collect_exp_(T, List/[Term|NewT], List/NewT) :-
	simplify_term(T,Term).

mul_term_(N,A,Term) :-
	simplify(N,NT), constant_(NT),
	simplify(A,AT),
	(constant_(AT) -> Term is AT*NT ; (sign_val_(Op,NT,M), Term = term(Op,AT,M))).
	
negate_exp_(T/T,NewT/NewT) :- var(T).
negate_exp_([term(Op,V,N)|Es]/T,[term(NOp,V,N)|NEs]/NewT) :- !,
	negate_op_(Op,NOp),
	negate_exp_(Es/T,NEs/NewT).
negate_exp_([C|Es]/T,[NC|NEs]/NewT) :-
	constant_(C), NC is -C,
	negate_exp_(Es/T,NEs/NewT).

collect_exp_items([],[]).
collect_exp_items([E|Es],[NE|NEs]) :-
	collect_exp_item_(Es,E,NE,ENxt),
	collect_exp_items(ENxt,NEs).

collect_exp_item_([],E,E,[]).
collect_exp_item_([V|Es],U,Eo,EsNxt) :-
	constant_(U), constant_(V),  % constant values must be precise to add
	S is U+V,
	collect_exp_item_(Es,S,Eo,EsNxt).
collect_exp_item_([term(Op1,V,N1)|Es],term(Op2,U,N2),Eo,EsNxt) :-
	V==U, catch(abs(V) =\= inf,_,true), !,  % if V==U = infinity, fail to next choice.
	sign_val_(Op1,N1,S1), sign_val_(Op2,N2,S2),
	S is S1+S2,
	sign_val_(Op,S,N),
	collect_exp_item_(Es,term(Op,V,N),Eo,EsNxt).
collect_exp_item_([term(Op1,V,N1)|Es],term(Op2,U,N2),Eo,EsNxt) :-
	atomic(V), atomic(U), abs(V) =:= inf, abs(U) =:= inf,
	throw(error("Arithmetic operations not allowed on two infinities.")).
collect_exp_item_([Ei|Es],E,Eo,[Ei|EsNxt]) :-  % Note that imprecise floats are not added
	collect_exp_item_(Es,E,Eo,EsNxt).


reduce_exp_items_([],0).
reduce_exp_items_([T],Exp) :-
	reduce_exp_item_(T,Exp,_,_).
reduce_exp_items_([T1,T2|Ts],Exp) :-
	reduce_exp_item_(T1,Exp1,_,_),
	reduce_exp_item_(T2,_,Op,Exp2),
	build_exp_(Exp1,Exp2,Op,ExpN), !,  % ExpN =.. [Op,Exp1,Exp2], !,
	reduce_exp_items_([ExpN|Ts],Exp).

% throws away zeros
build_exp_(Zero,Exp2,-,NExp2) :- Zero == 0, build_Nexp_(Exp2, NExp2).
build_exp_(Zero,Exp2,+,Exp2)  :- Zero == 0.
build_exp_(Exp1,Zero,_,Exp1)  :- Zero == 0.
build_exp_(Exp1,Exp2,Op,ExpN) :- ExpN =.. [Op,Exp1,Exp2].

build_Nexp_(  V,   -V) :- var(V).
build_Nexp_(Exp, NExp) :- constant_(Exp), NExp is -Exp.
build_Nexp_(N*T, NN*T) :- constant_(N), NN is -N.
build_Nexp_(N/T, NN/T) :- constant_(N), NN is -N.
build_Nexp_(Exp, -Exp).

reduce_exp_item_(          V,   V, +,   V) :- var(V).
reduce_exp_item_(term(O,V,N),   S, O,   T) :- reduce_term_(V,N,O,T,S).
reduce_exp_item_(          R,   R, -,   M) :- constant_(R), R<0, M is -R.  % negative constants
reduce_exp_item_(          T,   T, +,   T).              % positive constants and anything else (?) 

% Case 1: _ * 0.
reduce_term_(_,0,+,0,0).
% Case 2: var * constant
reduce_term_(V,1,+,V, V) :- var(V).
reduce_term_(V,1,-,V,-V) :- var(V).
reduce_term_(V,N,+,N*V,N*V) :- var(V).
reduce_term_(V,N,-,N*V,M*V) :- var(V), M is -N.
% Case 3: (mul and div) * constant - need to find the beginning
reduce_term_(V1*V2,N,Op,T*V2,S*V2) :- reduce_term_(V1,N,Op,T,S).
reduce_term_(V1/V2,N,Op,T/V2,S/V2) :- reduce_term_(V1,N,Op,T,S).
% Case 4: constant * constant
reduce_term_(C,N,+,T,T)  :- constant_(C), T is C*N.
reduce_term_(C,N,-,T,S)  :- constant_(C), T is C*N, S is -T.
% Case 5: constant * float (Open question - should eval be deferred due to possible rounding error?)
reduce_term_(F,N,Op,T,S) :- float(F), abs(F)=:=inf, T is copysign(inf,sign(F)*sign(N)), (Op= + -> S=T ; S is -T).
reduce_term_(F,N,+,T,T)  :- float(F), T is F*N.
reduce_term_(F,N,-,T,S)  :- float(F), T is F*N, S is -T.
% Case 6: anything_else * constant
reduce_term_(V,1,+,V, V).
reduce_term_(V,1,-,V, -V).
reduce_term_(V,N,+,N*V, N*V).
reduce_term_(V,N,-,N*V, M*V) :- M is -N.

%
% simplify a term to an "expression" of term structures and constants
%
simplify_term(T,Term) :-
	collect_term_(T, L/L, Ts/[]),    % collect in a difference list
	collect_term_items_([1|Ts],Is),  % ensure there's a constant multiplier and collect like terms
	sort_exp_(Is,[C|SIs]),           % multiplier will be first, all others sorted
	reduce_term_items_(SIs,ITerm),   % reduce back to expression
	% this does constant folding if reduction resulted in a constant
	(constant_(ITerm) -> Term is ITerm*C ; (sign_val_(Op,C,M), Term = term(Op,ITerm,M))),
	!.

collect_term_(A, List/[elem(*,A,1)|NewT], List/NewT) :-
	var(A), !.
	
collect_term_(A, List/[A|NewT], List/NewT) :-
	rational(A), !.

collect_term_(A, List/[elem(*,A,1)|NewT], List/NewT) :-
	float(A), !.

collect_term_(-A, List, ListA/NewT) :- % -Term as Term * -1 for reducing signs
	simplify(A,AT), collect_term_(AT,List,ListA/[-1|NewT]).

collect_term_(A**N, List/[Term|NewT], List/NewT) :-  % possible special case of user written element
	simplify(N,NT), constant_(NT),
	simplify(A,AT),
	(constant_(AT) -> Term is AT**NT ; (pwr_val_(Op,NT,P), Term = elem(Op,AT,P))).

collect_term_(A*B,List,NewList) :-
	simplify(A,AT),	simplify(B,BT),
	collect_term_(AT,List,ListA),
	collect_term_(BT,ListA,NewList).
	
collect_term_(A/B,List,NewList) :-
	simplify(A,AT),	simplify(B,BT),
	collect_div_(AT,BT,List,NewList).

collect_term_(E,List/[elem(*,Exp,1)|NewT], List/NewT) :-
	E =.. [F|IArgs],
	simplify_list_(IArgs,OArgs),
	Exp =.. [F|OArgs].

simplify_list_([],[]).
simplify_list_([I|IArgs],[O|OArgs]) :-
	simplify(I,O),
	simplify_list_(IArgs,OArgs).

collect_div_(AT,BT,List/[N|NewT], List/NewT) :-
	constant_(AT),constant_(BT),
	(BT==0 -> throw(error("Zero divisor in constraint expression":AT/BT)) ; true),  % throw exception if BT=0
	N is AT rdiv BT.  % rational constant expressed as AT/BT
collect_div_(AT,BT,List,ListA/NewT) :-
	collect_term_(AT,List,ListA/T),
	collect_term_(BT,P/P,ListB),
	invert_term_(ListB,T/NewT).
	
invert_term_(T/T,NewT/NewT) :- var(T).
invert_term_([elem(Op,V,N)|Es]/T,[elem(IOp,V,N)|NEs]/NewT) :-
	(V==0.0 -> throw(error("Zero divisor in constraint expression":'_'/V)) ; true),  % throw exception if V=0.0
	invert_op_(Op,IOp),  %% NN is -N,
	invert_term_(Es/T,NEs/NewT).
invert_term_([N|Es]/T,[NN|NEs]/NewT) :-
	rational(N,A,B),  % constants
	(A==0 -> throw(error("Zero divisor in constraint expression":N)) ; true),       % throw exception if A=0
	NN is B rdiv A,
	invert_term_(Es/T,NEs/NewT).
	
collect_term_items_([],[]).
collect_term_items_([E|Es],[NE|NEs]) :-
	collect_term_item_(Es,E,NE,ENxt),
	collect_term_items_(ENxt,NEs).

collect_term_item_([],E,E,[]).
collect_term_item_([V|Es],U,Eo,EsNxt) :-
	constant_(U), constant_(V),  % precise for multiply
	S is U*V,
	collect_term_item_(Es,S,Eo,EsNxt).
collect_term_item_([elem(Op1,V,N1)|Es],elem(Op2,U,N2),Eo,EsNxt) :-
	V==U, catch(abs(V) =\= inf,_,true), !,  % if V==U = infinity, fail to next choice.
	pwr_val_(Op1,N1,S1), pwr_val_(Op2,N2,S2),
	S is S1+S2,
	pwr_val_(Op,S,N),
	collect_term_item_(Es,elem(Op,V,N),Eo,EsNxt).
collect_term_item_([elem(Op1,V,N1)|Es],elem(Op2,U,N2),Eo,EsNxt) :-
	atomic(V), atomic(U), abs(V) =:= inf, abs(U) =:= inf,
	throw(error("Arithmetic operations not allowed on two infinities.")).
collect_term_item_([Ei|Es],E,Eo,[Ei|EsNxt]) :-
	collect_term_item_(Es,E,Eo,EsNxt).

reduce_term_items_([0|_],0).    % element is 0 => 0
reduce_term_items_([T],Exp) :-  %%%% guaranteed to have at least one item
	reduce_term_item_(T,E,Op),
	build_term_(1,E,Op,Exp).  %% (Op = / -> Exp=1/E ; Exp=E).
reduce_term_items_([T1,T2|Ts],Exp) :-
	reduce_term_item_(T1,Exp1,_),
	reduce_term_item_(T2,Exp2,Op),
	build_term_(Exp1,Exp2,Op,ExpN),  %% ExpN =.. [Op,Exp1,Exp2],
	!,
	reduce_term_items_([ExpN|Ts],Exp).

build_term_( One, Exp, *, Exp) :- One==1.
build_term_( One, Exp, /,IExp) :- One==1, (rational(Exp,M,N) -> IExp is N rdiv M ; IExp = 1/Exp).
build_term_( Exp, One, _, Exp) :- One==1.
build_term_(Exp1,Exp2,Op, Exp) :- Exp =.. [Op,Exp1,Exp2].

reduce_term_item_(elem( _,_,0),    1,  *).
reduce_term_item_(elem(Op,V,1),    V, Op).
reduce_term_item_(elem(Op,V,E), V**E, Op).
reduce_term_item_(           R,    R,  *).  % catchall?? presumably a constant
%%%%

%
% build a node from an expression
%
build_(Int, Int, VarType, Agenda, NewAgenda) :-     % existing interval object
	interval_object(Int, Type, _, _), !,
	applyType_(VarType, Type, Int, Agenda, NewAgenda).   % coerces exsiting intervals to required type
build_(Var, Var, VarType, Agenda, Agenda) :-        % implicit interval creation.
	var(Var), !,
	universal_interval(U),
	int_decl_(VarType,U,Var).
build_(Num, Int, _, Agenda, Agenda) :-              % floating point constant, may not be precise
	float(Num), !,
	Int::real(Num,Num).                             % will be fuzzed, so not a point
build_(Num, Num, _, Agenda, Agenda) :-              % rational numeric value is precise
	rational(Num), !.  %%integer(Num), !.
	% rational(Num,M,N), C is M/N, !.  %%integer(Num), !.
build_(pt(Num), Num, _, Agenda, Agenda) :-          % point value, must be a number
	numeric(Num), !.
build_(Exp, Int, VarType, Agenda, NewAgenda) :-
	ground(Exp),                                    % ground exp which evaluates to a number
	catch(V is Exp, _, fail),                       % also catches symbolic "numbers", e.g., inf, pi, ..
	build_(V, Int, VarType, Agenda, NewAgenda), !.  % may be fuzzed, so not a point
build_(Exp, Z, _, Agenda, NewAgenda) :-
	Exp =.. [F|Args],
	fmap_(F,Op,[Z|Args],ArgsR,Types), !,
	build_args_(ArgsR,Objs,Types,Agenda,ObjAgenda),
	newNode_(Op,Objs,ObjAgenda,NewAgenda).

build_args_([],[],_,Agenda,Agenda).
build_args_([Arg|ArgsR],[Obj|Objs],[Type|Types],Agenda,NewAgenda) :-
	build_(Arg,Obj,Type,Agenda,NxtAgenda),
	build_args_(ArgsR,Objs,Types,NxtAgenda,NewAgenda).

constraint_(C) :- nonvar(C), C =..[Op|_], fmap_(Op,_,_,_,[boolean|_]), !.  %  a constraint must evaluate to a boolean

fmap_(+,    add,   ZXY,     ZXY,     [real,real,real]).
fmap_(-,    add,   [Z,X,Y], [X,Z,Y], [real,real,real]).     % note subtract before minus 
fmap_(*,    mul,   ZXY,     ZXY,     [real,real,real]).
fmap_(/,    mul,   [Z,X,Y], [X,Z,Y], [real,real,real]).
fmap_(**,   pow,   ZXY,     ZXY,     [real,real,real]).
fmap_(min,  min,   ZXY,     ZXY,     [real,real,real]).
fmap_(max,  max,   ZXY,     ZXY,     [real,real,real]).
fmap_(==,   eq,    ZXY,     ZXY,     [boolean,real,real]).
fmap_(is,   eq,    ZXY,     ZXY,     [boolean,real,real]).
fmap_(<>,   ne,    ZXY,     ZXY,     [boolean,integer,integer]).
fmap_(=<,   le,    ZXY,     ZXY,     [boolean,real,real]).
fmap_(>=,   le,    [Z,X,Y], [Z,Y,X], [boolean,real,real]).
fmap_(<,    lt,    ZXY,     ZXY,     [boolean,real,real]).
fmap_(>,    lt,    [Z,X,Y], [Z,Y,X], [boolean,real,real]).
fmap_(<=,   sub,   ZXY,     ZXY,     [boolean,real,real]).  % inclusion/subinterval
fmap_(=>,   sub,   [Z,X,Y], [Z,Y,X], [boolean,real,real]).  % inclusion/subinterval

fmap_(and,  and,   ZXY,     ZXY,     [boolean,boolean,boolean]).
fmap_(or,   or,    ZXY,     ZXY,     [boolean,boolean,boolean]).
fmap_(nand, nand,  ZXY,     ZXY,     [boolean,boolean,boolean]).
fmap_(nor,  nor,   ZXY,     ZXY,     [boolean,boolean,boolean]).
fmap_(xor,  xor,   ZXY,     ZXY,     [boolean,boolean,boolean]).
fmap_(->,   imB,   ZXY,     ZXY,     [boolean,boolean,boolean]).

fmap_(sqrt,pow,   [Z,X],    [X,Z,2], [real,real,integer]).
fmap_(-,   minus, [Z,X],    [Z,X],   [real,real]).
fmap_(~,   not,   ZX,       ZX,      [boolean,boolean]).
fmap_(exp, exp,   ZX,       ZX,      [real,real]).
fmap_(log, exp,   [Z,X],    [X,Z],   [real,real]).
fmap_(abs, abs,   ZX,       ZX,      [real,real]).
fmap_(sin, sin,   ZX,       ZX,      [real,real]).
fmap_(asin,sin,   [Z,X],    [X,Z],   [real,real]).
fmap_(cos, cos,   ZX,       ZX,      [real,real]).
fmap_(acos,cos,   [Z,X],    [X,Z],   [real,real]).
fmap_(tan, tan,   ZX,       ZX,      [real,real]).
fmap_(atan,tan,   [Z,X],    [X,Z],   [real,real]).

%
% Node constructor
%
newNode_(Op, Args, Agenda, NewAgenda) :-
	NewNode =.. [node, Op, P, L|Args],
	addNode_(Args,NewNode),
	linkNode_(Agenda, NewNode, NewAgenda).

addNode_([],_Node).
addNode_([Arg|Args],Node) :-
	(interval_object(Arg, _Type, _Val, Nodelist) -> newmember(Nodelist, Node) ; true),
	addNode_(Args,Node).

% extend list with X
newmember([X|Xs],N) :- 
	nonvar(X), !,       % not end of (indefinite) list
	newmember(Xs,N).
newmember([N|_],N).     % end of list

%
% Process Agenda to narrow intervals
%
stable_(Agenda) :-
	current_prolog_flag(clpBNR_iteration_limit,Ops),  % budget for current operation
	stableLoop_(Agenda,Ops).

stableLoop_([]/[], OpsLeft) :- !,           % terminate successfully when agenda comes to an end
	nb_getval(clpBNR_iterations_,Cur),      % maintain "low" water mark (can be negative)
	(OpsLeft<Cur -> nb_linkval(clpBNR_iterations_,OpsLeft);true).  % nb_linkval OK for numbers
stableLoop_([Node|Agenda]/T, OpsLeft) :-
	doNode_(Node, OpsLeft, Agenda/T, NewAgenda), !,
	nb_setarg(3,Node,0),                    % reset linked bit
	RemainingOps is OpsLeft-1,              % decrement OpsLeft (can go negative)
	stableLoop_(NewAgenda,RemainingOps).
stableLoop_(Agenda, OpsLeft) :-             % doNode_ failed
	stableLoop_([]/[], OpsLeft),            % discard Agenda
	fail.                                   % and fail

% support for max_iterations statistic
clpStatistics :-
	current_prolog_flag(clpBNR_iteration_limit,L), nb_setval(clpBNR_iterations_,L),  % set "low" water mark to upper limit
	fail.  % backtrack to reset other statistics.

clpStatistic(max_iterations(O/L)) :-
	nb_getval(clpBNR_iterations_,Ops),
	current_prolog_flag(clpBNR_iteration_limit,L),
	O is L-Ops.  % convert "low" water mark to high water mark

%
% Execute a node on the queue
%
doNode_(node(instantiate,P,_,Int,Pt), _, Agenda, Agenda) :-  % frozen constraints must be run as stable_/1 step
	!, Int=Pt.  % cut before 'thaw', constraints run now on thaw
doNode_(Node, OpsLeft, Agenda, NewAgenda) :-
	Node =.. [node,Op,P,L|Args],
	var(P), !,                             % check persistent bit
	marshal_args_(Args,PrimArgs),
	evalNode(Op, P, PrimArgs, New),        % can fail causing stable_ to fail => backtracking
%	traceIntOp_(Op, Args, PrimArgs, New),  % in ia_utilities
	update_values_(PrimArgs, New, Args, OpsLeft, Agenda, NewAgenda),
	(ground(Args) -> P=p;true).            % conditionally set persistent bit
doNode_(Node, OpsLeft, Agenda, Agenda).    % persistent bit "set", skip node

marshal_args_([],[]).
marshal_args_([A|Args],[P|PrimArgs]) :-
	getValue(A,P),
	marshal_args_(Args,PrimArgs).

update_values_([], [], [], _, Agenda, Agenda).
update_values_([P|PrimArgs], [N|New], [A|Args], OpsLeft, Agenda, NewAgenda) :-
	updateValue_(P, N, A, OpsLeft, Agenda, NxtAgenda),
	update_values_(PrimArgs, New, Args, OpsLeft, NxtAgenda, NewAgenda).

%
% Any changes in interval values should come through here.
%
updateValue_(Old, Old, _, _, Agenda, Agenda) :- !.                  % no change in value
updateValue_(_Old, [Pt,Pt], Rat, _, Agenda, Agenda) :-              % could be just equivalent rational 
	rational(Rat), !,
	Rat =:= Pt.  % should always be true
updateValue_(_Old, [Pt,Pt], Int, _, Agenda, NewAgenda) :- !,        % Point value ==> update value
	putValue_([Pt,Pt], Int, Nodelist),  % ignore node list, will run via 'instantiate' node
	linkNode_(Agenda,node(instantiate,P,L,Int,Pt), NewAgenda).      % add 'instantiate' node to Agenda
updateValue_(Old, New, Int, OpsLeft, Agenda, NewAgenda) :-          % set value to New
	% NewL=<NewH,  % check unnecessary if primitives do their job
	putValue_(New, Int, Nodelist),                      % update value
	(propagate_if_(OpsLeft, Old, New)                   % if OpsLeft >0 or narrowing sufficent
		-> linkNodeList_(Nodelist, Agenda, NewAgenda)   % then propagate change
		 ; NewAgenda = Agenda                           % else continue with remaining Agenda
	).

propagate_if_(Ops, _, _)           :- Ops>0.  % ! unnecessary since it's used in '->' test
propagate_if_(_, [OH,OL], [NH,NL]) :- catch((NH-NL)/(OH-OL) < 0.9,_,true).  % any overflow in calculation will propagate

linkNodeList_([X|Xs], List, NewList) :-
	nonvar(X),                                     % not end of list ...
	arg(3,X,0),                                    % not linked and ...
	arg(2,X,P), var(P), !,                         % not persistent ->
	linkNode_(List, X, NextList),                  % add to list
	linkNodeList_(Xs, NextList, NewList).
linkNodeList_([X|Xs], List, NewList) :-            % skip node until end of list
	nonvar(X), !,
	linkNodeList_(Xs, List, NewList).
linkNodeList_(_, List, List).                      % end of indefinite node list (don't make it definite)

linkNode_(List/[X|NextTail], X, List/NextTail) :-
	setarg(3,X,1).                                 %% SWIP set linked bit, reset on backtracking

%%%%:- include(ia_utilities).  % print,solve, etc.
:- initialization((  % initialization takes single argument - form conjunction
	% use defined portray hook
	set_prolog_flag(write_attributes, portray),
	% increase max_depth (default 10)
	set_prolog_flag(answer_write_options,
		[quoted(false), portray(true), max_depth(64), spacing(next_argument)])
	)).

%
%  lower_bound and upper_bound
%
lower_bound(Int) :- 
	getValue(Int,[L,H]),
	Int=L.

upper_bound(Int) :-
	getValue(Int,[L,H]),
	Int=H.

%
%  print_interval(Int)
%
print_interval(ListOfInt) :-
	is_list(ListOfInt), !,
	write('['),
	print_intervals(ListOfInt),
	write(']').
	
print_interval(Int) :- 
	number(Int), !,  % point interval
	write(Int).
	
print_interval(Int) :-
	mapTerm_(Int,Out),!,
	write(Out).

print_intervals([]).
print_intervals([Int]) :- !,
	print_interval(Int).
print_intervals([Int|Ints]) :-
	print_interval(Int), write(','),
	print_intervals(Ints).
	

%
% portray for attributed interval objects (instantiated values print as numbers)
%    hook for system print/1
%
% direct use of portray/1
user:portray(Int) :-
	print_interval(Int).

%
%  SWI hook to print interval ranges for query variables
%
user:expand_answer(Bindings,ExBindings) :- 
	mapBindings_(Bindings,ExBindings).

mapBindings_([], []).
mapBindings_([Name=In|Bs], [Name=Out|ExBs]) :-
	mapTerm_(In,Out), !,
	mapBindings_(Bs,ExBs).

mapTerm_(Int,Out) :-
	interval_object(Int,T,Val,_NL),       % interval value, replace by Id(L,H)
	interval_domain_(T,Val,Dom),
	term_string(Int::Dom, Out).
mapTerm_(List,Out) :-
	is_list(List),
	mapEach_(List,Out).
mapTerm_(Comp,Out) :-
	compound(Comp),
	Comp=..[F|Ins],
	mapEach_(Ins,Outs),
	Out=..[F|Outs].
mapTerm_(T,T).
	
mapEach_([],[]).
mapEach_([In|Ins],[Out|Outs]) :-
	mapTerm_(In,Out), !,
	mapEach_(Ins,Outs).
	
/*
intValue(Id,T,[L,H],Out)  :- 
	V=..[T,L,H],
	term_string(Id::V, Out).

intValue(Id,L,H,Out) :-
	float(L), float(H),
	number_codes(L,LC), number_codes(H,HC),
	matching_(LC,HC,Match,0,MLen),
	MLen>5,
	atom_concat(Match,'...',Out).
matching_([],[],[],N,N).
matching_([C|LCs],[C|HCs],[C|Cs],N,Nout) :- !,  % matching
	succ(N,N1),
	matching_(LCs,HCs,Cs,N1,Nout).
matching_(LCs,HCs,[],N,N) :-    % non-matching
	digits_(LCs),digits_(HCs).  % remaining must be digit codes, i.e., no exponent

digits_([]).
digits_([D|Ds]) :- 48=<D,D=<57, digits_(Ds).
*/

%
%  trace debug code only -  used by stable_/1
%
traceIntOp_(Op, Ints, Ins, Outs) :-
	current_prolog_flag(debug, false), !.  % only while debugging
traceIntOp_(Op, Ints, Ins, Outs) :-
	write('node:  '),write(Op),write('('),
	traceInts(Ints),
	traceChanges(Ints, Ins, Outs),
	write('\n'), !.
	
traceInts([Int]) :- mapTerm_(Int,Out),print(Out),write(')').
traceInts([Int|Ints]) :- mapTerm_(Int,Out), print(Out), write(','), traceInts(Ints).

traceChanges([_Int], [In], [In]).  % no change
traceChanges([Int], [_],  [Out]) :-
	write('\n    '), mapTerm_(Int,F), functor(F,Id,_), print(Id), write(' <- '), write(Out).
traceChanges([Int|Ints], [In|Ins], [Out|Outs]) :-
	traceChanges([Int], [In], [Out]),
	traceChanges(Ints, Ins, Outs).

% for building ...
traceNew_(Cons) :-
	current_prolog_flag(debug, false), !.  % only while debugging
traceNew_(Cons) :-
	 nl,write({Cons}).

%
%  enumerate integer and boolean intervals
%
enumerate(X) :-
	interval(X), !,   % if single interval, put it into a list
	enumerate_([X]).  % list of one
enumerate(X) :-
	integer(X), !.    % already a point value
enumerate(X) :-
	enumerate_(X).

enumerate_([]).
enumerate_([X|Xs]) :-
	number(X), !,    % already bound to a point value
	enumerate_(Xs).
enumerate_([X|Xs]) :-
	interval(X),
	getValue(X,[L,H]),
	between(L,H,X),  % gen values, constraints run on unification
	enumerate_(Xs).

%
%  minimize(Interval, Vars, Solver)
%
%  search for minimized Interval using Solver, fails if no minimization possible
%  on successful exit Vars will be narrowed consistent with the minimized Interval (single solution)
%
minimize(Min,Vs,Solver) :-
	nb_delete(minimize__),  % Note: depends on global var so not thread-safe
	minimize__(Min,Vs,Solver).

minimize__(Min,Vs,Solver) :-
	interval(Min),               % only works on intervals (numbers, and others, can't be minimized)
	once(                        %% get first solution with a lower UB
		(range(Min,[_,PUB]),
		 Solver,
		 range(Min, [_,UB]),
		 UB < PUB  % specific check for new smaller UB, discards equivalent (and same) solutions
		)
	),
	nb_setval(minimize__, [1,Min,Vs]),  % new Min values for next iteration
	fail.
	
minimize__(Min,Vs,Solver) :-
	catch((nb_getval(minimize__, [1,NewMin,NewVs]),nb_setval(minimize__, [0,NewMin,NewVs])),_,fail),
	range(NewMin,[_,UB]), {Min=<pt(UB)},	% constrain UB, use pt() to avoid outward rounding
	minimize__(Min,Vs,Solver),
	!.
	
minimize__(Min,Vs,_):-  % can't minimize UB any further, retrieve last solution and fail if none
	catch((nb_getval(minimize__, [_,Min,Vs]),nb_delete(minimize__)),_,fail).

%
%  maximize(Interval, Vars, Solver)
%
%  analogous to minimize (see above)
%
maximize(Max,Vs,Solver) :-
	nb_delete(maximize__),  % Note: depends on global var so not thread-safe
	maximize__(Max,Vs,Solver).

maximize__(Max,Vs,Solver) :-
	interval(Max),               % only works on intervals (numbers, and others, can't be maximized)
	once(                        %% get first solution with a lower UB
		(range(Max,[PLB,_]),
		 Solver,
		 range(Max, [LB,_]),
		 LB > PLB  % specific check for new smaller UB, discards equivalent (and same) solutions
		)
	),
	nb_setval(maximize__, [1,Max,Vs]),  % new Min values for next iteration
	fail.
	
maximize__(Max,Vs,Solver) :-
	catch((nb_getval(maximize__, [1,NewMax,NewVs]),nb_setval(maximize__, [0,NewMax,NewVs])),_,fail),
	range(NewMax,[LB,_]), {Max>=pt(LB)},	% constrain LB, use pt() to avoid outward rounding
	maximize__(Max,Vs,Solver),
	!.
	
maximize__(Max,Vs,_):-  % can't minimize UB any further, retrieve last solution and fail if none
	catch((nb_getval(maximize__, [_,Max,Vs]),nb_delete(maximize__)),_,fail).

%
%  splitsolve(Int) - joint search on list of intervals
%  simple split, e.g., no filtering on splutions, etc.
%
splitsolve(X) :-
	current_prolog_flag(clpBNR_default_precision,P),
	splitsolve(X,P).

splitsolve(X,P) :-
	interval(X), !,               % if single interval, put it into a list
	splitsolve([X],P).
splitsolve(X,P) :-
	number(X), !.                 % already a point value
splitsolve(X,P) :-                     % assume list
	Err is 10**(-(P+1)),          % convert digits of precision to normalized error value 
	simplesolveall_(X,Err).
	   
simplesolveall_([],Err) :- !.
simplesolveall_(Xs,Err) :-
	simplesolve_each_(Xs,Us,Err),     % split once and collect successes
	simplesolveall_(Us,Err).          % continue to split remaining

simplesolve_each_([],[],Err) :- !.
simplesolve_each_([X|Xs],[X|Us],Err) :-
	interval_object(X,Type,B,_),          % get interval type and value
	simple_split_(Type,X,B,Err,Choices),  % split interval
	!,
	Choices,                              % create choice(point)
	simplesolve_each_(Xs,Us,Err).         % split others in list
simplesolve_each_([X|Xs],Us,Err) :-       % avoid freeze ovehead if [] unified in head
	X==[], !,                             % end of nested listed, discard
	simplesolve_each_(Xs,Us,Err).         % split remaining
simplesolve_each_([X|Xs],[U|Us],Err) :-
	is_list(X), !,                        % nested list
	simplesolve_each_(X,U,Err),           % split nested list
	simplesolve_each_(Xs,Us,Err).         % then others in main list
simplesolve_each_([X|Xs],Us,Err) :-
	simplesolve_each_(Xs,Us,Err).         % split failed or already a number, drop interval from list, and keep going

simple_split_(real,X,B,Err,({X =< pt(Pt)};{pt(Pt) =< X})) :-  %%%%%%
	splitinterval_real_(B,Pt,Err), !.

simple_split_(integer,X,B,_,({X =< Pt};{Pt < X})) :-
	splitinterval_integer_(B,Pt), !.
simple_split_(integer,X,_,_,enumerate_([X])).           % failed to split, so enumerate


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%					absolve( X )
%					absolve( X, Precision)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%  absolve( X ), for X an interval or list of intervals, is intended 
%  solely to trim up the boundaries of what is essentially a single
%  (non-point)  solution to a problem. Hence absolve- unlike the rest
%  of the solve family -  is deterministic!
%	 The strategy used in absolve( derived from the old V 3 solve) is to 
%  work in from the edges of the interval ("nibbling away") until you
%  cannot go nay farther, then reduce step size and resume nibbling.
%  Control parameters limit the number of successive halvings of the 
%  step size, which is initially the interval width. 
%  		Note that absolve and solve each abstract a different part of
%  of the strategy used in the solve in BNRP V. 3. In this sense, the
%  combination: " solve(X), absolve(X) "  { in that order } does something
%  like what "solve(X)"did under the old system.


absolve( X ):- absolve(X,12),!.

absolve( X , Limit ):-
	interval_object(X, Type, [L,U], _),     % get interval type and value
	delta_(Type,L,U,Delta),
	absolve_l(X,Delta,L,1,Limit),!,
	absolve_r(X,Delta,U,1,Limit),!.

absolve( [], _).		% extends to lists
absolve( [X|Xs],Lim):- absolve(X,Lim),!, absolve(Xs,Lim).

delta_(integer,L,U,D) :- D is U div 2 - L div 2.
delta_(real,L,U,D)    :- D is U/2 - L/2.

absolve_l(X, _, _, _, _) :- 
		not(not(lower_bound(X))),	% changed 93/06/01 WJO to avoid getting stuck on lower bound
		!.
absolve_l(X, DL,LB, NL,Limit):- NL<Limit, % work on left side
	interval_object(X, Type, [LB2, UB2], _),     % get interval type and value
	trim_point_(NL,NL1,Type,Limit, DL,DL1),
	% DL1 > 0,
		%domain_(X, real(LB2, UB2)),
        Split is LB + DL1,
		Split > LB2, Split < UB2,	% changed 93/06/01 WJO make sure that the interval can be split
        not(  {X=<Split}),!,  % so X must be > split
        {X >= Split},
  	interval_object(X, Type, [LB1, _], _),     % get interval type and value
        % domain_(X, real(LB1, U)),!,  %  nl, print(X)
        absolve_l(X, DL1, LB1,NL1,Limit).
absolve_l(_, _, _,  _,_).
         
absolve_r(X, _, _, _, _) :-
		not(not(upper_bound(X))),	% changed 93/06/01 WJO to avoid getting stuck on upper bound
		!.
absolve_r(X, DU,UB, NU,Limit):- NU<Limit, % work on right side
	interval_object(X, Type, [LB2, UB2], _),     % get interval type and value
	trim_point_(NU,NU1,Type,Limit, DU,DU1),
	% DU1 > 0,
		%domain_(X, real(LB2, UB2)),
        Split is UB - DU1,
		Split > LB2, Split < UB2,	% changed 93/06/01 WJO make sure that the interval can be split
        not(  {X>=Split}),!,       % so X must be > split
        {X =< Split},
  	interval_object(X, Type, [_, UB1], _),     % get interval type and value
       % domain_(X, real(_, UB1) ),!,  % nl, print(X), 
        absolve_r(X, DU1,UB1, NU1,Limit).
absolve_r(_, _, _,  _,_).

trim_point_( N,N, _Type, _Limit, Delta, Delta).
trim_point_( N,M, integer, Limit, Delta, Result):- N<Limit,N1 is N + 1,
       D is  Delta div 2,
       trim_point_(N1,M, integer, Limit,D, Result).
trim_point_( N,M, real, Limit, Delta, Result):- N<Limit,N1 is N + 1,
       D is  Delta/2,
       trim_point_(N1,M,real, Limit,D, Result).

%
%  solve(Int) - joint search on list of intervals
%
solve(X) :-
	current_prolog_flag(clpBNR_default_precision,P),
	solve(X,P).

solve(X,P) :-
	interval(X), !,               % if single interval, put it into a list
	solve([X],P).
solve(X,P) :-
	number(X), !.                 % already a point value
solve(X,P) :-                     % assume list
	Err is 10**(-(P+1)),          % convert digits of precision to normalized error value 
	xpsolveall_(X,Err).
	
xpsolveall_([],Err) :- !.
xpsolveall_(Xs,Err) :-
	xpsolve_each_(Xs,Us,Err),     % split once and collect successes
	xpsolveall_(Us,Err).          % continue to split remaining

xpsolve_each_([],[],Err).
xpsolve_each_([X|Xs],[X|Us],Err) :-
	interval_object(X,Type,_,_),          % get interval type and value
	splitinterval_(Type,X,Err,Choices),   % split interval
	!,
	Choices,                              % create choice(point)
	xpsolve_each_(Xs,Us,Err).             % split others in list
xpsolve_each_([X|Xs],Us,Err) :-           % avoid freeze ovehead if [] unified in head
	X==[], !,                             % end of nested listed, discard
	xpsolve_each_(Xs,Us,Err).             % split remaining
xpsolve_each_([X|Xs],[U|Us],Err) :-
	is_list(X), !,                        % nested list
	xpsolve_each_(X,U,Err),               % split nested list
	xpsolve_each_(Xs,Us,Err).             % then others in main list
xpsolve_each_([X|Xs],Us,Err) :-
	xpsolve_each_(Xs,Us,Err).             % split failed or already a number, drop interval from list, and keep going
	
%
% try to split interval - fails if unsplittable (too narrow)
%
splitinterval_(real,X,Err,({X =< SPt};{SPt =< X})) :-
	getValue(X,V),
	% nl,write(splitting(V)),
	splitinterval_real_(V,Pt,Err), !,           % initial guess
	split_real_(X,V,Pt,Err,SPt).
	
splitinterval_(integer,X,_,({X =< Pt};{Pt < X})) :-   % try to split and on failure use enumerate/1 .
	getValue(X,V),
	splitinterval_integer_(V,Pt), !.
splitinterval_(integer,X,_,enumerate_([X])).           % failed to split, so enumerate

splitinterval_(boolean,X,Err,Choices) :-
	splitinterval_(integer,X,Err,Choices).


%  split a real interval
split_real_(X,_,Pt,_,pt(Pt)) :-            % Pt not in solution space, split here
	X\=Pt, !.
split_real_(X,[L,H],Pt,Err,pt(NPt)) :-     % Pt in current solution space, try lower range
	split_real_lo(X,[L,Pt],NPt,Err), !.
split_real_(X,[L,H],Pt,Err,pt(NPt)) :-     % Pt in current solution space, try upper range
	split_real_hi(X,[Pt,H],NPt,Err).

split_real_lo(X,[L,Pt],NPt,Err) :-         % search lower range for a split point 
	splitinterval_real_([L,Pt],SPt,Err), !,
	(X\=SPt -> NPt=SPt ; split_real_lo(X,[L,SPt],NPt,Err)).

split_real_hi(X,[Pt,H],NPt,Err) :-         % search upper range for a split point 
	splitinterval_real_([Pt,H],SPt,Err), !,
	(X\=SPt -> NPt=SPt ; split_real_hi(X,[SPt,H],NPt,Err)).


%
% splitinterval_integer_ and splitinterval_real_ require ! at point of call.
%
	
splitinterval_integer_([L,H],0) :-
	L < 0, H > 0.                     % contains 0 but not 0 
splitinterval_integer_([-1.0Inf,H],Pt) :-
	Pt is H*10-5.                     % subtract 5 in case H is 0. (-5, -15, -105, -1005, ...)
splitinterval_integer_([L,-1.0Inf],Pt) :-
	Pt is L*10+5.                     % add 5 in case L is 0. (5, 15, 105, 1005, ...)
splitinterval_integer_([L,H],Pt) :- 
	catch(H-L >= 16, _Err, fail),     % don't split ranges smaller than 16
%	catch(H-L >= 4, _Err, fail),      % don't split ranges smaller than 4
	Pt is (L div 2) + (H div 2).      % avoid overflow


splitinterval_real_([L,H],0.0,E) :-  % if interval contains 0, split on 0.
	L < 0, H > 0, !,
	catch((H-L) > E, _, true).       % fail if width is less than error criteria, overflow is OK
splitinterval_real_([-1.0Inf,H],Pt,_) :-   % neg. infinity to zero or neg. H
	Pt is H*10-1.                    % subtract 1 in case H is 0. (-1, -11, -101, -1001, ...)
splitinterval_real_([L,1.0Inf],Pt,_) :-   % zero or pos. L to pos. infinity
	Pt is L*10+1.                    % add 1 in case L is 0. (1, 11, 101, 1001, ...)
splitinterval_real_([L,H],Pt,E) :-   % finite L,H, positive or negative but not split
	splitMean_(L,H,Pt),
	MinZ isH 0.0,                    % use rounding to limit 0.0 case
	MinW is max(MinZ,abs(Pt)*E),     % Minimum width at Pt due to Err criteria
	(Pt-L) > MinW, (H-Pt) > MinW.


% geometric mean of L and H (same sign) if not non-zero, arithmetic mean if either 0
splitMean_(L,H,M) :- L>0, !, M is sqrt(L)*sqrt(H).     % avoid overflow
splitMean_(L,H,M) :- H<0, !, M is -sqrt(-L)*sqrt(-H).
splitMean_(L,H,M) :- L=:=0, !, M is H/2.
splitMean_(L,H,M) :- H=:=0, !, M is L/2.
%%%%

%
% Get all defined statistics
%
clpStatistics(Ss) :- findall(S, clpStatistic(S), Ss).

% end of reset chain succeeds. Need cut since predicate is "discontiguous".
clpStatistics :- !.

:- initialization((
	nl,write("*** clpBNR v0.7.3alpha ***"),nl,
	set_prolog_stack(global,min_free(8196)),
	create_prolog_flag(clpBNR_iteration_limit,10000,[type(integer)]),
	create_prolog_flag(clpBNR_default_precision,6,[type(integer)]),
	clpStatistics
)).
