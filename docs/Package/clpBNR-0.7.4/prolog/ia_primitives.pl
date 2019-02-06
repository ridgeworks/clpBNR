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

recover_(X**Y, float_overflow, Z)      :- Z is copysign(inf,X).

recover_(exp(X), float_overflow, 1.0Inf).

recover_(Inf, float_overflow, Z)       :- abs(Inf) =:= inf, Z is Inf.

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
g_inc(G)    :- nb_getval(G,N), succ(N,N1), nb_linkval(G,N1).  % measured as slightly faster
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
	sin_(MX,Xp,Z,NMX,X1,Z1),
	unwrap_(X1,2*pi,NMX,X2),      % project back to original cylinder
	^(X,X2,NewX),
	^(Z1,[-1,1],NewZ).            % take care of any rounding beyond range

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
	cos_(MX,Xp,Z,NMX,X1,Z1),
	unwrap_(X1,2*pi,NMX,X2),      % project back to original cylinder
	^(X,X2,NewX),
	^(Z1,[-1,1],NewZ).            % take care of any rounding beyond range

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
