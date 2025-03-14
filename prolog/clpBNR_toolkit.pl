/*	The MIT License (MIT)
 *
 *	Copyright (c) 2022-2024 Rick Workman
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
:- module(clpBNR_toolkit,       % SWI module declaration
	[
	iterate_until/3,            % general purpose iterator
	mid_split_one/1,            % contractor to split largest interval at midpoint
	mid_split/1,                % contractor to split an interval at midpoint
	taylor_contractor/2,        % build cf_contractor based on Taylor expansion
	taylor_merged_contractor/2, % build merged Taylor cf_contractor from list of equations
	cf_contractor/2,            % execute cf_contractor
	cf_solve/1, cf_solve/2,     % a solve predicate for centre form contractors

	integrate/3, integrate/4,   % simple numerical integration
	boundary_values/2, boundary_values/3, boundary_values/4,  % solve boundary value problems

	lin_minimum/3,              % find minimum of linear problem using library(simplex)
	lin_maximum/3,              % find maximum of linear problem using library(simplex)
	lin_minimize/3,             % lin_minimum/3 plus bind vars to solution minimizers
	lin_maximize/3,             % lin_maximum/3 plus bind vars to solution maximizers

	local_minima/1,             % apply KT constraints for objective function expression (OFE)
	local_maxima/1,             % semantically equivalent to local_minima/1
	local_minima/2,             % apply KT constraints for minima with constraints
	local_maxima/2              % apply KT constraints for maxima with constraints
	]).
	
/** <module> clpBNR_toolkit: Toolkit of various utilities used for solving problems with clpBNR

CLP(BNR) (=|library(clpBNR)|=) is a CLP over the domain of real numbers extended with ±∞. This module contains a number of useful utilities for specific problem domains like the  optimization of linear systems, enforcing local optima conditions, and constructing centre form contractors to improve performance (e.g., Taylor extensions of constraints). For more detailed discussion, see [A Guide to CLP(BNR)](https://ridgeworks.github.io/clpBNR/CLP_BNR_Guide/CLP_BNR_Guide.html) (HTML version included with this pack in directory =|docs/|=).

Documentation for exported predicates follows. The "custom" types include:
*  _interval_  : a variable with a =clpBNR= attribute
*  _numeric_   : an _interval_ or a _number_
*  _|*_list|_  : a list of _|*|_
*/
:- use_module(library(apply),[maplist/3]).
:- use_module(library(apply_macros)).  % compiler support for `maplist`, helps a bit
:- use_module(library(clpBNR)).
:- use_module(library(simplex)).

% sandboxing for SWISH
:- multifile(sandbox:safe_primitive/1).

% messages for noisy failure
fail_msg_(FString,Args) :-
	debug(clpBNR,FString,Args), fail.
	
:- set_prolog_flag(optimise,true).  % for arithmetic, this module only

/**
iterate_until(+Count:integer,Test,Goal) is nondet

Succeeds when Goal succeeds; otherwise fails. Goal will be called recursively up to Count times as long as Test succeeds Example using this predicate for simple labelling using Test =small/2= and Goal =|midsplit/1|= :
==
?- X::real(-1,1),iterate_until(10,small(X,0),mid_split(X)),format("X = ~w\n",X),fail;true.
X = _6288{real(-1,-1r2)}
X = _6288{real(-1r2,0)}
X = _6288{real(0,1r2)}
X = _6288{real(1r2,1)}
true.
==
The specific intended use case is to provide an iterator for meta-contractors such as the centre-form contractor such as =|midsplit/1|= (example above) or as constructed by =|taylor_contractor/2|= as in:
==
?- X::real,taylor_contractor({X**4-4*X**3+4*X**2-4*X+3==0},T),
iterate_until(50,small(X),(T,mid_split_one([X]))),format("X = ~w\n",X),fail;true.
X = _150{real(0.999999999926943,1.00000000007306)}
X = _150{real(2.999999999484828,3.0000000005152105)}
true.
==
(Aside: For some problems, solving with Taylor contractors can be a faster and more precise alternative to =|clpBNR:solve/1|=.)
*/
%
% General purpose iterator: execute Goal a maximum of N times or until Test succeeds
%
iterate_until(N,Test,Goal) :- N>0, !,
	Goal,
	N1 is N-1,
	(Test
	 -> true
	  ; iterate_until(N1,Test,Goal)
	).
iterate_until(_N,_,_).  % non-positive N --> exit

sandbox:safe_meta(clpBNR_toolkit:iterate_until(_N,Test,Goal), [Test, Goal]).

/**
mid_split_one(+Xs:numeric_list) is nondet

Succeeds splitting the widest interval in Xs, a list of intervals; fails if Xs is not a list of intervals. See =|mid_split|= for details of interval splitting for this predicate.

@see =|mid_split/1|=
*/
mid_split_one(Xs) :-
	select_split(Xs,X),  % select largest interval with largest width
	mid_split(X).        % split it
/**
mid_split(X:numeric) is nondet

Succeeds if X is an interval that can be split at its midpoint narrowing X to it's lower "half"; on backtracking X is constrained to the upper half; fails if X is not a numeric. If X is an interval, defined as:
==
mid_split(X) :-
	M is midpoint(X),
	({X=<M} ; {M=<X}).
==
Note that =|mid_split|= succeeds if X is a number, but doesn't do anything.

Use =|clpBNR:small|= as a pre-test to avoid splitting intervals which are already small enough.

@see =|clpBNR:small/1|=
*/
mid_split(X) :-
	(number(X)                    % optimise number case
	 -> true
	 ;  (small(X)
	     -> true
	     ;  midpoint(X,M),       % fails if not an interval
	        ({X=<M} ; {M=<X})    % possible choicepoint
	    )
	).
%
% select interval with largest width
%
select_split([X],X) :- !.       % select last remaining element
select_split([X1,X2|Xs],X) :-   % compare widths and discard one interval
	delta(X1,D1),
	delta(X2,D2),
	(D1 >= D2
	 -> select_split([X1|Xs],X)
	 ;  select_split([X2|Xs],X)
	).

/**
cf_contractor(Xs:interval_list,As:interval_list) is semidet

Succeeds if each interval in As can be unified with the midpoints of the respective interval in Xs; otherwise fails. This predicate executes one narrowing step of the centre form contractor such as that generated by =|taylor_contractor|=. In normal usage, a direct call to =|cf_contractor|= does appear; instead use =|cf_contractor|= or in a =|Goal|= for =|iterate_until/3|=.

@see =|taylor_contractor/2|=, =|cf_solve/1|=, =|iterate_until/3|=
*/
%
% centred form contractor
%
% Bind the values of As to the midpoints of Xs. To support repetitive application 
% of the contractor (required by the iterator), the contractor should not permanently 
% bind anything so findall/3 will be used to achieve this "forward checking" 
% (as suggested in [CLIP]). After the call to findall, the bounds of the resulting list
% of narrowed domains (XDs) are then applied to Xs.
%
% This contractor can be used with any "centred form", e.g., Newton or Krawczyk, since it
% only depends on intervals and their midpoints, hence its name `cf_contractor`. The 
% details which distinguish the variety of centred form are built into the variables' 
% constraints.
%
cf_contractor(Xs,As) :-
	findall(Ds,(maplist(bind_to_midpoint,Xs,As),maplist(cf_domain,Xs,Ds)),[XDs]),
	maplist(set_domain,Xs,XDs).
	
bind_to_midpoint(X,A) :- A is float(midpoint(X)).

cf_domain(X,D) :- 
	number(X) -> D = X ; domain(X,D).  % in case X narrowed to a point
	
set_domain(X,D) :- 
	number(D) -> X = D ; X::D.

/**
cf_solve(+Contractor) is nondet

Equivalent to =|cf_solve/2|= using default precision.
*/
/**
cf_solve(+Contractor, +Precision:integer) is nondet

Succeeds if a solution can be found for all variables in the centre form contractor, Contractor, where the resultant domain of any variable is narrower than the limit specified by Precision (for cf_solve/1, default Precision is number of digits as defined by the environment flag  =clpBNR_default_precision=); otherwise fails. 

This is done by using =|iterate_until/3|= limited to a count determined by the flag  =|clpBNR_iteration_limit|=. Examples:
==
?- X::real, taylor_contractor({X**4-4*X**3+4*X**2-4*X+3==0},T), cf_solve(T).
T = cf_contractor([X], [_A]),
X:: 1.000000000...,
_A::real(-1.0Inf, 1.0Inf) ;
T = cf_contractor([X], [_A]),
X:: 3.00000000...,
_A::real(-1.0Inf, 1.0Inf) ;
false.

?- taylor_contractor({2*X1+5*X1**3+1==X2*(1+X2), 2*X2+5*X2**3+1==X1*(1+X1)},T), cf_solve(T).
T = cf_contractor([X2, X1], [_A, _B]),
X1:: -0.42730462...,
X2:: -0.42730462...,
_B::real(-1.0Inf, 1.0Inf),
_A::real(-1.0Inf, 1.0Inf) ;
false.
==

@see =|taylor_contractor/2|=, =|cf_contractor/2|=
*/
cf_solve(T) :-
    current_prolog_flag(clpBNR_default_precision,P),
    cf_solve(T,P).
cf_solve(cf_contractor(Xs,As),P) :-
    current_prolog_flag(clpBNR_iteration_limit,L),
    Count is L div 10,          % heuristic - primitive iteration limit/10    
    cf_iterate_(Count,Xs,As,P).

cf_iterate_(Count,Xs,As,P) :-
	Count > 0,
	\+ small(Xs,P),             % at least one var not narrow enough
	!, 
	cf_contractor(Xs,As),       % execute contractor
	select_split(Xs,X),         % select widest
	(small(X,P)                 % still wide enough to split?
	 -> true                    % no, we're done 
	  ; mid_split(X),           % yes, split it
	    Count1 is Count-1,
	    cf_iterate_(Count1,Xs,As,P)  % and iterate
	).
cf_iterate_(_,_,_,_).           % done (Count=<0 or all small Xs)

/**
taylor_contractor(+Constraints,-Contractor) is semidet

Succeeds if a centre form contractor Contractor can be generated from one or more multivariate equality (=|==|= or =|=:=|=) constraints Constraints; otherwise fails. Example:
==
?- taylor_contractor({X**4-4*X**3+4*X**2-4*X+3==0},T).
T = cf_contractor([X], [_A]),
X::real(-1.509169756145379, 4.18727500493995),
_A::real(-1.0Inf, 1.0Inf).
==
Use the contractor with =|cf_solve|= to search for solutions, as in:
==
?- X::real,taylor_contractor({X**4-4*X**3+4*X**2-4*X+3==0},T), cf_solve(T).
T = cf_contractor([X], [_A]),
X:: 1.000000000...,
_A::real(-1.0Inf, 1.0Inf) ;
T = cf_contractor([X], [_A]),
X:: 3.00000000...,
_A::real(-1.0Inf, 1.0Inf) ;
false.
==
Multiple equality constraints are supported, as in this example of the Broyden banded problem (N=2):
==
?- taylor_contractor({2*X1+5*X1**3+1==X2*(1+X2), 2*X2+5*X2**3+1==X1*(1+X1)},T), cf_solve(T).
T = cf_contractor([X2, X1], [_A, _B]),
X1:: -0.42730462...,
X2:: -0.42730462...,
_B::real(-1.0Inf, 1.0Inf),
_A::real(-1.0Inf, 1.0Inf) ;
false.
==
Centre form contractors can converge faster than the general purpose builtin fixed point iteration provided by =|solve/1|=. 

@see =|cf_solve/1|=
*/
%
% build a cf_contractor for a multivariate expression based on Taylor expansion
%
taylor_contractor({E1=:=E2},CF) :-
	taylor_contractor({E1==E2},CF).
taylor_contractor({E1==E2},cf_contractor(Xs,As)) :-
	Exp=E1-E2,
	term_variables(Exp,Xs),              % original arguments, bound to TXs on call
	make_EQ_(Exp,TEQ),                   % original constraint with arguments
	% build constraint list starting with Z's and ending with TEQ and DEQ ()
	T::real(0,1),
	make_As_and_Zs_(Xs,T,As,Zs,Cs,[TEQ,DEQ]),  % T per Z
	% now build Taylor constraint, DEQ
	copy_term_nat(Exp,AExp),              % copy of original constraint with  As
	term_variables(AExp,As),
	sum_diffs(Xs, As, Zs, Zs, Exp, AExp, DEQ),  % add on D(Z)'s'
	% make any vars in original equation and contractor arguments finite real intervals
	!,
	Xs::real,  % all vars are intervals
	{Cs}.      % apply constraints
taylor_contractor({Es},CF) :-
	taylor_merged_contractor({Es},CF),  % list or sequence	
	!.
taylor_contractor(Eq,_) :-
	fail_msg_('Invalid constraint for Taylor contractor: ~w',[Eq]).

make_As_and_Zs_([],_,[],[],Tail,Tail).
make_As_and_Zs_([X|Xs],T,[A|As],[Z|Zs],[Z==A+T*(X-A)|CZs],Tail) :-
	make_As_and_Zs_(Xs,T,As,Zs,CZs,Tail).

sum_diffs([], [], [], _AllZs, _Exp, ExpIn, EQ) :- make_EQ_(ExpIn,EQ).
sum_diffs([X|Xs], [A|As], [Z|Zs], AllZs, Exp, AExp, DEQ) :-
	copy_term_nat(Exp,NExp),        % copy expression and replace Xs by Zs
	term_variables(NExp,AllZs),
	partial_derivative(NExp,Z,DZ),  % differentiate wrt. Z and add to generated expression
	sum_diffs(Xs, As, Zs, AllZs, Exp, AExp+DZ*(X-A), DEQ).

% map expression Exp to an equation equivalent to Exp==0 with numeric RHS
make_EQ_(Exp,LHS==RHS) :-    % turn expression into equation equivalent to Exp==0.
	make_EQ_(Exp,LHS,RHS).
	
make_EQ_(E,E,0)         :- var(E), !.
make_EQ_(X+Y,X,SY)      :- number(Y), !, SY is -Y.
make_EQ_(X-Y,X,Y)       :- number(Y), !.
make_EQ_(X+Y,Y,SX)      :- number(X), !, SX is -X.
make_EQ_(X-Y,SY,SX)     :- number(X), !, SX is -X, negate_sum_(Y,SY).
make_EQ_(X+Y,LHS+Y,RHS) :- !, make_EQ_(X,LHS,RHS).
make_EQ_(X-Y,LHS-Y,RHS) :- !, make_EQ_(X,LHS,RHS).
make_EQ_(E,E,0).        % default (non +/- subexpression)

negate_sum_(Y,-Y) :- var(Y), !.
negate_sum_(X+Y,NX-Y) :- !, negate_sum_(X,NX).
negate_sum_(X-Y,NX+Y) :- !, negate_sum_(X,NX).
negate_sum_(E,-E).

/**
taylor_merged_contractor(+Constraints,-Contractor) is semidet

Succeeds if a merged centre form contractor Contractor can be generated from each equality (=|==|= or =|=:=|=) constraint in Constraints; otherwise fails. 

@deprecated - use =|taylor_contractor/2|= instead
*/
%
% build a cf_contractor by merging a list of cf_contractor's
%
taylor_merged_contractor({Es},T) :-
	cf_list(Es,Ts),
	cf_merge(Ts,T).

cf_list([],[]) :- !.
cf_list([C|Cs],[CF|CFs]) :- !,
	cf_list(C, CF),
	cf_list(Cs,CFs).
cf_list((C,Cs),[CF|CFs]) :-  !,
	cf_list(C, CF),
	cf_list(Cs,CFs).
cf_list(C,CF) :-
	taylor_contractor({C},CF).

cf_merge(CFs,CF) :- cf_merge(CFs,cf_contractor([],[]),CF).

cf_merge([],CF,CF).
cf_merge([CF|CFs],CFIn,CFOut) :-
	cf_merge(CF,CFIn,CFNxt),
	cf_merge(CFs,CFNxt,CFOut).	
cf_merge(cf_contractor(Xs,As),cf_contractor(XsIn,AsIn),cf_contractor(XsOut,AsOut)) :-
	cf_add(Xs,As,XsIn,AsIn,XsOut,AsOut).

cf_add([],[],Xs,As,Xs,As).
cf_add([X|Xs],[A|As],XsIn,AsIn,XsOut,AsOut) :-
	var_existing(XsIn,AsIn,X,A), !,
	cf_add(Xs,As,XsIn,AsIn,XsOut,AsOut).
cf_add([X|Xs],[A|As],XsIn,AsIn,XsOut,AsOut) :-
	cf_add(Xs,As,[X|XsIn],[A|AsIn],XsOut,AsOut).

var_existing([Xex|Xs],[Aex|As], X,A) :- Xex==X -> Aex=A ; var_existing(Xs,As,X,A).

/**
integrate(+F,-X:interval,-R) is semidet

Equivalent to =|integrate/4|= with default precision.
*/
/**
integrate(+F,-X:interval,-R,+P:integer) is semidet

Succeeds if R is the numerical integration of F over the range of interval X.  F must be continuously differentiable over this range or it fails.

The number of integration steps (= 2**P) is determined by the precision parameter P (default is value of environment flag clpBNR_default_precision). Example of use with increasing precision values:
==
?- X::real(0.0,1.0), F=X**2, between(2,10,P),integrate(F,X,RV,P), range(RV,R), format('~w:~w\n',[P,R]), fail.
2:[0.328125,0.359375]
3:[0.33203125,0.33984375]
4:[0.3330078125,0.3349609375]
5:[0.333251953125,0.333740234375]
6:[0.33331298828125,0.33343505859375]
7:[0.3333282470703125,0.3333587646484375]
8:[0.3333320617675781,0.3333396911621094]
9:[0.33333301544189453,0.33333492279052734]
10:[0.33333325386047363,0.33333373069763184]
false.
==
*/

% integrate(F,X,R) where X is an interval over which to integrate and F = f(X)
% Note that integrate(F,X,R) is equivalent to boundary_values(X,[dV(_,F,0,R])
integrate(F,X,R) :-
	current_prolog_flag(clpBNR_default_precision,P),
	integrate(F,X,R,P,_).
integrate(F,X,R,P) :-
	integrate(F,X,R,P,_).
integrate(F,X,R,P,Steps) :-                    % internal arity 5 for development
	compound(F),                               % F must be an expression in X
    interval(X),                               % X must be an interval 
    integer(P), P>0,                           % P must be positive integer
	!,                                         % args OK, commit 
	boundary_values(X,[dV(_,F,0,R)],P,Steps). % use integration in `boundary_values`
integrate(F,X,R,P,_Steps) :-
	fail_msg_('Invalid argument(s): ~w',[integrate(F,X,R,P)]).

/**
boundary_values(-X:interval, +Dvars:list) is semidet

Equivalent to  =|boundary_values/4|= with default precision and discarding steps list.
*/
/**
boundary_values(-X:interval, +Dvars:list, +P:integer) is semidet

Equivalent to =|boundary_values/4|= discarding steps list.
*/
/**
boundary_values(-X:interval, +Dvars:list, +P:integer, -Steps:list) is semidet

Succeeds if a solution can be found to the boundary value problem specified by the independent variable X and the list of dependent variables defined by Dvars. Each dependent variable definition is a compound term of the form `dV(Y, Fxy, Yi, Yf)`. The initial and final values of the independent variable for the purposes of the boundary value problem are specified by the lower and upper values of the domain of X. The arguments of for `dvar/4`
are:
* `Y` : the dependent variable for this definition
* `Fxy` : an expression defining the derivative of Y with respect to `X`
* `Yi` : the value of `Y` when `X` takes the value of its lower bound
* `Yf` : the value of `Y` when `X` takes the value of its upper bound
The intent of this predicate is to find values for any of the unspecified boundary values (i.e., any `Yi`,`Yf`). An unbound `Yi` and `Yf` can be any evaluable arithmetic expression. The actual dependent and independent variables (`X` and `Y`'s respectively) are unchanged.

The optional third argument `P` defines a precision value, a positive integer (default = environment flag `clpBNR_default_precision`), which controls the the numerical integration; larger `P` means smaller step size.

The arity 4 version has an additional (final) argument which is unified with a list of the step values generated by the integration; each value is a tuple of the form `(X,Ys)`.

This predicate fails if any of the arguments are invalid (generates an error message if `clpBNR` debug topic is enabled) or if a solution to the boundary value problem cannot be found.  Examples for X in the range 0..1 and derivative of `Y = -2*X*Y`:
==
?- X::real(0,1), boundary_values(X,[dV(Y, -2*X*Y,1,Yf)]).
X::real(0, 1),
Yf:: 0.368... .

?- X::real(0,1),boundary_values(X,[dV(Y, -2*X*Y,1,Yf)],9).
X::real(0, 1),
Yf:: 0.36788... .

?- X::real(0,1), boundary_values(X,[dV(Y, -2*X*Y,Yi,1/e)]).
X::real(0, 1),
Yi:: 1.00... .

?- debug(clpBNR).
true.

?- X=42, boundary_values(X,[dV(Y, -2*X*Y,Yi,1/e)]).
% Invalid argument(s): boundary_values(42,[dV(_10836,-2*42*_10836,_10850,1/e)],6)
false.
==
As with any application requiring numerical integration, care must be taken to avoid instability problems (more discussion in [A Guide to CLP(BNR)](https://ridgeworks.github.io/clpBNR/CLP_BNR_Guide/CLP_BNR_Guide.html).
*/
boundary_values(X,YDefs) :-
	current_prolog_flag(clpBNR_default_precision,P),
	boundary_values_(X,YDefs,P,_).
	
boundary_values(X,YDefs,P) :-
	boundary_values_(X,YDefs,P,_).

boundary_values(X,YDefs,P,Steps) :-
	boundary_values_(X,YDefs,P,Steps/_).

boundary_values_(X,YDefs,P,Out/[(Xf,Yfs)]) :-
    integer(P), P>0,                             % P must be positive integer
    domain(X,Xdom), Xdom =.. [_Type,Xi,Xf],      % X must be an interval 
	eval_dvars(YDefs,Ys,Yis,Yfs,Ydoms),          % too many args for maplist	
	maplist(fXY_lambda(X,Ys),YDefs,Fxys),        % list of partial derivative lambda args
	(maplist(total_derivative_(Fxys),Fxys,DFxys) % list of connective derivative lambda args
	 -> true
	 ;  DFxys = none                             % F non-differentiable(?), use euler step
	),
	!,                                           % args all good, commit
    integrate_(P,Fxys,DFxys,(Xi,Yis),(Xf,Yfs),Ydoms,Out/[(Xf,Yfs)]).
boundary_values_(X,YDefs,P,_) :-
	fail_msg_('Invalid argument(s): ~w',[boundary_values(X,YDefs,P)]).

eval_dvars([],[],[],[],[]).
eval_dvars([dV(Y, _PD, Lexp, Uexp)|YDefs],[Y|Ys],[Yi|Yis],[Yf|Yfs],[Ydom|Ydoms]) :-
	(domain(Y,Ydom) -> true ; Ydom = real),  % Ydom defaults to real 
	(var(Lexp) -> Yi=Lexp, Yi::Ydom ; Yi is Lexp),
	(var(Uexp) -> Yf=Uexp, Yf::Ydom ; Yf is Uexp),
	eval_dvars(YDefs,Ys,Yis,Yfs,Ydoms).

% construct Lambda args for Fxy
fXY_lambda(X,Ys,dV(_Y,Fxy,_,_),FxyArgs) :- 
	lambda_for_(Fxy,X,Ys,FxyArgs).

% construct Lambda args for derivative function of Fxy from Lambda of Fxy

total_derivative_(Fxys,_Free/Ps,DxyArgs) :- !,  % ignore free variables
	total_derivative_(Fxys,Ps,DxyArgs).
total_derivative_(Fxys,[X,Ys,Fxy],DxyArgs) :-
	partial_derivative(Fxy,X,DFDX),          % clpBNR built-in
	sumYpartials(Fxys,Ys,Fxy,0,DYsum),
	simplify_sum_(DFDX, DYsum, DExp), !,
	lambda_for_(DExp,X,Ys,DxyArgs).
	
sumYpartials([],[],_Fxy,Acc,Acc).
sumYpartials([_Free/FxyI|FxyIs],YIs,Fxy,Acc,Sum) :- !,
	sumYpartials([FxyI|FxyIs],YIs,Fxy,Acc,Sum).
sumYpartials([[_X,_Ys,FxyI]|FxyIs],[YI|YIs],Fxy,Acc,Sum) :-
	partial_derivative(Fxy,YI,DFDYI),
	(number(DFDYI), DFDYI =:= 0 -> NxtAcc = Acc ; simplify_sum_(Acc,FxyI*DFDYI,NxtAcc)),
	!,
	sumYpartials(FxyIs,YIs,Fxy,NxtAcc,Sum).

simplify_sum_(X,Y,Y) :- number(X),X=:=0.
simplify_sum_(X,Y,X) :- number(Y),Y=:=0.
simplify_sum_(X,Y,X+Y).

% construct args for Lambda expression
lambda_for_(Fxy,X,Ys,Args) :-
	Lambda_parms = [X,Ys,Fxy],
	term_variables(Fxy,FVs),
	exclude(var_member_([X|Ys]),FVs,EVs),    % EVs = free variables
	(comma_op_(EVs,EV) -> Args = {EV}/Lambda_parms ; Args = Lambda_parms).

var_member_([L|Ls],E) :- L==E -> true ; var_member_(Ls,E).

comma_op_([X],X).  % assumes use in if-then
comma_op_([X|Xs],(X,Y)) :- comma_op_(Xs,Y).	

% integration loop
integrate_(0, Fxys, Dxys, Initial, Final, Ydomains, [Initial|Ps]/Ps) :- !,
	% select integration step
	( Dxys == none
	 -> step_euler(Fxys, Initial, Final, Ydomains)
	 ;  step_trap(Fxys, Dxys, Initial, Final, Ydomains)
	).
integrate_(P, Fxys, Dxys, Initial, Final, Ydomains, L/E) :-
    % create interpolation point and integrate two halves
    interpolate_(Initial, Final, Ydomains, Middle),
    Pn is P - 1,
    integrate_(Pn, Fxys, Dxys, Initial, Middle, Ydomains, L/M),
    integrate_(Pn, Fxys, Dxys, Middle,  Final,  Ydomains, M/E).

interpolate_((X0,_Y0s), (X1,_Y1s), Ydomains, (XM,YMs)) :-
    XM is (X0 + X1)/2,            % XM is midpoint of (X0,X1)
	maplist(::,YMs,Ydomains).     % corresponding YMs

step_euler(Fxys, (X0,Y0), (X1,Y1), Ydoms) :-
    X01:: real(X0,X1),            % range of X in step
    maplist(lambda_constrain_(X01,Y01),Fxys,Fs),   % approx f' over X0 
    Dx is X1 - X0,                % assumed (X1>X0)
    DX :: real(0,Dx),             % range for estimate
	euler_constraints(Y0,Y1,Y01,Ydoms,Dx,DX,Fs,In/In,Cs/[]),  % flatten with diff list
	{Cs}.
	
step_trap(Fxys, Dxys, (X0,Y0), (X1,Y1), Ydoms) :-
    X01:: real(X0,X1),            % range of X in step
    maplist(lambda_constrain_(X0,Y0),Fxys,F0s),    % F0s = slopes at X0
    maplist(lambda_constrain_(X1,Y1),Fxys,F1s),    % F1s = slopes at X1 
    maplist(lambda_constrain_(X01,Y01),Dxys,Ds),   % approx f' over X0 
    Dx is X1 - X0,                % assumed (X1>X0)
    DX :: real(0,Dx),             % range for estimate
	trap_constraints(Y0,Y1,Y01,Ydoms,Dx,DX,F0s,F1s,Ds,In/In,Cs/[]),  % flatten with diff list
	{Cs}.  %%, absolve(Y1,2).

lambda_constrain_(X,Ys,Args,F) :-  % reorder args for yall: >>
	yall: >>(Args,true,X,Ys,F).    % avoid meta-call (basically just makes copy)
%  known safe since lambda Goal=true
sandbox:safe_primitive(clpBNR_toolkit:lambda_constrain_(_X,_Ys,_Args,_F)). 

/* see Carleton notes:
https://www.softwarepreservation.org/projects/prolog/bnr/doc/Older-Introduction_to_CLP%28BNR%29-1995.pdf/view
*/
euler_constraints([],[],[],[],_Dx,_DX,[],In,In).
euler_constraints([Y0|Y0s],[Y1|Y1s],[Y01|Y01s],[Ydom|Ydoms],Dx,DX,[F|Fs],
	In/[FM <= F,                      % FM = slope inclusion 
	    Y01 - Y0 is DX*FM,
	    Y1  - Y0 is Dx*FM
	   |Cs],
	Out) :-
	Y01:: Ydom,
	euler_constraints(Y0s,Y1s,Y01s,Ydoms,Dx,DX,Fs,In/Cs,Out).

trap_constraints([],[],[],[],_Dx,_DX,[],[],[],In,In).
trap_constraints([Y0|Y0s],[Y1|Y1s],[Y01|Y01s],[Ydom|Ydoms],Dx,DX,[F0|F0s],[F1|F1s],[D|Ds],
	% use `is` to circumvent `simplify`
	In/[FM <= (F0+F1)/2,              % FM = average slope using step endpoints (one-way)
	    % Note that the following must not be symbolically simplified to eliminate D
	    8*DR is D - D,                % 4*deltaR == (D-D)/2 (for error term)
	    Y01 - Y0 is DX*(FM + DR*DX),
	    Y1  - Y0 is Dx*(FM + DR*Dx)
	   |Cs],
	Out) :-
	Y01:: Ydom, DR::real,
	trap_constraints(Y0s,Y1s,Y01s,Ydoms,Dx,DX,F0s,F1s,Ds,In/Cs,Out).

/**
lin_minimum(+ObjF,Constraints:{},?Min:numeric) is semidet

Succeeds if the global minimum value of the objective function ObjF subject to Constraints can be unified with Min; otherwise fails. Both the objective function and Constraints must be linear, i.e., only subexpressions summing of the form =|X*C|= (or =|C*X|=) are permitted since the actual computation is done using =|library(simplex)|=. Narrowing of minimizers (variables in ObjF) is limited to that constrained by the Min result to accomodate multiple sets of minimizers. (See =|lin_minimize/3|= to use minimizers used to derive Min.) A solution generator, e.g., =|clpBNR:solve/1|= can be used to search for alternative sets of minimizers. "Universal Mines" example from the User Guide:
==
?- [M_Idays,M_IIdays,M_IIIdays]::integer(0,7),
lin_minimum(20*M_Idays+22*M_IIdays+18*M_IIIdays,
{4*M_Idays+6*M_IIdays+M_IIIdays>=54,4*M_Idays+4*M_IIdays+6*M_IIIdays>=65}, Min).
Min = 284,
M_Idays::integer(2, 7),
M_IIdays::integer(4, 7),
M_IIIdays::integer(2, 7).

?- [M_Idays,M_IIdays,M_IIIdays]::integer(0,7),
lin_minimum(20*M_Idays+22*M_IIdays+18*M_IIIdays,
{4*M_Idays+6*M_IIdays+M_IIIdays>=54,4*M_Idays+4*M_IIdays+6*M_IIIdays>=65}, Min),
solve([M_Idays,M_IIdays,M_IIIdays]).
M_Idays = 2,
M_IIdays = 7,
M_IIIdays = 5,
Min = 284 ;
false.
==

For linear systems, =|lin_minimum/3|=, =|lin_maximum/3|= can be significantly faster than using the more general purpose =|clpBNR:global_minimum/3|=, =|clpBNR:global_maximum/3|=

@see =|lin_minimize/3|=, =|library(simplex)|= 
*/
/**
lin_maximum(+ObjF,Constraints:{},?Max:numeric) is semidet

Succeeds if the global minimum value of the objective function ObjF subject to Constraints can be unified with Max; otherwise fails. This is the corresponding predicate to =|lin_minimum/3|= for finding global maxima.

@see =|lin_minimum/3|=, =|lin_maximize/3|=
*/
lin_minimum(ObjF,{Constraints},MinValue) :-
	lin_minimum_(ObjF,{Constraints},MinValue,false).

lin_maximum(ObjF,{Constraints},MinValue) :-
	lin_maximum_(ObjF,{Constraints},MinValue,false).
/**
lin_minimize(+ObjF,Constraints:{},?Min:numeric) is semidet

Succeeds if the global minimum value of the objective function ObjF subject to Constraints can be unified with Min; otherwise fails. This behaves identically to =|lin_minimum/3|= except variables in ObjF will be narrowed to the values used in calculating the final value of Min. Any other sets of minimizers corresponding to Min are removed from the solution space. "Universal Mines" example from the User Guide:
==
?- [M_Idays,M_IIdays,M_IIIdays]::integer(0,7),
lin_minimize(20*M_Idays+22*M_IIdays+18*M_IIIdays,
{4*M_Idays+6*M_IIdays+M_IIIdays>=54,4*M_Idays+4*M_IIdays+6*M_IIIdays>=65}, Min).
M_Idays = 2,
M_IIdays = 7,
M_IIIdays = 5,
Min = 284.
==
@see =|lin_minimum/3|=
*/
/**
lin_maximize(+ObjF,Constraints:{},?Max:numeric) is semidet

Succeeds if the global maximum value of the objective function ObjF subject to Constraints can be unified with Max; otherwise fails. This behaves identically to =|lin_maximum/3|= except variables in ObjF will be narrowed to the values used in calculating the final value of Max. Any other sets of minimizers corresponding to Min are removed from the solution space.

@see =|lin_maximum/3|=
*/
lin_minimize(ObjF,{Constraints},MinValue) :-
	lin_minimum_(ObjF,{Constraints},MinValue,true).

lin_maximize(ObjF,{Constraints},MinValue) :-
	lin_maximum_(ObjF,{Constraints},MinValue,true).
	

lin_minimum_(ObjF,{Constraints},MinValue,BindVars) :-
	init_simplex_(ObjF,Constraints,Objective,S0,Vs),
	(minimize(Objective,S0,S)
	 -> objective(S,MinValue), {ObjF == MinValue},
	    (BindVars == true
	     -> bind_vars_(Vs,S)
	     ;  remove_names_(Vs),
	        {Constraints}  % apply constraints
	    )
	 ;  fail_msg_('Failed to minimize: ~w',[ObjF])
	).
	
lin_maximum_(ObjF,{Constraints},MaxValue,BindVars) :-
	init_simplex_(ObjF,Constraints,Objective,S0,Vs),
	(maximize(Objective,S0,S)
	 -> objective(S,MaxValue), {ObjF == MaxValue},
	    (BindVars == true
	     -> bind_vars_(Vs,S)
	     ;  remove_names_(Vs),
	        {Constraints}  % apply constraints
	    )
	 ;  fail_msg_('Failed to maximize: ~w',[ObjF])
	).

init_simplex_(ObjF,Constraints,Objective,S,Vs) :-
	gen_state(S0),
	term_variables((ObjF,Constraints),Vs),
	(Vs = []
	 -> fail_msg_('No variables in expression to optimize: ~w',[ObjF])
	 ;  sim_constraints_(Constraints,S0,S1),
	    _::real(_,Max),  % max value to constrain for simplex
	    constrain_ints_(Vs,Max,S1,S),
	    (map_simplex_(ObjF,T/T,Objective/[])
	     -> true
	     ;  fail_msg_('Illegal linear objective: ~w',[ObjF])
	    )
	).

% use an attribute to associate a var with a unique simplex variable name
simplex_var_(V,SV) :- var(V),
	(get_attr(V,clpBNR_toolkit,SV)
	 -> true
	 ;  statistics(inferences,VID), SV = var(VID), put_attr(V,clpBNR_toolkit,SV)
	).

% Name attribute removed before exit.
remove_names_([]).
remove_names_([V|Vs]) :-
	del_attr(V,clpBNR_toolkit),
	remove_names_(Vs).
		 
attr_unify_hook(var(_),_).     % unification always does nothing and succeeds

constrain_ints_([],_,S,S).
constrain_ints_([V|Vs],Max,Sin,Sout) :- 
	% Note: library(simplex) currently constrains all variables to be non-negative
	simplex_var_(V,SV),               % corresponding simplex variable name
	% if not already an interval, make it one with finite non-negative value
	(domain(V,D) -> true ; V::real(0,_), domain(V,D)),
	(D == boolean -> Dom = integer(0,1); Dom = D),
	Dom =.. [Type,L,H],
	(Type == integer -> constraint(integral(SV),Sin,S1) ; S1 = Sin),
	(L < 0
	 -> % apply non-negativity condition    
	    ({V >= 0} -> L1 = 0 ; fail_msg_('Negative vars not supported by \'simplex\': ~w',[V]))
	 ;  L1 = L
	),
	% explicitly constrain any vars not (0,Max-eps)
	(L1 > 0   -> constraint([SV] >= L1,S1,S2)   ; S2 = S1),    % L1 not negative
	(H  < Max -> constraint([SV] =< H,S2,SNxt)  ; SNxt = S2),
	constrain_ints_(Vs,Max,SNxt,Sout).

bind_vars_([],_).
bind_vars_([V|Vs],S) :-  
	% Note: skip anything nonvar (already bound due to active constraints)
	(simplex_var_(V,SV) -> variable_value(S,SV,V) ; true),
	bind_vars_(Vs,S).

% clpBNR constraints have already been applied so worst errors have been detected
sim_constraints_([],S,S) :- !.
sim_constraints_([C|Cs],Sin,Sout) :- !,
	sim_constraints_(C, Sin,Snxt),
	sim_constraints_(Cs,Snxt,Sout).
sim_constraints_((C,Cs),Sin,Sout) :-  !,
	sim_constraints_(C, Sin,Snxt),
	sim_constraints_(Cs,Snxt,Sout).
sim_constraints_(C,Sin,Sout) :- 
	sim_constraint_(C,SC),
	constraint(SC,Sin,Sout).  % from simplex

sim_constraint_(C,SC) :-
	C=..[Op,LHS,RHS],              % decompose
	constraint_op(Op,COp),         % acceptable to simplex
	number(RHS), RHS >= 0,         % requirement of simplex
	map_simplex_(LHS,T/T,Sim/[]),  % map to simplex list of terms
	!,
	SC=..[COp,Sim,RHS].            % recompose
sim_constraint_(C,_) :-
	fail_msg_('Illegal linear constraint: ~w',[C]).	

map_simplex_(T,CT/[S|Tail],CT/Tail) :-
	map_simplex_term_(T,S),
	!.
map_simplex_(A+B,Cin,Cout) :- !,
	map_simplex_(A,Cin,Cnxt),
	map_simplex_(B,Cnxt,Cout).
map_simplex_(A-B,Cin,Cout) :- !,
	map_simplex_(A,Cin,Cnxt),
	map_simplex_(-B,Cnxt,Cout).
			
map_simplex_term_(V,1*SV)   :- simplex_var_(V,SV), !.
map_simplex_term_(-T,NN*V)  :- !,
	map_simplex_term_(T,N*V),
	NN is -N.
map_simplex_term_(N*V,N*SV) :- number(N), simplex_var_(V,SV), !.
map_simplex_term_(V*N,N*SV) :- number(N), simplex_var_(V,SV).

constraint_op(==,=).
constraint_op(=<,=<).
constraint_op(>=,>=).

/**
local_minima(+ObjF) is semidet

Succeeds if the value of objective function ObjF can be constrained to be a local minimum, i.e, it's "slope" is 0 in every dimension; otherwise fails. This requires that a partial derivative of ObjF exists for each variable. =local_minima= should be executed prior to a call to =|clpBNR:global_minimum|= using the same objective function, e.g.,
==
?- X::real(0,10), OF=X**3-6*X**2+9*X+6, local_minima(OF), global_minimum(OF,Z).
OF = X**3-6*X**2+9*X+6,
X:: 3.00000000000000...,
Z:: 6.000000000000... .
==
Using any local optima predicate can significantly improve performance compared to searching for global optima (`clpBNR:global_`*) without local constraints.

@see =|clpBNR:local_minima/2|=
*/
/**
local_maxima(+ObjF) is semidet

Succeeds if the value of objective function ObjF can be constrained to be a local maximum, i.e, it's "slope" is 0 in every dimension; otherwise fails. This requires that a partial derivative of ObjF exists for each variable. =local_maxima= should be executed prior to a call to =|clpBNR:global_maximum|= using the same objective function, e.g.,
==
?- X::real(0,10), OF=X**3-6*X**2+9*X+6, local_maxima(OF), global_maximum(OF,Z).
OF = X**3-6*X**2+9*X+6,
X:: 1.000000000000000...,
Z:: 10.0000000000000... .
==
@see =|clpBNR:local_maxima/2|=
*/
%
%	local_minima/1,       % apply KT constraints for objective function expression (OFE)
%	local_maxima/1,       % semantically equivalent to local_minima/1
%
local_minima(ObjExp) :-
	local_optima_(min,ObjExp,[]).

local_maxima(ObjExp) :-
	local_optima_(max,ObjExp,[]).
/**
local_minima(+ObjF,+Constraints:{}) is semidet

Succeeds if the value of objective function ObjF can be constrained to be a local minimum, i.e, it's "slope" is 0 in every dimension, subject to Constraints; otherwise fails. This requires that a partial derivative of ObjF, and any subexpression in Constraints, exists for each variable. =local_minima= should be executed prior to a call to =|clpBNR:global_minimum|= using the same objective function, e.g.,
==
?- [X1,X2]::real, OF=X1**4*exp(-0.01*(X1*X2)**2),
local_minima(OF,{2*X1**2+X2**2==10}), global_minimum(OF,Z), solve([X1,X2]).
OF = X1**4*exp(-0.01*(X1*X2)**2),
X1::real(-1.703183936003284e-108, 1.703183936003284e-108),
X2:: -3.16227766016838...,
Z:: 0.0000000000000000... ;
OF = X1**4*exp(-0.01*(X1*X2)**2),
X1::real(-1.703183936003284e-108, 1.703183936003284e-108),
X2:: 3.16227766016838...,
Z:: 0.0000000000000000... .
==

@see =|clpBNR:local_minima/1|=
*/
/**
local_maxima(+ObjF,+Constraints:{}) is semidet

Succeeds if the value of objective function ObjF can be constrained to be a local maximum, i.e, it's "slope" is 0 in every dimension; otherwise fails. This requires that a partial derivative of ObjF, and any subexpression in Constraints, exists for each variable. =local_maxima= should be executed prior to a call to =|clpBNR:global_maximum|= using the same objective function, e.g.,
==
?- [X1,X2]::real,OF=X1**4*exp(-0.01*(X1*X2)**2),
local_maxima(OF,{2*X1**2+X2**2==10}), global_maximum(OF,Z),solve([X1,X2]).
OF = X1**4*exp(-0.01*(X1*X2)**2),
X1:: -2.23606797749979...,
X2:: 0.0000000000000000...,
Z:: 25.0000000000000... ;
OF = X1**4*exp(-0.01*(X1*X2)**2),
X1:: 2.23606797749979...,
X2:: 0.0000000000000000...,
Z:: 25.0000000000000... .
==

@see =|clpBNR:local_maxima/1|=
*/
%
%	local_minima/2,       % apply KT constraints for minima with constraints
%	local_maxima/2        % apply KT constraints for maxima with constraints
%
local_minima(ObjExp,{Constraints}) :-
	local_optima_(min,ObjExp,Constraints).
	
local_maxima(ObjExp,{Constraints}) :-
	local_optima_(max,ObjExp,Constraints).
	
	
local_optima_(MinMax,ObjF,Constraints) :-
	local_optima_(MinMax,ObjF,Constraints,Cs),  % generate constraints
	{Cs}.                                       % then apply

local_optima_(MinMax,ObjF,Constraints,[Constraints,GCs,LCs]) :-
	lagrangian_(Constraints,MinMax,ObjF,LObjF,LCs),
	term_variables((Constraints,ObjF),Vs),
	gradient_constraints_(Vs,GCs,LObjF).

gradient_constraints_([],[],_Exp).
gradient_constraints_([X|Xs],[C|Cs],Exp) :-
	partial_derivative(Exp,X,D),
	(number(D) -> C=[] ; C=(D==0)),  % no constraint if PD is a constant
	gradient_constraints_(Xs,Cs,Exp).
	
% for each constraint add to Lagrangian expression with auxiliary KKT constraints
lagrangian_(C,MinMax,Exp,LExp, LC) :- nonvar(C),
	kt_constraint_(C,CExp, LC), % generate langrange term with multiplier
	lexp(MinMax,Exp,CExp,LExp),
	!.
lagrangian_([],_,L,L,[]).
lagrangian_([C|Cs],MinMax,Exp,LExp,[LC|LCs]) :-
	lagrangian_(C, MinMax,Exp,NExp,LC),
	lagrangian_(Cs,MinMax,NExp,LExp,LCs).	
lagrangian_((C,Cs),MinMax,Exp,LExp,[LC|LCs]) :-
	lagrangian_(C,MinMax,Exp,NExp,LC),
	lagrangian_(Cs,MinMax,NExp,LExp,LCs).
		
lexp(min,Exp,CExp,Exp+CExp).
lexp(max,Exp,CExp,Exp-CExp).

kt_constraint_(LHS == RHS, M*(LHS-RHS), []) :-
	M::real.                          % finite multiplier only
kt_constraint_(LHS =< RHS, MGx,     MGx==0) :-
	MGx = M*(LHS-RHS), M::real(0,_).  % positive multiplier and KKT non-negativity condition
kt_constraint_(LHS >= RHS, Exp,         LC) :-
	kt_constraint_(RHS =< LHS, Exp, LC).  % >= convert to =<
