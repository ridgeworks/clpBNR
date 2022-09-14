%
% Toolkit of useful utilities for CLP(BNR)
%
/*	The MIT License (MIT)
 *
 *	Copyright (c) 2022 Rick Workman
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
	
	lin_minimum/3,              % find minimum of linear problem using library(simplex)
	lin_maximum/3,              % find maximum of linear problem using library(simplex)
	lin_minimize/3,             % lin_minimum/3 plus bind vars to solution minimizers
	lin_maximize/3,             % lin_maximum/3 plus bind vars to solution maximizers

	local_minima/1,             % apply KT constraints for objective function expression (OFE)
	local_maxima/1,             % semantically equivalent to local_minima/1
	local_minima/2,             % apply KT constraints for minima with constraints
	local_maxima/2              % apply KT constraints for maxima with constraints
	]).
	
:- use_module(library(apply),[maplist/3]).
:- current_module(clpBNR) -> true ; use_module(library(clpBNR)).
:- current_module(simplex) -> true ; use_module(library(simplex)).

% messages for noisy failure
fail_msg_(FString,Args) :-
	debug(clpBNR,FString,Args), fail.

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
%
% contractor to split largest interval of a list on midpoint
%
mid_split_one(Xs) :-
	select_split(Xs,X),  % select largest interval with largest width
	mid_split(X).        % split it
%
% contractor to split a single interval on midpoint if sufficiently wide (creates a choicepoint)
%
mid_split(X) :- small(X), !. % too narrow to split
mid_split(X) :-
	M is midpoint(X),
	({X=<M} ; {M=<X}).
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
%
% centred form contractor
%
% Bind the values of As to the midpoints of Xs. To support repetitive application 
% of the contractor (required by the iterator), the contractor should not permanently 
% bind anything so findall/3 will be used to achieve this "forward checking" 
% (as suggested in [CLIP]). After the call to findall, 'XDs' is a list of narrowed domains
% of Xs and are then applied to Xs.
%
% This contractor can be used with any "centred form", e.g., Newton or Krawczyk, since it
% only depends on intervals and their midpoints, hence its name `cf_contractor`. The 
% details which distinguish the variety of centred form are built into the variables' 
% constraints.
%
cf_contractor(Xs,As) :-
	findall(Ds,(maplist(bind_to_midpoint,Xs,As),maplist(cf_domain,Xs,Ds)),[XDs]),
	maplist(::,Xs,XDs).
	
bind_to_midpoint(X,A) :- A is float(midpoint(X)).

cf_domain(X,D) :- 
	number(X) -> D = real(X,X) ; domain(X,D).  % in case X narrowed to a point
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
taylor_contractor(Eq,_) :-
	fail_msg_('Invalid equation for Taylor contractor: ~w',[Eq]).

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
cf_list((C,Cs),[CF,CFs]) :-  !,
	cf_list(C, CF),
	cf_list(Cs,CFs).
cf_list(C,CF) :-
	taylor_contractor({C},CF).

cf_merge(CFs,CF) :- cf_merge(CFs,cf_contractor([],[]),CF).

cf_merge([],CF,CF).
cf_merge([cf_contractor(Xs,As)|CFs],cf_contractor(XsIn,AsIn),CF) :-
	cf_add(Xs,As,XsIn,AsIn,XsOut,AsOut),
	cf_merge(CFs,cf_contractor(XsOut,AsOut),CF).

cf_add([],[],Xs,As,Xs,As).
cf_add([X|Xs],[A|As],XsIn,AsIn,XsOut,AsOut) :-
	var_existing(XsIn,AsIn,X,A), !,
	cf_add(Xs,As,XsIn,AsIn,XsOut,AsOut).
cf_add([X|Xs],[A|As],XsIn,AsIn,XsOut,AsOut) :-
	cf_add(Xs,As,[X|XsIn],[A|AsIn],XsOut,AsOut).

var_existing([Xex|_], [A|_],   X,A) :- Xex==X, !.
var_existing([_|XsIn],[_|AsIn],X,A) :- var_existing(XsIn,AsIn,X,A).

%
%	lin_minimum/3         % find minimum of linear problem using library(simplex)
%	lin_maximum/3         % find maximum of linear problem using library(simplex)
%
lin_minimum(ObjF,{Constraints},MinValue) :-
	lin_minimum_(ObjF,{Constraints},MinValue,false).

lin_maximum(ObjF,{Constraints},MinValue) :-
	lin_maximum_(ObjF,{Constraints},MinValue,false).
%
%	lin_minimize/3,       % lin_minimum/3 and bind vars to generated solution
%	lin_maximize/3,       % lin_maximum/3 and bind vars to generated solution
%	
lin_minimize(ObjF,{Constraints},MinValue) :-
	lin_minimum_(ObjF,{Constraints},MinValue,true).

lin_maximize(ObjF,{Constraints},MinValue) :-
	lin_maximum_(ObjF,{Constraints},MinValue,true).
	

lin_minimum_(ObjF,{Constraints},MinValue,BindVars) :-
	init_simplex_(ObjF,Constraints,Objective,S0,Vs),
	(minimize(Objective,S0,S)
	 -> objective(S,MinValue), {ObjF == MinValue},
	    (BindVars
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
	    (BindVars
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
	    constrain_ints_(Vs,S1,S),
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

	
constrain_ints_([],S,S).
constrain_ints_([V|Vs],Sin,Sout) :- 
	% Note: library(simplex) currently constrains all variables to be non-negative
	simplex_var_(V,SV),               % corresponding simplex variable name
	% if not already an interval, make it one with finite non-negative value
	(domain(V,D) -> true ; V::real(0,_), domain(V,D)),
	(D == boolean -> Dom = integer(0,1); Dom = D),
	Dom =.. [Type,L,_],
	(Type == integer -> constraint(integral(SV),Sin,S1) ; S1 = Sin),
	(L < 0
	 -> ({V >= 0}                     % apply non-negativity condition
	     -> S2 = S1
	     ;  fail_msg_('Negative vars not supported by \'simplex\': ~w',[V])
	    )
	 ;  (L =:= 0 -> S2 = S1 ; constraint([SV] >= L,S1,S2))  % non-zero Lbound constraint
	),
	constrain_ints_(Vs,S2,Sout).

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

%
%	local_minima/1,       % apply KT constraints for objective function expression (OFE)
%	local_maxima/1,       % semantically equivalent to local_minima/1
%
local_minima(ObjExp) :-
	local_optima_(min,ObjExp,[]).

local_maxima(ObjExp) :-
	local_optima_(max,ObjExp,[]).
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

