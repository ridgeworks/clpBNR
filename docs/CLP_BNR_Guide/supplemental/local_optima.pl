% Unconstrained optimization (just the objective function)
local_optima(ObjF) :-
	local_optima(_,ObjF,[]).

% Constrained optimization - have to specify whether searching for a `min` or `max`		
local_optima(MinMax,ObjF,Constraints) :-
	local_optima(MinMax,ObjF,Constraints,Cs),  % generate constraints
	{Cs}.                                      % then apply

local_optima(MinMax,ObjF,Constraints,[Constraints,GCs,LCs]) :-
	lagrangian_(Constraints,MinMax,ObjF,LObjF,LCs),
	term_variables(Constraints+ObjF,Vs),
	gradient_constraints_(Vs,GCs,LObjF).

gradient_constraints_([],[],_Exp).
gradient_constraints_([X|Xs],[C|Cs],Exp) :-
	partial_derivative(Exp,X,D),
	(number(D) -> C=[] ; C=(D==0)),  % no constraint if PD is a constant
	gradient_constraints_(Xs,Cs,Exp).
	
% for each constraint add to Lagrangian expression with auxiliary KKT constraints
lagrangian_([],_,L,L,[]).
lagrangian_([C|Cs],MinMax,Exp,L,[LC|LCs]) :-
	constrain_(C,CExp, LC), % generate langrange term with multiplier
	lexp(MinMax,Exp,CExp,LExp), !,
	lagrangian_(Cs,MinMax,LExp,L,LCs).
		
lexp(min,Exp,CExp,Exp+CExp).
lexp(max,Exp,CExp,Exp-CExp).

constrain_(LHS == RHS, M*(LHS-RHS), []) :-
	M::real.                          % finite multiplier only
constrain_(LHS =< RHS, MGx,     MGx==0) :-
	MGx = M*(LHS-RHS), M::real(0,_).  % positive multiplier and KKT non-negativity condition
constrain_(LHS >= RHS, Exp,         LC) :-
	constrain_(RHS =< LHS, Exp, LC).  % >= convert to =<
