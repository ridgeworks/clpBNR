:- discontiguous weights/2, values/2, demands/2.

% 11 possible Load configs, MaxLoad=3 items
weights(3, [30,20,50]).
values( 3, [90,70,20]).
demands(3, [12,7,15]).

% 27 possible Load configs, MaxLoad=2 items
weights(15, [97,74,39,75,22,
	 61,45,64,41,37,
	 56,75,99,84,42]).

values(15, [57,47,92,131,186,
	53,173,67,26,170,
	81,96,159,48,36]).

demands(15, [48,46,80,13,57,
	 66,39,38,78,16,
	 38,39,33,34,18]).

% 900 possible Load configs, MaxLoad=11 items
weights(21, [14,51,78,83,89,63,80,62,23,11,45,68,42,91,92,82,65,39,6,1,64]).
values( 21, [25,9,11,71,82,86,45,80,66,79,34,94,42,83,64,37,92,47,76,18,85]).
demands(21, [29,76,73,41,70,71,94,80,78,55,20,62,27,85,34,67,79,51,64,49,24]).

% 107 possible Load configs, MaxLoad=4 items
weights(25, [97,74,39,75,22,
	 61,45,64,41,37,
	 56,75,99,84,42,
	 14,38,54,97,9,
	 55,75,47,57,91]).

values(25, [57,47,92,131,186,
	53,173,67,26,170,
	81,96,159,48,36,
	47,25,174,9,111,
	194,172,124,113,170]).

demands(25, [48,46,80,13,57,
	 66,39,38,78,16,
	 38,39,33,34,18,
	 50,22,74,64,65,
	 34,86,14,69,41]).
	 

% define what a camel can do
camel(Weights,Values,Load,Count) :-
	length(Weights,L), 
	length(Load,L), Load::integer(0,_),  % Load is list of item counts
	Weight::integer(1,100),  % weight can't exceed 100 but must be > 0
	sym_sum_prod(Load,Weights,SumW),
	{Weight == SumW},
	Value::integer(1,200),   % value can't exceed 200 but must be > 0
	sym_sum_prod(Load,Values,SumV),	
	{Value == SumV},
	Count::integer(1,_),     % total load (number of items of any kind)
	sym_sum_list(Load,SumL),
	{Count == SumL}.

sym_sum_list([X],X) :- !.
sym_sum_list([X|Xs],X+XS) :-
	sym_sum_list(Xs,XS).

sym_sum_prod([X],[Y],X*Y) :- !.
sym_sum_prod([X|Xs],[Y|Ys],X*Y+SPS) :-
	sym_sum_prod(Xs,Ys,SPS).

%setup_camels_(Items,Total,Weights,Values,MaxCount) :- 
setup_camels_(Items,Total,Weights,Values) :- 
	length(Items,L),
	weights(L,Weights),
	values(L,Values),
	lists:sum_list(Items,Total).

% reduce result to a Load list and total for output
accumulate_camels_([],[],Total,Total).
accumulate_camels_([(_,L)|Camels],CCamels,Acc,Total) :- !,
	accumulate_camels_([1*L|Camels],CCamels,Acc,Total).
accumulate_camels_([0*_|Camels],CCamels,Acc,Total) :- !,
	accumulate_camels_(Camels,CCamels,Acc,Total).	
accumulate_camels_([N*L,(_,L)|Camels],CCamels,Acc,Total) :- !,
	N1 is N+1,
	accumulate_camels_([N1*L|Camels],CCamels,Acc,Total).
accumulate_camels_([N*L|Camels],[N*L|CCamels],Acc,Total) :-
	AccN is Acc+N,
	accumulate_camels_(Camels,CCamels,AccN,Total).

%	For example:
% ?- demands(3,Items), pack_camels(Items,Camels,Required).
% Items = [12, 7, 15],
% Camels = [4*[0, 0, 2], 1*[1, 0, 1], 3*[2, 0, 0], 1*[0, 2, 1], 5*[1, 1, 1]],
% Required = 14.
%
pack_camels(Items,CamelSpec,Required) :-
	setup_camels_(Items,Total,Weights,Values),
	camel_load_(Total,Items,Weights,Values,Camels),  % incrementally adds camels as needed
	camels_ordered_(Camels),        % order list to break order symmetry
	enum_camels(Camels), !,  % commit to first solution
	msort(Camels,SCamels),   % sort result by load count for output
	accumulate_camels_(SCamels,CamelSpec,0,Required).

% load additional camels until residual item count reaches 0
% camel load defined by (Count,Load) where Count is sum of Load elements
camel_load_(0,Items,_,_,[]) :-
	zero_list_(Items).
camel_load_(Total,Items,Weights,Values,[(Count,Load)|Camels]) :-
	camel(Weights,Values,Load,Count),          % new camel
	{NxtTotal == Total-Count, NxtTotal >= 0},  % reduces total item count
	subtract_clp(Items,Load,Residual),         % and count of each item type
	camel_load_(NxtTotal,Residual,Weights,Values,Camels).  % adds more as needed

zero_list_([]).
zero_list_([0|Items]) :- zero_list_(Items).

subtract_clp([], [], []).
subtract_clp([X|Xs], [Y|Ys], [Z|Zs]) :-
	{Z == X - Y, Z >= 0},  % can't get to -ve items
	subtract_clp(Xs,Ys,Zs).

camels_ordered_([_]) :- !.         % finish with one item
camels_ordered_([X,Y|Xs]) :-
	order_camels(X,Y),      % order constraint on first two items
	camels_ordered_([Y|Xs]).       % order second and remaining items

order_camels((C1,_L1), (C2,_L2)) :- {C1>=C2}.  % constrain camel order by carried items

% enumerate camel loads to find a solution which meets constraints
enum_camels([]).
enum_camels([(_Count,Load)|Camels]) :-
	enumerate(Load),  % standard clpBNR enumerate from L to H, H to L might be faster?
	enum_camels(Camels).


%	For example:
% ?- demands(3,Items), fastpack_camels(Items,Camels,Required).
% Items = [12, 7, 15],
% Camels = [4*[0, 0, 2], 1*[1, 0, 1], 3*[2, 0, 0], 1*[0, 2, 1], 5*[1, 1, 1]],
% Required = 14.
%
fastpack_camels(Items,CamelSpec,Required) :-
	setup_camels_(Items,_Total,Weights,Values),  % process input data
	% generate possible load patterns
	findall(Load, (camel(Weights,Values,Load,_Count),enumerate(Load)), Loads),
	% use Items and Loads to define linear objective expression and constraints 
	camels_lin_summation(Items,Loads,NC,Obj,Constraints),
	lin_minimize(Obj,{Constraints},_Min),         % and minimize
	accumulate_camels_(NC,CamelSpec,0,Required).  % format for output

camels_lin_summation(Items,Loads,NC,Obj,Constraints) :-
	map_camel_loads(Loads,Ns,NC),  % lists of pattern counts
	sym_sum_list(Ns,Obj),          % Objective function is sum of counts
	length(Items,TLen),            % construct constraint for each type
	lin_constraints_camels(0,TLen,Items,Loads,Ns,Constraints).

map_camel_loads([],[],[]).
map_camel_loads([Load|Loads],[N|Ns],[N*Load|NCs]) :-
	N::integer(0,_),
	map_camel_loads(Loads,Ns,NCs).
	
lin_constraints_camels(T,T,_,_,_,[]) :- !.
lin_constraints_camels(T,TLen,Items,Loads,Ns,[LHS==RHS|Constraints]):-
	camel_lhs_constraint_(Loads,Ns,T,LHS),  % constraint LHS for item type T
	nth0(T,Items,RHS),                      % constraint RHS for item type T
	TNxt is T+1,                            % next type
	lin_constraints_camels(TNxt,TLen,Items,Loads,Ns,Constraints).

% constraint LHS for type T = sum(Load[T]*N)
camel_lhs_constraint_([Load],[N],T, L*N) :- !,  % last Load - minimum form
	nth0(T,Load,L).
camel_lhs_constraint_([Load|Loads],[N|Ns],T, RHS) :-
	nth0(T,Load,L),                         % Load[T]
	(L==0 -> RHS = RHS1 ; RHS = L*N+RHS1),  % omit if Load[T] == 0
	camel_lhs_constraint_(Loads,Ns,T,RHS1).
