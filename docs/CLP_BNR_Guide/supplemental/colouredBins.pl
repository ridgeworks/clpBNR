% example data
bin_demands(b1,[3*glass, 4*plastic, 1*steel, 4*wood, 2*copper]).
bin_demands(b2,[6*glass, 8*plastic, 2*steel, 8*wood, 4*copper]).

bin_demands(c1,[32*glass,44*plastic,11*steel,44*wood,230*copper]).

bin_demands(d1,[132*glass,414*plastic,1001*steel,414*wood,230*copper]).

% pack 3 bin types with 5 types of commodities
bin_types([red,green,blue]).

commodities([glass, plastic, steel, wood, copper]).

% define a bin with constraints
bin(Type, Contents, Total):-
	Type::integer(1,3),                               % enumeration of 3 bin types
	{Red == (Type==1), Green == (Type==2), Blue == (Type==3)}, % true if bin the designated colour
	Binsize::integer(1,4),                            % bin capacity, colour dependent
	{Binsize == Red*3 + Blue*1 + Green*4},            % "conditional" expression
	Contents=[Glass,Plastic,Steel,Wood,Copper], Contents::integer(0,_),
	Total::integer(1,_),                              % % bin contains Total items (at least 1)
	{Total == Glass + Plastic + Steel + Wood + Copper, Total =< Binsize},  
	{(Wood >= 1) -> (Plastic >= 1)},                  % wood requires plastic
	{Glass * Copper == 0},                            % glass excludes copper
	{Copper * Plastic == 0},                          % copper excludes plastic
	{Blue  -> (Wood + Plastic == 0)},                 % blue bin -> no plastc or wood
	{Red   -> ((0==Steel + Plastic) and (Wood=<1))},  % red bin -> no steel or plastic, no more than 1 wood
	{Green -> ((0==Glass + Steel) and (Wood=<2))}.    % green bin -> no steel or plastic, no more than 2 wood

setup_bins_(Items,Total,Contents) :-
	commodities(Names),
	get_bin_items_(Names,Items,Contents,0,Total).

get_bin_items_([],_,[],Total,Total).
get_bin_items_([N|Names],ItemsList,[C|Counts],Acc,Total):-
	(memberchk(C*N,ItemsList) -> NewAcc is Acc+C ; NewAcc=Acc),
	get_bin_items_(Names,ItemsList,Counts,NewAcc,Total).

% reduce result for output
accumulate_bins_([],[],Total,Total).
accumulate_bins_([bin(T,C,L)|BinsRaw],Bins,Acc,Total) :- !,
	accumulate_bins_([1*bin(T,C,L)|BinsRaw],Bins,Acc,Total).
accumulate_bins_([0*_|BinsRaw],Bins,Acc,Total) :- !,
	accumulate_bins_(BinsRaw,Bins,Acc,Total).	
accumulate_bins_([N*B,B|BinsRaw],Bins,Acc,Total) :- !,
	N1 is N+1,
	accumulate_bins_([N1*B|BinsRaw],Bins,Acc,Total).
accumulate_bins_([N*bin(T,Contents,_)|BinsRaw],[N*Bin|Bins],Acc,Total) :-
	bin_types(BTs), nth1(T,BTs,Type),
	commodities(Names), format_commodities_(Names,Contents,Comms),
	Bin =.. [Type|Comms], !,
	AccN is Acc+N,
	accumulate_bins_(BinsRaw,Bins,AccN,Total).

format_commodities_([],[],[]).
format_commodities_([N|Names],[Count|Contents],[Count*N|Comms]) :- Count>0, !,
	format_commodities_(Names,Contents,Comms).
format_commodities_([_|Names],[_|Contents],Comms) :-
	format_commodities_(Names,Contents,Comms).

%	For example:
% ?- pack_bins([3*glass, 4*plastic, 1*steel, 4*wood, 2*copper],Bins,Required).
% Bins = [1*red(2*copper), 1*red(3*glass), 2*green(2*plastic, 2*wood), 1*blue(1*steel)],
% Required = 5.
%
pack_bins(Items,Bins,Required) :-
	setup_bins_(Items,Total,ItemsRaw),  % process input
	bin_load_(Total,ItemsRaw,BinsRaw),  % add a bin (further add on backtracking)
	bins_ordered_(BinsRaw),             % order bins to break symmetry
	enum_bins_(BinsRaw), !,             % enumerate bin type and contents - single solution
	accumulate_bins_(BinsRaw,Bins,0,Required).  % format for output
	
bin_load_(0, [0,0,0,0,0], []).
bin_load_(Total, Amounts, [bin(Type,Contents,Size)|Bins]) :-
	bin(Type,Contents,Size),                    % new bin
	{T == Total - Size, T>=0},                  % decrease total by bin capacity
	subtract_clp(Amounts, Contents, Residual),  % decrease each commodity using bin contents
	bin_load_(T, Residual, Bins).               % repeat until feasible solution exists

bins_ordered_([_]) :- !.
bins_ordered_([X,Y|Xs]) :- order_bins_(X,Y), bins_ordered_([Y|Xs]).

order_bins_(bin(T1,_,S1), bin(T2,_,S2)) :-
	{(T1<T2) or ((T1==T2) and (S1=<S2))}.

subtract_clp([], [], []).
subtract_clp([X|Xs], [Y|Ys], [Z|Zs]) :-
	{Z == X - Y, Z >= 0},  % can't get to -ve items
	subtract_clp(Xs,Ys,Zs).

enum_bins_([]).
enum_bins_([bin(T,C,_S)|Bs]):- 
	enumerate([T|C]),
	enum_bins_(Bs).

%	For example:
% ?- fastpack_bins([3*glass, 4*plastic, 1*steel, 4*wood, 2*copper],Bins,Required).
% Bins = [1*blue(1*steel), 1*green(2*copper), 1*red(3*glass), 2*green(2*plastic, 2*wood)],
% Required = 5.
%
fastpack_bins(Items,Bins,Required) :-
	setup_bins_(Items,_Total,ItemsRaw),        % process input
	% generate possible load patterns
	findall(bin(Type,Contents,Size), (bin(Type, Contents, Size), enumerate([Type|Contents])), BinDefs),
	% use ItemsRaw and BinDefs to define linear objective expression and constraints 
	bins_lin_summation(ItemsRaw,BinDefs,NBins,Obj,Constraints),
	lin_minimize(Obj,{Constraints},_Min),      % and minimize
	accumulate_bins_(NBins,Bins,0,Required).   % format for output

bins_lin_summation(Items,BinDefs,NBins,Obj,Constraints) :-
	bins_list(BinDefs,Ns,NBins),  % lists of pattern counts
	sym_sum_list(Ns,Obj),     % Objective function is sum of counts
	length(Items,TLen),    % construct constraint for each type
	lin_constraints_bins(0,TLen,Items,BinDefs,Ns,Constraints).

bins_list([],[],[]).
bins_list([Bin|BinDefs],[N|Ns],[N*Bin|NBins]) :-
	N::integer(0,_),
	bins_list(BinDefs,Ns,NBins).
	
lin_constraints_bins(T,T,_,_,_,[]) :- !.
lin_constraints_bins(T,TLen,Items,BinDefs,Ns,[LHS==RHS|Constraints]):-
	bin_lhs_constraint_(BinDefs,Ns,T,LHS),
	nth0(T,Items,RHS),
	T1 is T+1,	
	lin_constraints_bins(T1,TLen,Items,BinDefs,Ns,Constraints).
	
bin_lhs_constraint_([bin(_,Contents,_)],[N],T, CI*N) :- !,
	nth0(T,Contents,CI).
bin_lhs_constraint_([bin(_,Contents,_)|BinDefs],[N|Ns],T, RHS) :-	
	nth0(T,Contents,CI),
	(CI==0
	 -> bin_lhs_constraint_(BinDefs,Ns,T,RHS)
	 ;  RHS = CI*N+RHS1,
	    bin_lhs_constraint_(BinDefs,Ns,T,RHS1)
	).

sym_sum_list([X],X) :- !.
sym_sum_list([X|Xs],X+XS) :-
	sym_sum_list(Xs,XS).
