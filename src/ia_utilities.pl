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
	print(Int).
	
print_interval(Int) :-
	getValue(Int,Bounds),
	print(Bounds).

print_intervals([]).
print_intervals([Int]) :- !,
	print_interval(Int).
print_intervals([Int|Ints]) :-
	print_interval(Int), write(','),
	print_intervals(Ints).
	

%
% portray for frozen interval objects (instantiated values print as numbers)
%    hook for system print/1, except not used on vars frozen or otherwise
%
% direct use of portray/1
user:portray(X) :-  
	interval(X), !,
	frozen(X,Goal),
	print(Goal).
% catch output using standard freeze format
user:portray(freeze(X, clpBNR:intdef_(X,T,Id,NL))) :-  % Note: X is not the frozen var
	print(clpBNR:intdef_(X,T,Id,NL)).
% catch output of clpBNR freeze Goal
user:portray(clpBNR:intdef_(X,T,Id,NL)) :- 
	b_getval(Id,[L,H]),  %%%  stealthy access since clpBNR:getValue(Id,V) not accessible from user:P
%	intValue(Id,L,H,Out),
	write(clpBNR:intdef_(X,T,Id,NL)).
	
%attribute_goals(X) -->
%	{get_attr(X, freeze, clpBNR:intdef_(X,_T,Id,_NL))},
%	{trace},
%	[mapTerm(X,Out)].
%'$attvar':portray_attr(freeze,Goal,X) :-
%	interval(X), !,
%	system:print(Goal).

%
%  SWI hook to print interval ranges for query variables
%
:- initialization(                                  % increase max_depth (default 10)
	set_prolog_flag(answer_write_options,
		[quoted(true), portray(true), max_depth(64), spacing(next_argument)])
	).

user:expand_answer(Bindings,ExBindings) :- 
	mapBindings_(Bindings,ExBindings).

mapBindings_([], []).
mapBindings_([Name=In|Bs], [Name=Out|ExBs]) :-
	mapTerm_(In,Out), !,
	mapBindings_(Bs,ExBs).
	
mapTerm_(Int,Out) :-
	interval_object(Int,_T,Id,_NL),       % interval value, replace by Id(Range..)
	getValue(Int,[L,H]),
	intValue(Id,L,H,Out).  %Out=..[Id,L,H].
mapTerm_(List,Out) :-
	list(List),
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
intValue(Id,L,H,Out) :-
	float(L), float(H),
	number_codes(L,LC), number_codes(H,HC),
	matching_(LC,HC,Match,0,MLen),
	MLen>5,
	atom_concat(Match,'...',Out).
*/
intValue(Id,L,H,Out) :- Out=..[Id,L,H].  % universal format %% atom_codes(Id,[948]), 
	
/*
matching_([],[],[],N,N).
matching_([C|LCs],[C|HCs],[C|Cs],N,Nout) :- !,  % matching
	succ(N,N1),
	matching_(LCs,HCs,Cs,N1,Nout).
matching_(LCs,HCs,[],N,N) :-    % non-matching
	digits_(LCs),digits_(HCs).  % remaining must be digit codes, i.e., no exponent

digits_([]).
digits_([D|Ds]) :- 48=<D,D=<57, digits_(Ds).
*/
	
	
	
/*
portray(@(Int,_)) :-         % SWI cyclic str
	interval(Int), !,    % fails if not an interval
	portrayInt(Int).

portray(@(V,Vs)) :-          % SWI cyclic str
	defined_(Vs,V,Int),
	interval(Int), !,    % fails if not an interval
	portrayInt(Int).
	
portray(@(ListOfInt,Vs)) :-  % SWI cyclic str
	is_list(ListOfInt),!,
	write('['),
	portray_intervals(ListOfInt,Vs),
	write(']').
	
defined_([V=Int|Vs], V, Int) :-!.
defined_([_|Vs], V, Int) :- defined_(Vs,V,Int).

portray_intervals([],_).
portray_intervals([Int],Vs) :- !,
	print(@(Int,Vs)).
portray_intervals([Int|Ints],Vs) :-
	print(@(Int,Vs)), write(','),
	portray_intervals(Ints,Vs).
	
portrayInt(Int) :- 
	interval_object(Int,Type,Id,_),
	atom_concat(Type,Id,Label),   % make Label
	getValue(Int,V),
	printValue_(V, Val),    % Val format type dependant
	print(Label::Val).
portrayInt(Int) :- 
	Int = int(Type,_, _),
	atom_concat(Type,'@?',Label),   % make undefined Label
	print(Label::'_').
	
printValue_([N,N],N) :- !.
printValue_(V,    V).
*/
	
%
%  trace debug code only -  called from stable_/1
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
%  solve(Int) - joint search on list of intervals
%

solve(X) :- solve(X,6).           % default solve to 6 digits of precision

solve(X,P) :-
	interval(X), !,               % if single interval, put it into a list
	solve([X],P).
solve(X,P) :-
	number(X), !.                 % already a point value
solve(X,P) :-
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
	list(X), !,                           % nested list
	xpsolve_each_(X,U,Err),               % split nested list
	xpsolve_each_(Xs,Us,Err).             % then others in main list
xpsolve_each_([X|Xs],Us,Err) :-
	xpsolve_each_(Xs,Us,Err).             % split failed or already a number, drop interval from list, and keep going
	
%
% try to split interval - fails if unsplittable (too narrow)
%
splitinterval_(real,X,Err,({X =< SPt};{SPt =< X})) :-
	getValue(X,V),
	splitinterval_real_(V,Pt,Err), !,           % initial guess
	split_real_(X,V,Pt,Err,SPt).
	
splitinterval_(integer,X,_,({X < SPt};{SPt < X})) :-          % try to split and on failure use enumerate/1 .
	getValue(X,V),
	splitinterval_integer_(V,Pt),
	split_integer_(X,V,Pt,SPt), !.
splitinterval_(integer,X,_,enumerate([X])).     % failed to split, so enumerate

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

%  split an integer interval
split_integer_(X,_,Pt,Pt) :-               % Pt not in solution space, split here
	X\=Pt, !.
split_integer_(X,[L,H],Pt,SPt) :-          % Pt in current solution space, try lower range
	split_integer_lo(X,[L,Pt],SPt), !.
split_integer_(X,[L,H],Pt,SPt) :-          % Pt in current solution space, try upper range
	split_integer_hi(X,[Pt,H],SPt).

split_integer_lo(X,[L,Pt],NPt) :-
	splitinterval_integer_([L,Pt],SPt), !,
	(X\=SPt -> NPt=SPt ; split_integer_lo(X,[L,SPt],NPt)).

split_integer_hi(X,[Pt,H],NPt) :-
	splitinterval_integer_([Pt,H],SPt), !,
	(X\=SPt -> NPt=SPt) ; split_integer_hi(X,[SPt,H],NPt).

%
% splitinterval_integer_ and splitinterval_real_ require ! at point of call.
%
	
splitinterval_integer_([L,H],0) :-
	L<0, H>0.                         % contains 0 but 0 not a bound so splittable
splitinterval_integer_([L,H],Pt) :-
	negInfinity(L),
	Pt is H*10-5.                     % subtract 5 in case H is 0. (-5, -15, -105, -1005, ...)
splitinterval_integer_([L,H],Pt) :-
	posInfinity(H),
	Pt is L*10+5.                     % add 5 in case L is 0. (5, 15, 105, 1005, ...)
splitinterval_integer_([L,H],Pt) :- 
	catch(H-L >= 16, _Err, fail),     % don't split ranges smaller than 16
	Pt is (L div 2) + (H div 2).      % avoid overflow


splitinterval_real_([L,H],0.0,E) :-  % if interval contains 0, but isn't 0, split on 0.
	L < 0, H > 0,
	L < H.  % fail if width is zero (can't split)'
splitinterval_real_([L,H],Pt,_) :-   % neg. infinity to zero or neg. H
	negInfinity(L),
	Pt is H*10-1.                    % subtract 1 in case H is 0. (-1, -11, -101, -1001, ...)
splitinterval_real_([L,H],Pt,_) :-   % zero or pos. L to pos. infinity
	posInfinity(H),
	Pt is L*10+1.                    % add 1 in case L is 0. (1, 11, 101, 1001, ...)
splitinterval_real_([L,H],Pt,E) :-   % finite L,H, positive or negative but not split
	D is (H-L),                      % current inteval width (positive), also can't overflow'
	posSmallest(PS),
	D > PS*2,                        % width > some minimum to split
	splitMean_(L,H,Pt),              % mean of infinity (overflow) or 0 (underflow) will cause failure
	abs(D/Pt) > E.                   % error criteria

% geometric mean of L and H (same sign) if not non-zero, arithmetic mean if either 0
splitMean_(L,H,M) :- L>0, !, M is sqrt(L)*sqrt(H).     % avoid overflow
splitMean_(L,H,M) :- H<0, !, M is -sqrt(-L)*sqrt(-H).
splitMean_(L,H,M) :- 0.0 is float(L), !, M is H/2.
splitMean_(L,H,M) :- 0.0 is float(H), !, M is L/2.


%
% Get all defined statistics
%
clpStatistics(Ss) :- findall(S, clpStatistic(S), Ss).
