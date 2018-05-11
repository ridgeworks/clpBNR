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
% portray for (cyclic) interval objects
%    hook for system print/1
%
portray(Int) :-
	interval(Int), !,    % fails if not an interval
	portrayInt(Int).
	
%portray(freeze(Int,clpBNR:intdef_(Int,Type,Id,NL))) :- !,
%	portray(freeze(Int,intdef_(Int,Type,Id,NL))).

%portray(Int) :-   %%% vars never get portrayed
%	get_attrs(Int,As),
%	nl,write(As).

portray({freeze(Int, Goal)}) :-
	write(@(Goal)).

portray(freeze(Int, Goal)) :- 
	write(@(Goal)),
	Goal = clpBNR:intdef_(_,Type,Id,_),
	%atomic(Id),
	%atom_concat(Type,Id,Label),   % make Label
	g_read(Id,V),                 % Int not the frozen variable?? 
	printValue_(V, [L,H]),        % Val format type dependant
	Val=..[Type,L,H],
	print(Int::Val).

/*portray(freeze(Int,G)) :- isfrozen(Int,G).
	
isfrozen(Int,G) :-
	write(freeze),
	((var(Int) -> write(' var '));
	 (interval(Int) -> write(' interval '));
	 write(' unknown ')),
	write(Int),
	print(G).
*/	
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
/*portrayInt(Int) :- 
	Int = int(Type,_, _),
	atom_concat(Type,'@?',Label),   % make undefined Label
	print(Label::'_').*/
	
printValue_([N,N],N) :- !.
printValue_(V,    V).
%
%  enumerate integer and boolean intervals
%
		 
enumerate(X) :-
	interval(X), !,               % if single interval, put it into a list
	enumerate_([X]).  % list of one
enumerate(X) :-
	enumerate_(X).
	
	
enumerate_([]).
enumerate_([X|Xs]) :-
	number(X), !,  % already bound to a point value
	enumerate_(Xs).
enumerate_([X|Xs]) :-
	interval(X),
	getValue(X,[L,H]),
%	between(L,H,N), {X==N},  % gen and constrain
	between(L,H,X),  % gen and constrain
	enumerate_(Xs).

%
%  solve(Int) - joint search on list of intervals
%

solve(X) :- solve(X,5).           % default solve to 5 digits of precision

solve(X,P) :-
	interval(X), !,               % if single interval, put it into a list
	solve([X],P).
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
xpsolve_each_([[]|Xs],Us,Err) :-          % end of nested listed, discard
	!,
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
	splitinterval_real_(V,Pt,Err), !,
	SPt::real(Pt,Pt).  % create point interval
	
splitinterval_(integer,X,_,Choices) :-
	getValue(X,V),
	splitinterval_integer_(V,X,Choices), !.

splitinterval_(boolean,X,Err,Choices) :-
	splitinterval_(integer,X,Err,Choices).

%
% splitinterval_integer_ and splitinterval_real_ require ! at point of call.
%
splitinterval_integer_([L,L],_,_) :-
	!,fail.                          % point interval, can't be split'
%splitinterval_integer_([L,H],X,{X==L},{X==H}) :-
%	1 is H-L.                        % width is 1, either/or
splitinterval_integer_([L,H],X,enumerate([X])) :-
	H-L =< 16.                       % if width =< 16, just use enumerate
splitinterval_integer_([L,H],X,({X=<0};{1=<X})) :-
	L<0, H>0.                        % difference exceeds 16 and contains 0
splitinterval_integer_([L,H],X,({X=<PtL};{PtH=<X})) :-
	negInfinity(L),
	PtL is H*10-5,                    % subtract 5 in case H is 0. (-5, -15, -105, -1005, ...)
	PtH is PtL+1.
splitinterval_integer_([L,H],X,({X=<PtL};{PtH=<X})) :-
	posInfinity(H),
	PtL is L*10+5,                    % add 5 in case L is 0. (5, 15, 105, 1005, ...)
	PtH is PtL+1.
splitinterval_integer_([L,H],X,({X=<PtL};{PtH=<X})) :-     % difference is more than 16
	PtL is (L div 2) + (H div 2),    % avoid overflow
	PtH is PtL+1.

splitinterval_real_([L,H],0.0,_) :-  % if interval contains 0, but isn't 0, split on 0.
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
