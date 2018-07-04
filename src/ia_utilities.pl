%
%  print_interval(Int)
%
		
print_interval(ListOfInt) :-
	is_list(ListOfInt), !,  %% SWIP:
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

user:portray(Int) :-
	interval_object(Int,T,V,NL), !,
	print(clpBNR:intdef_(Int,T,V,NL)).


%
%  SWI hook to print interval ranges for query variables
%
:- initialization(                                  % increase max_depth (default 10)
	set_prolog_flag(answer_write_options,
		[quoted(false), portray(true), max_depth(64), spacing(next_argument)])
	).

user:expand_answer(Bindings,ExBindings) :- 
	mapBindings_(Bindings,ExBindings).

mapBindings_([], []).
mapBindings_([Name=In|Bs], [Name=Out|ExBs]) :-
	mapTerm_(In,Out), !,
	mapBindings_(Bs,ExBs).
	
mapTerm_(Int,Out) :-
	interval_object(Int,T,[L,H],_NL),       % interval value, replace by Id(L,H)
	Val=..[T,L,H],
	term_string(Int::Val, Out).
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
	
splitinterval_(integer,X,_,({X =< Pt};{Pt < X})) :-   % try to split and on failure use enumerate/1 .
	getValue(X,V),
	splitinterval_integer_(V,Pt), !.
splitinterval_(integer,X,_,enumerate([X])).           % failed to split, so enumerate

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
