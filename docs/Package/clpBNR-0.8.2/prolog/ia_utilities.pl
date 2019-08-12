/*	The MIT License (MIT)
 *
 *	Copyright (c) 2019 Rick Workman
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
	nb_delete(minimize__),  % Note: depends on global var so not thread-safe?
	Min::Dom,               % only works on intervals (numbers, and others, can't be minimized)
	functor(Dom,Type,_),
	minimize__(Type,Min,Vs,Solver).

minimize__(integer,Min,Vs,Solver) :-
	once(Solver),           % get first solution with a lower UB
	nb_setval(minimize__, [1,Min,Vs]),  % new Min values for next iteration
	fail.
	
minimize__(real,Min,Vs,Solver) :-
	once(                   % get first solution with a lower UB
		(range(Min, [_,PUB]),
		 Solver,
		 range(Min, [_,UB]),
		 % specific check for new smaller UB, discards  same solutions, can't use {<} with real
		 UB < PUB
		)
	),
	nb_setval(minimize__, [1,Min,Vs]),  % new Min values for next iteration
	fail.
	
minimize__(Type,Min,Vs,Solver) :-
	catch((nb_getval(minimize__, [1,NewMin,NewVs]),nb_setval(minimize__, [0,NewMin,NewVs])),_,fail),
	range(NewMin,[_,UB]),
	(Type=integer -> {Min<UB} ; {Min=<pt(UB)}),  % constrain UB, use pt() to avoid outward rounding
	minimize__(Type,Min,Vs,Solver),
	!.
	
minimize__(_,Min,Vs,_):-  % can't minimize UB any further, retrieve last solution and fail if none
	catch((nb_getval(minimize__, [_,Min,Vs]),nb_delete(minimize__)),_,fail).

%
%  maximize(Interval, Vars, Solver)
%
%  analogous to minimize (see above)
%
maximize(Max,Vs,Solver) :-
	nb_delete(maximize__),  % Note: depends on global var so not thread-safe
	Min::Dom,               % only works on intervals (numbers, and others, can't be minimized)
	functor(Dom,Type,_),
	maximize__(Type,Max,Vs,Solver).

maximize__(integer,Max,Vs,Solver) :-
	once(Solver),           % get first solution with a higher LB
	nb_setval(maximize__, [1,Max,Vs]),  % new Min values for next iteration
	fail.
	
maximize__(real,Max,Vs,Solver) :-
	once(                        %% get first solution with a lower UB
		(range(Max,[PLB,_]),
		 Solver,
		 range(Max, [LB,_]),
		 LB > PLB  % specific check for new lareger LB, discards same solutions
		)
	),
	nb_setval(maximize__, [1,Max,Vs]),  % new Min values for next iteration
	fail.
	
maximize__(Type,Max,Vs,Solver) :-
	catch((nb_getval(maximize__, [1,NewMax,NewVs]),nb_setval(maximize__, [0,NewMax,NewVs])),_,fail),
	range(NewMax,[LB,_]),
	(Type=integer -> {Max>LB} ; {Max>=pt(LB)}),  % constrain LB, use pt() to avoid outward rounding
	maximize__(Type,Max,Vs,Solver),
	!.
	
maximize__(_,Max,Vs,_):-  % can't minimize UB any further, retrieve last solution and fail if none
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


absolve( X ):-
	current_prolog_flag(clpBNR_default_precision,P),
	absolve(X,P),!.

absolve( X , _ ):- numeric(X),!.
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
	Split is LB + DL1,
	Split > LB2, Split < UB2,	% changed 93/06/01 WJO make sure that the interval can be split
	not({X=<Split}),!,  % so X must be > split
	{X >= Split},
  	interval_object(X, Type, [LB1, _], _),     % get interval type and value
	absolve_l(X, DL1, LB1,NL1,Limit).
absolve_l(_, _, _,  _,_).
         
absolve_r(X, _, _, _, _) :-
		not(not(upper_bound(X))),	% changed 93/06/01 WJO to avoid getting stuck on upper bound
		!.
absolve_r(X, DU,UB, NU,Limit):- NU<Limit, % work on right side
	interval_object(X, Type, [LB2, UB2], _),     % get interval type and value
	trim_point_(NU,NU1,Type,Limit, DU,DU1),
	Split is UB - DU1,
	Split > LB2, Split < UB2,	% changed 93/06/01 WJO make sure that the interval can be split
	not({X>=Split}),!,       % so X must be > split
	{X =< Split},
	interval_object(X, Type, [_, UB1], _),     % get interval type and value
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
	numeric(X), !.                % already a point value
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
	splitinterval_real_(V,Pt,Err), !,           % initial guess
	split_real_(X,V,Pt,Err,SPt).
	
splitinterval_(integer,X,_,({X =< Pt};{Pt < X})) :-   % try to split and on failure use enumerate/1 .
	getValue(X,V),
	splitinterval_integer_(V,Pt), !.
splitinterval_(integer,X,_,enumerate_([X])).           % failed to split, so enumerate

%splitinterval_(boolean,X,Err,Choices) :-
%	splitinterval_(integer,X,Err,Choices).


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


splitinterval_real_([L,H],0.0,E) :-   % if interval contains 0, split on 0.
	L < 0, H > 0, !,                  % cut in case error criteria fails
	catch((H-L) > E, _, true).        % fail if width is less than error criteria, overflow is OK

splitinterval_real_([-1.0Inf,H],Pt,_) :-   % neg. infinity to H=<0
	!,  % if following overflows, split failed
	catch(Pt is H*10-1,_,fail).       % subtract 1 in case H is 0. (-1, -11, -101, -1001, ...)
splitinterval_real_([L,1.0Inf],Pt,_) :-   % L>=0 to pos. infinity
	!,  % if following overflows, split failed
	catch(Pt is L*10+1,_,fail).       % add 1 in case L is 0. (1, 11, 101, 1001, ...)

splitinterval_real_([L,H],Pt,E) :-    % finite L,H, positive or negative but not split, Pt\=0.
	splitMean_(L,H,Pt),
	Pt =\= 0,                         % if calculated split point zero, underflow occurred -> fail
	catch((H-L) > max(abs(Pt),1)*E, _, true). % fail if width is less than relative error, overflow is OK
	
%splitinterval_real_([L,H],Pt,E) :-
%	writeln('FAIL'([L,H],Pt,E)),fail.

% (approx.) geometric mean of L and H (same sign)
splitMean_(L,H,M) :- L>0, !, M is sqrt(L)*sqrt(H).       % all > 0
splitMean_(L,H,M) :- H<0, !, M is -sqrt(-L)*sqrt(-H).    % all < 0

splitMean_(L,H,M) :- L=:=0, !, M is min(H/2, sqrt( H)).  % L endpoint is 0
splitMean_(L,H,M) :- H=:=0, !, M is max(L/2,-sqrt(-L)).  % H enpdoint is 0


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%					partial_derivative(E, X, D)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%  Perform symbolic differentiation followed by simplify/2:  D = dE/dX
%
%  located in utilities as it's a common requirement for applying series expansion
%  to improve convergance. Avoids necessity of exposing simplify/2.
%  Note that the set of rules only covers functions supported by {}.
%
partial_derivative(F,X,DFX) :-
	pd(F,X,DD),
	simplify(DD,DFX).

pd(Y,X,D)                      :- var(Y), (X==Y -> D=1 ; D=0), !.

pd(C,_,0)                      :- numeric(C), !.

pd(-U,X,-DU)                   :- pd(U,X,DU).

pd(U+V,X,DU+DV)                :- pd(U,X,DU), pd(V,X,DV).

pd(U-V,X,DU-DV)                :- pd(U,X,DU), pd(V,X,DV).

pd(U*V,X,V*DU+U*DV)            :- pd(U,X,DU), pd(V,X,DV).

pd(U**N,X,(N*U**(N-1))*DU)     :- pd(U,X,DU).

pd(U/V,X,(V*DU-U*DV)/(V**2))   :- pd(U,X,DU), pd(V,X,DV).

pd(log(U),X,DU/U)              :- pd(U,X,DU).

pd(exp(U),X,exp(U)*DU)         :- pd(U,X,DU).

pd(sqrt(U),X,DU/(2*sqrt(U)))   :- pd(U,X,DU).

pd(sin(U),X,cos(U)*DU)         :- pd(U,X,DU).

pd(cos(U),X,-sin(U)*DU)        :- pd(U,X,DU).

pd(tan(U),X,DU/cos(U)**2)      :- pd(U,X,DU).

pd(asin(U),X,DU/sqrt(1-U**2))  :- pd(U,X,DU).

pd(acos(U),X,-DU/sqrt(1-U**2)) :- pd(U,X,DU).

pd(atan(U),X,DU/(1+U**2))      :- pd(U,X,DU).


%
% safe declarations must be after the predicate definitions
%
% the following use meta-predicates
sandbox:safe_primitive(clpBNR:solve(_)).
sandbox:safe_primitive(clpBNR:solve(_,_)).
sandbox:safe_primitive(clpBNR:splitsolve(_)).
sandbox:safe_primitive(clpBNR:splitsolve(_,_)).
sandbox:safe_primitive(clpBNR:minimize(_,_,_)).
sandbox:safe_primitive(clpBNR:maximize(_,_,_)).
sandbox:safe_primitive(clpBNR:partial_derivative(_,_,_)).
