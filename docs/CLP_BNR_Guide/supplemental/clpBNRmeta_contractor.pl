%
% A module to support metalevel contractors for clpBNR
% Add  additional contractors as required
:- module(clpBNRmeta_contractor,
	[iterate_until/3,            % general purpose iterator
	 mid_split_one/1,            % contractor to split largest interval at midpoint
	 mid_split/1,                % contractor to split an interval at midpoint
	 cf_contractor/2,            % contractor for centred form, e.g., Taylor expansion
	 build_taylor_contractor/2,  % build cf_contractor based on Taylor expansion
	 build_taylor_merged/2       % build merged Taylor cf_contractor from list of equations 
	]).
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
cf_contractor(Xs,As) :-
	findall(Ds,(maplist(bind_to_midpoint,Xs,As),maplist(domain,Xs,Ds)),[XDs]),
	maplist(::,Xs,XDs).
	
bind_to_midpoint(X,A) :- A is float(midpoint(X)).	
%
% build a cf_contractor for a multivariate expression based on Taylor expansion
%
build_taylor_contractor(E1==E2,cf_contractor(Xs,As)) :-
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
	Xs::real,
	{Cs}. % apply constraints

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
build_taylor_merged(Es,T) :-
	maplist(build_taylor_contractor,Es,Ts),
	cf_merge(Ts,T).
	
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
