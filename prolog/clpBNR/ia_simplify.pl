/*	The MIT License (MIT)
 *
 *	Copyright (c) 2019-2025 Rick Workman
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
%
% Expression variables are Prolog var's; numeric constants are precise.
% Note floats are treated like variables and no arithmetic is performed on them
%

% signed multiplier and power values
sign_val_(+,C,C) :- C>=0.
sign_val_(-,C,N) :- N is -C.

pwr_val_(*,C,C) :- C>=0.
pwr_val_(/,C,N) :- N is -C.


% utility to distribute A*(B1+B2) if they have variables in common or A is a constant
% former is safe for intervals (sub-distributive law), latter is valid
distribute_(C,B,Exp) :-
	number(C), !,
	B=..[AddOp,B1,B2], (AddOp == '+' ; AddOp == '-' ),  % watch out for vars
	DExp=..[AddOp,C*B1,C*B2],
	simplify(DExp,Exp).

% utility for (in)equality reduction 
/*simplify_eq_(Diff,B,Op,Exp) :-  compound(Diff), Diff = A1-A2, % LHS is difference and RHS =:=0
	number(B), B =:= 0, !,
	simplify_eq_(A1,A2,Op,Exp). */
simplify_eq_(A,B,Op,Exp) :-         % LHS and RHS are expressions with shared vars
	num_exp_vars_(A,AVs),         % only consider vars in arithmetic Ops
	num_exp_vars_(B,BVs),
	shared_vars_in_(AVs,BVs), !,  % so far just a test, no unification of non-local vars
	simplify(A-B,ES),             % normalize with non-zero value on RHS
	num_separate_(ES,LHS,RHS),
	(RHS =:= 0, LHS = EA-EB -> Exp =.. [Op,EA,EB] ; Exp=..[Op,LHS,RHS]).
simplify_eq_(A,B,Op,Exp) :-         % everything else, leave LHS and RHS alone
	simplify(A,AS),
	num_separate_(AS,LHS,AN),
	simplify(B,BS),
	num_separate_(BS,BS1,BN),
	num_rhs_(AN,BN,BS1,RHS),      % leave as symbolic, for later fuzzing as req'd
	Exp=..[Op,LHS,RHS].

num_separate_(Exp,Exp,0) :- var(Exp), !.
num_separate_(A+B,Out,Num) :- !,
	(number(B) 
	 -> Num is -B,
	 	Out=A
	 ;	num_separate_(A,AOut,Num),
	 	Out=AOut+B
	).
num_separate_(A-B,Out,Num) :- !,
	(number(B) 
	 -> Num = B,
	 	Out=A
	 ;	num_separate_(A,AOut,Num),
	 	Out=AOut-B
	).
num_separate_(Exp,Exp,0).

num_rhs_(N,N,E,E)   :- !.
num_rhs_(0,N,E,RHS) :- !, (E==0 -> RHS = -N ; RHS = E-N).
num_rhs_(N,0,E,RHS) :- !, (E==0 -> RHS = N ; RHS = E+N).
num_rhs_(L,R,E,RHS) :- N is L-R, (E==0 -> RHS = N ; RHS = E+N).

num_exp_vars_(Exp,Vars) :-  % collect vars in arithmetic expressions, fails if none
	exp_vars_(Exp,V/V,Vs/[]),	
	(Vs=[_|_] -> term_variables(Vs,Vars)).  % removes any duplicates, fails if no vars 

exp_vars_(X,ListIn,ListIn) :- atomic(X), !.  % includes []
exp_vars_(X,List/[X|NextTail],List/NextTail) :- var(X), !. 
exp_vars_([X|Xs],ListIn,ListOut) :- !,
	exp_vars_(X,ListIn,ListNxt),
	exp_vars_(Xs,ListNxt,ListOut).
exp_vars_(Exp,ListIn,ListOut) :-
	Exp =.. [Op|Xs],
	(memberchk(Op,[-,+,*,/,**]) -> exp_vars_(Xs,ListIn,ListOut) ; ListIn = ListOut).

shared_vars_in_([AV|AVs],BVs) :-
	shared_var_(BVs,AV) -> true ; shared_vars_in_(AVs,BVs).

shared_var_([BV|BVs],AV) :-
	AV == BV -> true ; shared_var_(BVs,AV).

%
% simplify/2
%
simplify(A,A) :- var(A),!.

simplify(N,N) :- number(N),!.

% possible distribute
simplify(A*B,Exp) :-
	compound(B),
	distribute_(A,B,Exp), !.
simplify(A*B,Exp) :-
	compound(A),
	distribute_(B,A,Exp), !.

% simplify equalities and inequalities
simplify(A==B,Exp) :-
	simplify_eq_(A,B,==,Exp), !.

simplify(A=<B,Exp) :-
	simplify_eq_(A,B,=<,Exp), !.

simplify(A>=B,Exp) :-
	simplify_eq_(A,B,>=,Exp), !.

simplify(A<B,Exp) :-
	simplify_eq_(A,B,<,Exp), !.

simplify(A>B,Exp) :-
	simplify_eq_(A,B,>,Exp), !.

simplify(A is B,A is B) :- !.  % Don't bother simplifying `is`
/*
% simplify "cascaded" divisions A/B/C = (A/B)/C = A*C/B
simplify(A/B,Exp) :- 
%	compound(B), B=Bn/Bd, !,
%	simplify(A*Bd/Bn,Exp).
	compound(A), A=An/Ad, !,
	simplify(An*B, E1),
	simplify(E1/Ad,Exp).
*/
%
% General purpose simplify
%
simplify(E,Exp) :-
	collect_exp_(E, L/L, Es/[]),  % collect terms in a difference list
	collect_exp_items(Es,Is),     % collect like terms
	reduce_exp_items_(Is,Exp),    % and reduce back to expression
	!.
	
% use difference list to collect terms of an expression
collect_exp_(A, List, Head/NewT) :-
	var(A), !,
	List=Head/[term(A,1)|NewT].  % separate to keep head unification cheap
	
collect_exp_(C, List, Head/NewT) :-
	preciseNumber(C), !,               % precise numeric value
	List=Head/[C|NewT].

collect_exp_(A, List, Head/NewT) :-    % floats as terms, can collect but not do arithmetic
	float(A), !,
	List=Head/[term(A,1)|NewT].

collect_exp_(A+B, List, NewList) :-
	!,
	left_exp_(A,AE),
	collect_exp_(AE,List,ListA),
	simplify(B,BT), 
	collect_exp_(BT,ListA,NewList).

collect_exp_(A-B,List,NewList) :-
	!,
	left_exp_(A,AE),
	collect_exp_(AE,List,ListA),
	simplify(B,BT),
	collect_neg_(BT,ListA,NewList).
	
collect_exp_(-B,List,NewList) :-
	simplify(B,BT),
	collect_neg_(BT,List,NewList).

collect_exp_(T, List/[Term|NewT], List/NewT) :-
	simplify_term(T,Term).

left_exp_(A,A)  :- var(A), !.
left_exp_(A,A)  :- functor(A,+,2), !.
left_exp_(A,A)  :- functor(A,-,2), !.
left_exp_(A,AE) :- simplify(A,AE).

collect_neg_(BT,List/[N|NewT], List/NewT) :-
	rational(BT),
	N is -BT.  % rational constant expressed as AT-BT
collect_neg_(BT,ListA/T,ListA/NewT) :-
	collect_exp_(BT,P/P,ListB),
	negate_term_(ListB,T/NewT).

negate_term_(T/T,NewT/NewT) :- var(T).
negate_term_([term(V,N)|Es]/T,[term(V,NN)|NEs]/NewT) :-
	NN is -N,
	negate_term_(Es/T,NEs/NewT).
negate_term_([N|Es]/T,[NN|NEs]/NewT) :-
	NN is -N,
	negate_term_(Es/T,NEs/NewT).

collect_exp_items(Es,NEs) :-
	sort(0,@>=,Es,Sorted),  % num_separate_/3 depends on sort order
	collect_exp_items_(Sorted,NEs).

% assume items sorted
collect_exp_items_([],[]).
collect_exp_items_([U],[U]) :- !.
collect_exp_items_([U,V|Es],EsNxt) :-
	number(U), number(V), !,                % add precise constant values
	S is U+V, 
	collect_exp_items_([S|Es],EsNxt).
collect_exp_items_([term(V,N1),term(U,N2)|Es],EsNxt) :-
	V==U,
	(ground(V) -> V =\= 1.0Inf ; true), !,  % infinities don't obey algebraic rules
	N is N1+N2,
	collect_exp_items_([term(V,N)|Es],EsNxt).
collect_exp_items_([U,V|Es],[U|EsNxt]) :-   % Note that imprecise floats are not added
	collect_exp_items_([V|Es],EsNxt).

reduce_exp_items_([T1,T2|Ts],Exp) :-        % 2 or more terms, combine and continue
	reduce_exp_item_(T1,Op1,Exp1),
	reduce_exp_item_(T2,Op2,Exp2),
	build_exp_(Exp1,Exp2,Op1,Op2,ExpN), !,  % ExpN =.. [Op,Exp1,Exp2], !,
	reduce_exp_items_([ExpN|Ts],Exp).
reduce_exp_items_([E],Exp) :-               % terminating case, 1 item left
	(compound(E), functor(E,term,2)
	 -> reduce_exp_items_([0,E],Exp)        % terminate single term(_..)
	 ;  Exp = E                             % already reduced to var, constant or expression
	).

build_exp_(Z,Exp2,_Op1,Op2,NExp2) :- number(Z), Z =:= 0,
	(Op2 == '-' -> build_Nexp_(Exp2,NExp2) ;  NExp2 = Exp2).
build_exp_(Exp1,Z,Op1,_Op2,NExp1) :- number(Z), Z =:= 0,  
	(Op1 == '-' -> build_Nexp_(Exp1,NExp1) ; NExp1 = Exp1).
build_exp_(Exp1,Exp2,+,+,Exp1+Exp2).
build_exp_(Exp1,Exp2,+,-,Exp1-Exp2).
build_exp_(Exp1,Exp2,-,+,Exp2-Exp1).
build_exp_(Exp1,Exp2,-,-,NExp1-Exp2) :- build_Nexp_(Exp1,NExp1).

build_Nexp_(Exp, NExp) :-                                   % constant
	rational(Exp),
	NExp is -Exp.
build_Nexp_(Exp, NExp) :-                                   % * or / expression, find head
	nonvar(Exp), Exp =.. [Op,A1,A2], (Op == * ; Op == /),
	build_Nexp_(A1,NA1),
	NExp =.. [Op,NA1,A2].
build_Nexp_(Exp, -Exp).                                     % other expression or var

reduce_exp_item_(V,           +, V)    :- var(V).           % variables
reduce_exp_item_(R,           +, R)    :- rational(R).      % constants
reduce_exp_item_(term(V,1),   +, V).
reduce_exp_item_(term(V,-1),  -, V).
reduce_exp_item_(term(V,0),   +, 0)    :- finite_(V).       % reduces to +0 if V finite
reduce_exp_item_(term(V,N),   Op, T)   :- mult_term_(V, N, Op, T).
reduce_exp_item_(-Exp,        -, Exp).
reduce_exp_item_(Exp,         +, Exp).

finite_(V) :- 
	(ground(V)
%	 -> abs(V) < 1.0Inf  % ground expression, evaluates to finite value
	 -> catch(abs(V) =\= 1.0Inf,_Err,true)  % ground expression, does not evaluate to infinite value
	 ;  interval_object(V, _Type, (LB,UB), _),  % interval with finite bounds
	    -1.0Inf < LB, UB < 1.0Inf
	).

mult_term_(T,   N, Op, M*T)   :- var(T), val_sign_(N,Op,M).
mult_term_(X*Y, N, Op, Exp*Y) :- mult_term_(X,N,Op,Exp).     % maintain Op associativity
mult_term_(X/Y, N, Op, Exp/Y) :- mult_term_(X,N,Op,Exp).
mult_term_(T,   N, Op, M*T)   :- val_sign_(N,Op,M).

val_sign_(V,Op,Vp) :- Vp is abs(V), (V<0 -> Op = (-) ; Op = (+)).

%
% simplify a term to an "expression" of term structures and constants
%
simplify_term(T,Term) :-
	collect_term_(T, L/L, Ts/[]),    % collect in a difference list
	collect_term_items_(Ts,Is),      % collect like terms
	% this does constant folding if reduction resulted in a constant
	reduce_term_items_(Is,ITerm),    % reduce back to expression
	term_final_(ITerm,Term),
	!.

term_final_(Term,Term) :- rational(Term), !.
term_final_(Term,term(T,C)) :- compound(Term), Term = C*T, rational(C), !.
term_final_(Term,term(Term,1)).

collect_term_(A, List, Head/NewT) :-
	var(A), !,
	List=Head/[elem(A,1)|NewT].
	
collect_term_(A, List, Head/NewT) :-
	rational(A), !,
	List=Head/[A|NewT].

collect_term_(A, List, Head/NewT) :-
	float(A), !,
	List=Head/[elem(A,1)|NewT].

collect_term_(-A, List, ListA/NewT) :- % -Term as Term * -1 for reducing signs
	simplify(A,AT), collect_term_(AT,List,ListA/[-1|NewT]).

collect_term_(A**N, List, Head/NewT) :-  % possible special case of user written element
	simplify(N,NT), rational(NT),
	simplify(A,AT),
	simplify_pwr_(AT,NT,Term),
	List=Head/[Term|NewT].

collect_term_(A*B,List,NewList) :-
	!,
	left_term_(A,AE),
	collect_term_(AE,List,ListA),
	simplify(B,BT),
	collect_term_(BT,ListA,NewList).
	
collect_term_(A/B,List,ListA/NewT) :-
	!,
	left_term_(A,AE),
	simplify(B,BT),
	collect_term_(AE,List,ListA/T),
	collect_term_(BT,P/P,ListB),
	invert_term_(ListB,T/NewT).

collect_term_(E,List/[elem(Exp,1)|NewT], List/NewT) :-
	E =.. [F|IArgs],
	simplify_list_(IArgs,OArgs),
	Exp =.. [F|OArgs].

% simplify_pwr_: NT rational, 
simplify_pwr_(AT,NT,elem(Exp,Pwr)) :-
	compound(AT), AT=Exp**P, rational(P), !,  % (X**P)**NT, NT and P both rational
	Pwr is NT*P.
simplify_pwr_(AT,NT,elem(AT,NT)).

left_term_(A,A)  :- var(A), !.
left_term_(A,A)  :- functor(A,*,2), !.
left_term_(A,A)  :- functor(A,/,2), !.
left_term_(A,AE) :- simplify(A,AE).

simplify_list_([],[]).
simplify_list_([I|IArgs],[O|OArgs]) :-
	simplify(I,O),
	simplify_list_(IArgs,OArgs).

invert_term_(T/T,NewT/NewT) :- var(T),!.
invert_term_([elem(V,N)|Es]/T,[elem(V,NN)|NEs]/NewT) :-  !,
	NN is -N,
	invert_term_(Es/T,NEs/NewT).
invert_term_([N|Es]/T,[NN|NEs]/NewT) :-
	NN is 1/N,
	invert_term_(Es/T,NEs/NewT).
	
collect_term_items_([],[]).
collect_term_items_(Es,NEs) :-
	msort([1|Es],Sorted),                  % ensure initial constant multiplier and sort
	collect_term_item_(Sorted,NEs).

collect_term_item_([],[]).
collect_term_item_([U],[U]) :- !.
collect_term_item_([U,V|Es],EsNxt) :-
	rational(U), rational(V), !,           % precise for multiply
	S is U*V,
	collect_term_item_([S|Es],EsNxt).
collect_term_item_([elem(U,N1),elem(V,N2)|Es],EsNxt) :-
	V==U,
	(ground(V) -> V =\= 1.0Inf ; true), !, % infinities don't obey algebraic rules
	N is N1+N2,
	collect_term_item_([elem(U,N)|Es],EsNxt).
collect_term_item_([U,V|Es],[U|EsNxt]) :-
	collect_term_item_([V|Es],EsNxt).

reduce_term_items_([Exp],Exp) :-           % terminating variable
	var(Exp), !.
reduce_term_items_([Exp],Exp) :-           % terminating constant
	rational(Exp), !.
reduce_term_items_([elem(V,N)],Exp) :- !,  % terminating single elem(_..)
	reduce_term_items_([1,elem(V,N)],Exp).
reduce_term_items_([Exp],Exp).             % terminating final expression
reduce_term_items_([T1,T2|Ts],Exp) :-
	reduce_term_item_(T1,Exp1,_),
	reduce_term_item_(T2,Exp2,Op),
	build_term_(Exp1,Exp2,Op,ExpN),        % ExpN =.. [Op,Exp1,Exp2],
	!,
	reduce_term_items_([ExpN|Ts],Exp).

% optimize some cases involving ±1
build_term_(C, E, /, Exp) :- nonvar(E), E=A**B, one_term_(C,A**NB,Exp), rational(B), NB is -B.
build_term_(E, C, _, Exp) :- nonvar(E), E=C1/B, one_term_(C1,C/B,Exp).
build_term_(C, E, *, Exp) :- one_term_(C, E, Exp).
build_term_(E, C, _, Exp) :- one_term_(C, E, Exp). 
build_term_(E1,E2,Op,Exp) :- Exp =.. [Op,E1,E2].

one_term_(One, Exp0, Exp) :-
	number(One), C is float(One),
	( C =  1.0 -> Exp =  Exp0
	;(C = -1.0 -> Exp = -Exp0)
	).

reduce_term_item_(V,          V, *)     :- var(V),!.  % already reduced to var
reduce_term_item_(elem(_, 0), 1, *).
reduce_term_item_(elem(V, 1), V, *).
reduce_term_item_(elem(V,-1), V, /).
reduce_term_item_(elem(V, E), V**P, Op) :- P is abs(E), (E>0 -> Op= * ; Op= /).
reduce_term_item_(R,          R, *).  % catchall: constant or expression
