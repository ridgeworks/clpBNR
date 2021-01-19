/*	The MIT License (MIT)
 *
 *	Copyright (c) 2019,2020 Rick Workman
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

% negatable operators
negate_op_(+,-).
negate_op_(-,+).

% power operators
invert_op_(*,/).
invert_op_(/,*).

% signed multiplier and power values
sign_val_(+,C,C) :- C>=0.
sign_val_(-,C,N) :- N is -C.

pwr_val_(*,C,C) :- C>=0.
pwr_val_(/,C,N) :- N is -C.


% utility to distribute A*(B1+B2) if they have variables in common or A is a constant
% former is safe for intervals (sub-distributive law), latter is valid
distribute_(C,B,Exp) :-
	number(C), !,
	B=..[AddOp,B1,B2], negate_op_(AddOp,_),  % watch out for vars
	DExp=..[AddOp,C*B1,C*B2],
	simplify(DExp,Exp).
distribute_(A,B,Exp) :-  % not always a good thing, e.g., X*(X-1) may be better than X**2-X
	B=..[Op,B1,B2], negate_op_(Op,_),        % watch out for vars
	shared_vars_(A,B), !, % any shared vars
	DExp=..[Op,A*B1,A*B2],
	simplify(DExp,Exp).

% utility for (in)equality reduction 
normalize_(A,B,Op,Exp) :-
	B==0, !,                      % RHS = 0
	simplify(A,AS),
	num_separate_(AS,LHS,RHS),
	Exp=..[Op,LHS,RHS].
normalize_(A,B,Op,Exp) :-
	A==0, !,                      % LHS = 0
	simplify(B,BS),
	num_separate_(BS,RHS,LHS),
	Exp=..[Op,LHS,RHS].
normalize_(A,B,Op,Exp) :-
	occurs_in_(A,B), !,           % RHS is shared var
	simplify(A-B,AS),
	num_separate_(AS,LHS,RHS),
	Exp=..[Op,LHS,RHS].
normalize_(A,B,Op,Exp) :-
	occurs_in_(B,A), !,           % LHS is shared var
	simplify(B-A,BS),
	num_separate_(BS,RHS,LHS),
	Exp=..[Op,LHS,RHS].
normalize_(A,B,Op,Exp) :-
	compound(A), compound(B),     % LHS and RHS are expressions with shared vars
	shared_vars_(A,B), !,
	simplify(A-B,AS),
	num_separate_(AS,LHS,RHS),
	Exp=..[Op,LHS,RHS].
normalize_(A,B,Op,Exp) :-     % everything else, leave LHS and RHS alone
	simplify(A,AS),
	num_separate_(AS,LHS,AN),
	simplify(B,BS),
	num_separate_(BS,BS1,BN),
	N is AN-BN,
	(N =:= 0 -> RHS=BS1 ; RHS = BS1+N),
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

occurs_in_(Exp, V) :- var(V), term_variables(Exp,Vs), shared_var_(Vs,V).

shared_vars_(A,B) :-
	term_variables(A,AVs),
	term_variables(B,BVs),
	shared_vars_in_(AVs,BVs).

shared_vars_in_([AV|_AVs],BVs) :-
	shared_var_(BVs,AV), !.
shared_vars_in_([_AV|AVs],BVs) :-
	shared_vars_in_(AVs,BVs).

shared_var_([BV|_BVs],AV) :-
	AV == BV, !.
shared_var_([_BV|BVs],AV) :-
	shared_var_(BVs,AV).


%
% simplify/2
%
simplify(A,A) :- var(A),!.

simplify(C,C) :- rational(C),!.  % includes integers

% possible distribute
simplify(A*B,Exp) :-
	compound(B),
	distribute_(A,B,Exp), !.
simplify(A*B,Exp) :-
	compound(A),
	distribute_(B,A,Exp), !.

% simplify equalities and inequalities
simplify(A==B,Exp) :-
	normalize_(A,B,==,Exp), !.

simplify(A=<B,Exp) :-
	normalize_(A,B,=<,Exp), !.

simplify(A>=B,Exp) :-
	normalize_(A,B,>=,Exp), !.

simplify(A<B,Exp) :-
	normalize_(A,B,<,Exp), !.

simplify(A>B,Exp) :-
	normalize_(A,B,>,Exp), !.
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
	rational(C), !,
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
left_exp_(A,A)  :- A=..[AOp|_], negate_op_(AOp,_), !.
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

collect_exp_items([],[]).
collect_exp_items([E|Es],[NE|NEs]) :-
	collect_exp_item_(Es,E,NE,ENxt), !,
	collect_exp_items(ENxt,NEs).

collect_exp_item_([],E,E,[]).
collect_exp_item_([V|Es],U,Eo,EsNxt) :-
	rational(U), rational(V),  % constant values must be precise to add
	S is U+V,
	collect_exp_item_(Es,S,Eo,EsNxt).
collect_exp_item_([term(V,N1)|Es],term(U,N2),Eo,EsNxt) :-
	V==U,
	(ground(V) -> V =\= 1.0Inf ; true),     % infinities don't obey algebraic rules
	N is N1+N2,
	collect_exp_item_(Es,term(V,N),Eo,EsNxt).
collect_exp_item_([Ei|Es],E,Eo,[Ei|EsNxt]) :-  % Note that imprecise floats are not added
	collect_exp_item_(Es,E,Eo,EsNxt).

reduce_exp_items_([V],V) :-                 % terminate: var
	var(V), !.
reduce_exp_items_([C],C) :-                 % terminate: constant
	rational(C), !.
reduce_exp_items_([term(V,N)],Exp) :- !,    % terminate: single term(_..)
	reduce_exp_items_([0,term(V,N)],Exp).
reduce_exp_items_([Exp],Exp).               % terminate: final expression
reduce_exp_items_([T1,T2|Ts],Exp) :-        % 2 or more terms, combine and continue
	reduce_exp_item_(T1,Op1,Exp1),
	reduce_exp_item_(T2,Op2,Exp2),
	build_exp_(Exp1,Exp2,Op1,Op2,ExpN), !,  % ExpN =.. [Op,Exp1,Exp2], !,
	reduce_exp_items_([ExpN|Ts],Exp).

build_exp_(Z,Exp2,Op1,+,Exp2) :- Z==0.
build_exp_(Z,Exp2,Op1,-,NExp2) :- Z==0, build_Nexp_(Exp2,NExp2).
build_exp_(Exp1,Z,+,Op2,Exp1) :- Z==0.
build_exp_(Exp1,Z,-,Op2,NExp1) :- Z==0, build_Nexp_(Exp1,NExp1).
build_exp_(Exp1,Exp2,+,+,Exp1+Exp2).
build_exp_(Exp1,Exp2,+,-,Exp1-Exp2).
build_exp_(Exp1,Exp2,-,+,Exp2-Exp1).
build_exp_(Exp1,Exp2,-,-,NExp1-Exp2) :- build_Nexp_(Exp1,NExp1).

build_Nexp_(Exp, NExp) :-                                   % constant
	rational(Exp),
	NExp is -Exp.
build_Nexp_(Exp, NExp) :-                                   % * or / expression, find head
	nonvar(Exp), Exp =.. [Op,A1,A2], invert_op_(Op,_),
	build_Nexp_(A1,NA1),
	NExp =.. [Op,NA1,A2].
build_Nexp_(Exp, -Exp).                                     % other expression or var


reduce_exp_item_(V,           +, V)    :- var(V).
reduce_exp_item_(term(V,0),   +, 0)    :- (ground(V) -> V  =\= 1.0Inf ; true).
reduce_exp_item_(term(V,1),   +, V).
reduce_exp_item_(term(V,-1),  -, V).
reduce_exp_item_(term(V,N),   Op, T)   :- mult_term_(V, N, Op, T).
reduce_exp_item_(R,           Op, M)   :- rational(R), val_sign_(R,Op,M).  %  constants
reduce_exp_item_(-Exp,        -, Exp).
reduce_exp_item_(Exp,         +, Exp).

mult_term_(T,   N, Op, M*T)   :- var(T), val_sign_(N,Op,M).
mult_term_(T,   N, Op, V)     :- ground(V), T is V*N.
mult_term_(X*Y, N, Op, Exp*Y) :- mult_term_(X,N,Op,Exp).     % maintain Op associativity
mult_term_(X/Y, N, Op, Exp/Y) :- mult_term_(X,N,Op,Exp).
mult_term_(T,   N, Op, M*T)   :- val_sign_(N,Op,M).

val_sign_(V,Op,Vp) :- Vp is abs(V), (V<0 -> Op = - ; Op = +).

%
% simplify a term to an "expression" of term structures and constants
%
simplify_term(T,Term) :-
	collect_term_(T, L/L, Ts/[]),    % collect in a difference list
	collect_term_items_([1|Ts],[C|Is]),  % ensure there's a constant multiplier and collect like terms
	sort(0, @=<, Is, SIs),
	reduce_term_items_([1|SIs],ITerm),   % reduce back to expression
	% this does constant folding if reduction resulted in a constant
	(rational(ITerm) -> Term is ITerm*C ; Term = term(ITerm,C)),
	!.

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
simplify_pwr_(AT,NT,Term) :- rational(AT), !,  % constant folding
	Term is AT**NT.
simplify_pwr_(Exp**P,NT,elem(Exp,Pwr)) :- integer(NT), rational(P), !,  % (X**P)**NT
	Pwr is NT*P.
simplify_pwr_(AT,NT,elem(AT,NT)).

left_term_(A,A)  :- var(A), !.
left_term_(A,A)  :- A=..[AOp|_], invert_op_(AOp,_), !.
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
collect_term_items_([E|Es],[NE|NEs]) :-
	collect_term_item_(Es,E,NE,ENxt),
	collect_term_items_(ENxt,NEs).

collect_term_item_([],E,E,[]).
collect_term_item_([V|Es],U,Eo,EsNxt) :-
	rational(U), rational(V),  % precise for multiply
	S is U*V,
	collect_term_item_(Es,S,Eo,EsNxt).
collect_term_item_([elem(V,N1)|Es],elem(U,N2),Eo,EsNxt) :-
	V==U, 
	(ground(V) -> V =\= 1.0Inf ; true),    % infinities don't obey algebraic rules
	N is N1+N2,
	collect_term_item_(Es,elem(V,N),Eo,EsNxt).
collect_term_item_([Ei|Es],E,Eo,[Ei|EsNxt]) :-
	collect_term_item_(Es,E,Eo,EsNxt).

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


build_term_(E,    C,   Op, Exp)   :- var(E), Exp =.. [Op,E,C].
build_term_(1,    A**B,/,  A**NB) :- rational(B), NB is -B .
build_term_(1,    Exp, *,  Exp).
build_term_(1,    Exp, /,  1/Exp).
build_term_(One/B,C,   *,  C/B)   :- One==1.
build_term_(E1,   E2,  Op, Exp)   :- Exp =.. [Op,E1,E2].

reduce_term_item_(V,          V, *)     :- var(V),!.  % already reduced to var
reduce_term_item_(elem(_, 0), 1, *).
reduce_term_item_(elem(V, 1), V, *).
reduce_term_item_(elem(V,-1), V, /).
reduce_term_item_(elem(V, E), V**P, Op) :- P is abs(E), (E>0 -> Op= * ; Op= /).
reduce_term_item_(R,          R, *).  % catchall: constant or expression
