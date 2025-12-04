%
% simplify_constraint -  simplify algebraic expressions (esp. clpBNR constraints) for performance
%
/*	The MIT License (MIT)
 *
 *	Copyright (c) 2025 Rick Workman
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
:- module(simplify_constraint, [simplify/2]).

/** <module> simplify_constraint

=|clpBNR/simplify_constraint|= exports a single predicate, =|simplify/2|=, which attempts to reduce expressions, including constraints, to a more optimal form. This module was loosely based on [Simplifying Arithmetic Expressions with Prolog](https://github.com/Couleslaw/Expression-simplification) (licensed under "The  MIT License" as is this module) but modified to:
- support variables (including clpBNR intervals), atoms, floats and strings as "atomic"
- use SWIP native rationals directly
- support constraints (==, =<, =>, ...)
- remove functionality, e.g., multiplication expansion, which don't reduce expressions
- remove support for trig and logarithmic simplification (reduce overhead)
- other optimizations to reduce the number of term "classes"
- remove any floating point arithmetic (imprecise so deferred to constraint building)
- accommodate infinities (and potential infinities through unification)
*/

% ============= debug support ============

:- use_module(library(debug)).

debug_(MsgType,A,V) :-
	(debugging(simplify_constraint)
     -> AA is A+floor(log10(A))+1,  % tab position, compensation for level length
        debug_msg_(MsgType,[A,AA,V],DMsg),
        debug(simplify_constraint,"~w",[DMsg])
     ; true
    ).

debug_msg_(split,Args,DMsg)   :- format(atom(DMsg),"~w~`-t~*|~|> ~w",Args).
debug_msg_(combine,Args,DMsg) :- format(atom(DMsg),"~w~`=t~*|~|> ~w",Args).
debug_msg_(divider,[_,_,V],DMsg) :- format(atom(DMsg),"~w~n% ~`=t~60|",[V]).
debug_msg_(final,[_,_,V],DMsg) :- format(atom(DMsg),"~w~n",[V]).


:- set_prolog_flag(optimise,true).  % for arithmetic, after debug support

/**
simplify(+ExpIn,-ExpOut)

Succeeds when ExpOut is a "simpler" or equivalent form of ExpIn. "Simpler" is defined as a) requiring fewer arithmetic operations, and/or b) fewer occurrences of any included variable. 

Fails if any resultant expression or sub-expression evaluates to NaN.

Generally any expression allowed by the mathematical sub-language of =|library(clpBNR)|= is supported. Atomic values not subject to simplification include variables, numbers, atoms and strings. Only precise rational arithmetic is performed. And there is no expansion of product terms for possible identification of common factors, favouring efficiency over finding optimal solutions.

A final note: `is` constraints are not simplified.
 
Some examples:
==
?- simplify(X+Y-2*X,Exp).
Exp = Y-X.

?- simplify(2*X+1 =< X+5, Exp).
Exp = (X=<4).

?- simplify((X**3)/X, Exp).
Exp = X**2.

?- simplify(sin(X)*sin(X)-cos(X*X), Exp).
Exp = sin(X)**2-cos(X**2).

% X-X cannot be fully simplified to 0 if X can be infinite
?- simplify(X-X, Exp).
Exp = 0*X.

% `is` constraints are not simplified
?- simplify(Z is X+Y+X,Exp).
Exp = (Z is X+Y+X).

% Unexpanded form is simpler than X**2 * Y**2
?- simplify((X*Y)**2, Exp).
Exp = (X*Y)**2.

% fail if sub-expression is not defined
?- simplify(X+0/0, Exp).
false.
==
*/
simplify(V, V) :- var(V), !.
simplify(A is  B, A is  B) :- !.  % no simplification for is (undocumented)
simplify(A ==  B, L ==  R) :- !, simplify_(A-B,Exp), c_exp_(Exp,L,R).
simplify(A =:= B, L =:= R) :- !, simplify_(A-B,Exp), c_exp_(Exp,L,R).
simplify(A =<  B, L =<  R) :- !, simplify_(A-B,Exp), c_exp_(Exp,L,R).
simplify(A >=  B, L >=  R) :- !, simplify_(A-B,Exp), c_exp_(Exp,L,R).
simplify(A  <  B, L  <  R) :- !, simplify_(A-B,Exp), c_exp_(Exp,L,R).
simplify(A  >  B, L  >  R) :- !, simplify_(A-B,Exp), c_exp_(Exp,L,R).
simplify(<>(A,B), <>(L,R)) :- !, simplify_(A-B,Exp), c_exp_(Exp,L,R).  % non-standard op
simplify(Exp,     NExp)    :-    simplify_(Exp, NExp).  % non-constraint expressions

simplify_(A-B, Exp) :-   % optimize common constraint case, preserve values
	( (var(A), atomic(B)) ; (var(B), atomic(A)) ),  % skip analyse_ step
	!,
	reduce_(A-B,Exp).
simplify_(Exp, NExp) :- 
	analyse_(Exp,SExp,1),
	reduce_(SExp,NExp).

reduce_(SExp,NExp) :-
	debug_(divider,1,SExp),
	normalize_(SExp,NExp,1),
	debug_(final,1,NExp).

% reconstruct left and right hand sides of constraint
% Note, for some cases must switch sides to use same operator (=<, =>, ..)
c_exp_(X,     X,0)      :- var(X), !.  % avoids any unification below
% since nominal RHS is 0, can remove non-zero factors
c_exp_(-X,    RHS,LHS)  :- !, c_exp_(X, LHS,RHS).  % factor = -1
c_exp_(Lf*R,  LHS,RHS)  :- rational(Lf), cancel_factor_(Lf,R,LHS,RHS), !.
c_exp_(L*Rf,  LHS,RHS)  :- rational(Rf), cancel_factor_(Rf,L,LHS,RHS), !.
c_exp_(L/Rf,  LHS,RHS)  :- rational(Rf), cancel_factor_(Rf,L,LHS,RHS), !.
% distribute sums and differences if efficient
c_exp_(L+R,   R,LHS)    :- number(R), exp_fargs(L, [-,LHS]), !.
c_exp_(L-R,   RHS,LHS)  :- number(R), exp_fargs(L, [-,LHS]), !, RHS is -R.
c_exp_(LHS+R, LHS,RHS)  :- number(R), !, RHS is -R.
c_exp_(LHS-R, LHS,R)    :- number(R), !.
c_exp_(Exp,   LHS,RHS)  :- exp_fargs(Exp, [-,LHS,RHS]), !.
% general case
c_exp_(Exp,   Exp,0).

cancel_factor_(F,X,L,R) :-
	(F > 0 -> c_exp_(X,L,R)
	;F < 0 -> c_exp_(X,R,L)  % if factor negative swap sides for inequalities
	).                       % fails if factor is 0

% ============= some common utilities ============

exp_fargs(Exp,Fargs) :- compound(Exp), Exp =.. Fargs.

equals_num(X,Num) :-  % test for precise arithmetic equivalence
	(rational(X)
	 -> X==Num
	 ;  float(X), \+ float_class(X,infinite), 0 is cmpr(Num,rationalize(X))
	).

infinite(Inf) :- float(Inf), float_class(Inf,infinite).

% ============= "analyse" input to canonical form ============

analyse_(R,R,_L) :- rational(R), !.
analyse_(X,_,_) :- (X == nan ; X == 1.5NaN) -> !,fail.  % NaN's illegal
analyse_(V,ZV,L) :-
	compound(V), !,
	V =.. [Func|FArgs],
	debug_(split,L,V),
	L1 is L+1,
	analyse_args(FArgs,Args,L1),
	s(Func,Args,ZV),
	debug_(combine,L,ZV).
analyse_(X,Inf,_L) :- (X == inf -> Inf = x(1.0Inf) ; infinite(X), Inf=x(X)), !.  % infinities
analyse_(X,a(X),_L).  % vars and other atomics

analyse_args([],[],_A).
analyse_args([Arg|Args],[ZArg|ZArgs],A) :-
	analyse_(Arg,ZArg,A),
	analyse_args(Args,ZArgs,A).

% ============= "normalize" canonical form to output ============

normalize_(R,R,_L) :- rational(R), !.
normalize_(X,X,_L) :- (var(X); atomic(X)), !.
normalize_(x(X),X,_L) :- !.  % infinity
normalize_(a(X),Z,L) :- !,
	normalize_(X,Z,L).
normalize_(b(B),Z,L) :- !,
	normalize_(B,Z,L).
normalize_(c(R*Bs),Z,L) :- !,
	(Bs == []
	 -> Z=R
	 ;	normalize_args(Bs,[Bn1|BsN],L),
	    n_cc([R*Bn1|BsN],Bexp),
	    normalize_(Bexp,Z,L)
	).
normalize_(d(R+Cs),Z,L) :- !,
	(Cs == []
	 -> Z = R
	 ;  normalize_args(Cs,CsN,L),
	    n_dd(CsN,Cexp),
	    (R>0 -> normalize_(Cexp+R,Z,L) ; Rn is -R, normalize_(Cexp-Rn,Z,L))
	).
normalize_(V,ZV,L) :-
	V =.. [Func|FArgs],
	debug_(split,L,V),
	L1 is L+1,
	normalize_args(FArgs,Args,L1),
	n(Func,Args,ZV),
	debug_(combine,L,ZV).

normalize_args([],[],_A).
normalize_args([Arg|Args],[ZArg|ZArgs],A) :-
	normalize_(Arg,ZArg,A),
	normalize_args(Args,ZArgs,A).

% ============= general s rules ============

s(^,Args,R) :- !, s(**,Args,R).

% ========== rational operations =========

% Note:need to guard against conversion of rationals to floats
s(-,[A],X) :- rational(A), !,
	X is -A.

s(+,[A,B],X) :- rational(A), rational(B),
	X is A+B, rational(X), !.

s(-,[A,B],X) :- rational(A), rational(B),
	X is A-B, rational(X), !.

s(*,[A,B],X) :- rational(A), rational(B),
	X is A*B, rational(X), !.

s(/,[A,B],X) :- rational(A), rational(B),
	X is A/B, rational(X), !.

s(**,[A,B],X) :- rational(A), rational(B),
	X is A**B, rational(X), !.

% ========== type a(X) operations =========
s(-, [a(X)], C) :- !,
	s(-, [b(a(X)**1)], C).

s(+, [a(X), R], D) :- rational(R), !,
	s(+, [b(a(X)**1),R],D).
s(+, [R, a(X)], D) :- rational(R), !,
	s(+, [R, b(a(X)**1)],D).
s(+, [a(X1), a(X2)], D) :-  !,
	s(+, [b(a(X1)**1),b(a(X2)**1)], D).

s(-, [a(X), R], D) :- rational(R), !,
	s(-, [b(a(X)**1),R],D).
s(-, [R, a(X)], D) :- rational(R), !,
	s(-, [R, b(a(X)**1)],D).
s(-, [a(X1), a(X2)], D) :-  !,
	s(-, [b(a(X1)**1),b(a(X2)**1)], D).

s(*, [a(X), R], C) :- rational(R), !,
	s(*, [b(a(X)**1),R],C).
s(*, [R, a(X)], C) :- rational(R), !,
	s(*, [b(a(X)**1),R], C).
s(*, [a(X1), a(X2)], C) :-  !,
	s(*, [b(a(X1)**1),b(a(X2)**1)], C).

s(/, [a(X), R], C) :- rational(R), !,
	s(/, [b(a(X)**1),R],C).
s(/, [R, a(X)], C) :- rational(R), !,
	s(/, [R, b(a(X)**1)],C).
s(/, [a(X1), a(X2)], C) :-  !,
	s(/, [b(a(X1)**1),b(a(X2)**1)], C).

s(**, [a(X), R], b(a(X)**R)) :- rational(R), !.

% ========== type b(A**R) operations =========
s(-, [b(B)], c(-1*[b(B)])) :- !.

s(+, [b(B), R], D) :- rational(R), !,
	s(+, [c(1*[b(B)]), R], D).
s(+, [R, b(B)], D) :- rational(R), !,
	s(+, [c(1*[b(B)]), R], D).
s(+, [b(B), a(X)], D) :- !,
	s(+, [c(1*[b(B)]), c(1*[b(a(X)**1)])], D).
s(+, [a(X), b(B)], D) :- !,
	s(+, [c(1*[b(a(X)**1)]), c(1*[b(B)])], D).
s(+, [b(B1), b(B2)], D) :- !,
	s(+, [c(1*[b(B1)]),c(1*[b(B2)])], D).

s(-, [b(B), R], D) :- rational(R), !,
	s(-, [c(1*[b(B)]), R], D).
s(-, [R, b(B)], D) :- rational(R), !,
	s(+, [R, c(-1*[b(B)])], D).
s(-, [b(B), a(X)], D) :- !,
	s(+, [c(1*[b(B)]), c(-1*[b(a(X)**1)])], D).
s(-, [a(X), b(B)], D) :- !,
	s(+, [c(1*[b(a(X)**1)]), c(-1*[b(B)])], D).
s(-, [b(B1), b(B2)], D) :-  !,
	s(+, [c(1*[b(B1)]),c(-1*[b(B2)])], D).

s(*, [b(B), R], C) :- rational(R), !,
	C = c(R*[b(B)]).
s(*, [R, b(B)], C) :- rational(R), !,
	C = c(R*[b(B)]).
s(*, [b(B), a(X)], C) :- !,
	s(*, [b(B), b(a(X)**1)], C).
s(*, [a(X), b(B)], C) :- !,
	s(*, [c(1*[b(a(X)**1)]), c(1*[b(B)])], C).
s(*, [b(B1), b(B2)], C) :-  !,
	s(*, [c(1*[b(B1)]), c(1*[b(B2)])], C).

s(/, [b(B), R2], C) :- rational(R2), !,
	R is 1/R2,
	C = c(R*[b(B)]).
s(/, [R, b(A1**R1)], C) :- rational(R), !,
	R1n is -R1,
	s(*, [R, b(A1**R1n)],C).
s(/, [b(B), a(X)], C) :- !,
	s(*, [b(B), b(a(X)** -1)], C).
s(/, [a(X), b(B)], C) :- !,
	s(/, [c(1*[b(a(X)**1)]), c(1*[b(B)])], C).
s(/, [b(B1), b(B2)], C) :-  !,
	s(/, [c(1*[b(B1)]), c(1*[b(B2)])], C).

s(**, [b(a(X)**R1), R2], b(a(X)**R)) :- rational(R1), rational(R2), !,
	R is R1*R2.

% ========== type c(R*Bs) operations =========
s(-, [c(R*Bs)], c(Rn*Bs)) :- !,
	Rn is -R.

s(+, [c(C), R], D) :- rational(R), !,
	D = d(R+[c(C)]).
s(+, [R, c(C)], D) :- rational(R), !,
	D = d(R+[c(C)]).
s(+, [c(C), a(X)], D) :- !,
	s(+, [c(C), c(1*[b(a(X)**1)])], D).
s(+, [a(X), c(C)], D) :- !,
	s(+, [c(1*[b(a(X)**1)]), c(C)], D).
s(+, [c(C), b(B)], D) :- !,
	s(+, [c(C), c(1*[b(B)])], D).
s(+, [b(B), c(C)], D) :- !,
	s(+, [c(1*[b(B)]), c(C)], D).
s(+, [c(C1), c(C2)], D) :-  !,
	append_c([c(C1)],c(C2),Cs),
	D = d(0+Cs).

s(-, [c(C), R], D) :- rational(R), !,
	Rn is -R,
	D = d(Rn+[c(C)]).
s(-, [R, c(R2*Bs)], D) :- rational(R), !,
	R2n is -R2,
	D = d(R+[c(R2n*Bs)]).
s(-, [c(C), a(X)], D) :- !,
	s(-, [c(C), c(1*[b(a(X)**1)])], D).
s(-, [a(X), c(C)], D) :- !,
	s(-, [c(1*[b(a(X)**1)]), c(C)], D).
s(-, [c(C), b(B)], D) :- !,
	s(-, [c(C), c(1*[b(B)])], D).
s(-, [b(B), c(C)], D) :- !,
	s(-, [c(1*[b(B)]), c(C)], D).
s(-, [c(C1), c(R2*B2s)], D) :-  !,
	R2n is -R2,
	append_c([c(C1)],c(R2n*B2s),Cs),
	D = d(0+Cs).

s(*, [c(R1*B1s), R2], C) :- rational(R2), !,
	R is R1*R2,
	C = c(R*B1s).
s(*, [R1, c(R2*B2s)], C) :- rational(R1), !,
	R is R1*R2,
	C = c(R*B2s).
s(*, [c(C1), a(X)], C) :- !,
	s(*, [c(C1), c(1*[b(a(X)**1)])], C).
s(*, [a(X), c(C2)], C) :- !,
	s(*, [c(1*[b(a(X)**1)]), c(C2)], C).
s(*, [c(C1), b(B)], C) :- !,
	s(*, [c(C1), c(1*[b(B)])], C).
s(*, [b(B), c(C2)], D) :- !,
	s(*, [c(1*[b(B)]), c(C2)], D).
s(*, [c(R1*B1s), c(R2*B2s)], C) :-  !,
	R is R1*R2,
	merge_b(B2s,B1s,Bs),
	C = c(R*Bs).

s(/, [c(R1*B1s), R2], C) :- rational(R2), !,
	R is R1/R2,
	C = c(R*B1s).
s(/, [R1, c(R2*B2s)], C) :- rational(R1), !,
	R is R1/R2,
	invert_bs(B2s,B2si),
	C = c(R*B2si).
s(/, [c(C1), a(X)], C) :- !,
	s(/, [c(C1), c(1*[b(a(X)**1)])], C).
s(/, [a(X), c(C2)], C) :- !,
	s(/, [c(1*[b(a(X)**1)]), c(C2)], C).
s(/, [c(C1), b(B)], C) :- !,
	s(/, [c(C1), c(1*[b(B)])], C).
s(/, [b(B), c(C2)], C) :- !,
	s(/, [c(1*[b(B)]), c(C2)], C).
s(/, [c(R1*B1s), c(R2*B2s)], C) :- !,
	R is R1/R2,
	invert_bs(B2s,B2si),
	merge_b(B2si,B1s,Bs),
	C = c(R*Bs).

s(**, [c(R1*B1s), R], B) :- rational(R), !,
	s(**, [a(c(R1*B1s)), R], B).

% ========== type d(R+Cs) operations =========
s(-, [d(R+Cs)], d(Rn+Csn)) :- !,
	Rn is -R,
	negate_cs(Cs,Csn).

s(+, [d(R1+Cs), R2], D) :- rational(R2), !,
	R is R1+R2,
	D = d(R+Cs).
s(+, [R1, d(R2+Cs)], D) :- rational(R1), !,
	R is R1+R2,
	D = d(R+Cs).
s(+, [d(D1), a(X)], D) :- !,
	s(+, [d(D1), b(a(X)**1)], D).
s(+, [a(X), d(D2)], D) :- !,
	s(+, [b(a(X)**1), d(D2)], D).
s(+, [d(D1), b(B)], D) :- !,
	s(+, [d(D1), c(1*[b(B)])], D).
s(+, [b(B), d(D2)], D) :- !,
	s(+, [c(1*[b(B)]), d(D2)], D).
s(+, [d(R1+C1s), c(C2)], D) :- !,
	append_c(C1s,c(C2),Cs),
	D = d(R1+Cs).
s(+, [c(C1), d(R2+C2s)], D) :- !,
	append_c(C2s,c(C1),Cs),
	D = d(R2+Cs).
s(+, [d(R1+C1s), d(R2+C2s)], D) :-  !,
	R is R1+R2,
	merge_c(C1s,C2s,Cs),
	D = d(R+Cs).

s(-, [d(R1+Cs), R2], D) :- rational(R2), !,
	R is R1-R2,
	D = d(R+Cs).
s(-, [R1, d(R2+C2s)], D) :- rational(R1), !,
	R is R1-R2,
	negate_cs(C2s,C2sn),
	D = d(R+C2sn).
s(-, [d(D1), a(X)], D) :- !,
	s(-, [d(D1), b(a(X)**1)], D).
s(-, [a(X), d(D2)], D) :- !,
	s(-, [b(a(X)**1), d(D2)], D).
s(-, [d(D1), b(B)], D) :- !,
	s(-, [d(D1), c(1*[b(B)])], D).
s(-, [b(B), d(D2)], D) :- !,
	s(-, [c(1*[b(B)]), d(D2)], D).
s(-, [d(D1), c(R2*C2s)], D) :- !,
	R2n is -R2,
	s(+, [d(D1), c(R2n*C2s)], D).
s(-, [c(C1), d(D2)], D) :- !,
	s(-, [d(0+[c(C1)]), d(D2)], D).
s(-, [d(R1+C1s), d(R2+C2s)], D) :-  !,
	R is R1-R2,
	negate_cs(C2s,C2sn),
	merge_c(C1s,C2sn,Cs),
	D = d(R+Cs).

s(*, [d(R1+C1s), R2], d(R+Cs)) :- rational(R2),
	R is R1*R2, rational(R),
	mult_cs(C1s,R2,Cs),
	!.
s(*, [R1, d(R2+C2s)], d(R+Cs)) :- rational(R1),
	R is R1*R2, rational(R),
	mult_cs(C2s,R1,Cs),
	!.
s(*, [d(D1), d(D2)], C) :- !,
	s(*, [a(d(D1)), a(d(D2))], C).
s(*, [d(D1), X], C) :- !,
	s(*, [a(d(D1)), X], C).
s(*, [X, d(D2)], C) :- !,
	s(*, [X, a(d(D2))], C).

s(/, [d(R1+C1s), R2], d(R+Cs)) :- rational(R2), C1s = [c(Rc1*B1s)],
	R is R1/R2, rational(R),
	Rc is Rc1/R2, rational(Rc),
	!,
	Cs = [c(Rc*B1s)].
s(/, [d(D1), d(D2)], E) :- !,
	s(/, [a(d(D1)), a(d(D2))], E).
s(/, [d(D1), X], C) :- !,
	s(/, [a(d(D1)), X], C).
s(/, [X, d(D2)], C) :- !,
	s(/, [X, a(d(D2))], C).

s(**, [d(D), R], B) :- rational(R), !,
	s(**, [a(d(D)), R], B).

% ========== no simplifying operations =========

s(Func, Args, a(Z)) :- Z =.. [Func|Args].

% ========== s utilities =========

merge_b([],Bs,Bs).
merge_b([B1|B1s],B2s,Bs) :-
	append_b(B2s,B1,B2sN),
	merge_b(B1s,B2sN,Bs).
	
append_b([],B,[B]).
append_b([b(A1**R1)|B1s],b(A2**R2),Bs) :-
	(equal_term_(A1, A2)
	 -> R is R1+R2,
	    (R==0 -> Bs = B1s ; Bs = [b(A1**R)|B1s])
	 ;  Bs = [b(A1**R1)|BsN],
	    append_b(B1s,b(A2**R2),BsN)
	 ).
	
invert_bs([],[]).
invert_bs([b(A1**R1)|Bs], [b(A1**R1n)|Bsi]) :-
	R1n is -R1,
	invert_bs(Bs,Bsi).

merge_c([],Bs,Bs).
merge_c([B1|B1s],B2s,Bs) :-
	append_c(B2s,B1,B2sN),
	merge_c(B1s,B2sN,Bs).
	
append_c([], c(C), [c(C)]).
append_c([c(R1*B1s)|C1s], c(R2*B2s), Cs) :-
	(equal_list_(B1s,B2s)
	 -> R is R1+R2, 
	    Cs = [c(R*B1s)|C1s]
	 ;  Cs = [c(R1*B1s)|CsN],
	    append_c(C1s, c(R2*B2s), CsN)
	).

negate_cs([],[]).
negate_cs([c(R*Bs)|Cs], [c(Rn*Bs)|Csn]) :-
	Rn is -R,
	negate_cs(Cs,Csn).

mult_cs([],_,[]).
mult_cs([c(R*Bs)|Cs],Rm,[c(Rp*Bs)|Csp]) :-
	Rp is R*Rm, rational(Rp),
	mult_cs(Cs,Rm,Csp).

equal_term_(T1,T2) :- 
	((var(T1) ; var(T2)) ->  ! ; true),  % no alternatives if either var
	T1==T2,                       % identical terms
	!.
equal_term_(a(T1),a(T2)) :- !, equal_term_(T1,T2).
equal_term_(b(T1**R),b(T2**R)) :- !, equal_term_(T1,T2), !.
equal_term_(c(R*B1s),c(R*B2s)) :- !, equal_list_(B1s,B2s).
equal_term_(d(R+C1s),d(R+C2s)) :- !, equal_list_(C1s,C2s).

equal_list_([],[]).
equal_list_([BB1|BB1s],BB2s) :-
	select_item_(BB2s,BB1,NxtBB2s),
	equal_list_(BB1s,NxtBB2s).
	
select_item_([BB2|BB2s],BB1,NxtBB2s) :- 
	(equal_term_(BB1,BB2)  %%BB1 == BB2
	 ->	NxtBB2s = BB2s
	 ;  NxtBB2s = [BB2|BB2s1],
	    select_item_(BB2s,BB1,BB2s1)
	).

% ========== normalization =========

n(^,Args,R) :- !, n(**,Args,R).  % just a precaution

% Note: no unifications in n/3 head of arguments parm 
n(-,[X],Rxn) :- !, (number(X) -> Rxn is -X ; Rxn = -X).

n(+,[Zero,X],X) :- equals_num(Zero,0), !.
n(+,[X,Zero],X) :- equals_num(Zero,0), !.
n(+,[X,R],X-Rp) :- rational(R), R<0,!, Rp is -R.
n(+,[X,Y],X-Rp*Y1) :- exp_fargs(Y,[*,R,Y1]), rational(R), R<0,!, Rp is -R.
n(+,[X,Y],Y-Xp) :- exp_fargs(X, [-,Xp]), !.
n(+,[X,Y],Z) :- infinite_args(X,Y), Z is X+Y, !, Z \== 1.5NaN.
n(+,[X,Y],X+Y)  :- !.

n(-,[Zero,X],Xn) :- equals_num(Zero,0), !, n(-,[X],Xn).
n(-,[X,Zero],X) :- equals_num(Zero,0), !.
n(-,[X,Y],Z) :- rational(Y), exp_fargs(X,[*,R,X1]), rational(R), R =\= 0, !, 
	RY is Y/R, 
	n(*,[R,X1-RY], Z).  % common rational factor for subtraction, worthwhile special case for constraints
n(-,[X,Y],Z) :- infinite_args(X,Y), Z is X-Y, !, Z \== 1.5NaN.
n(-,[X,Y],0) :- equal_term_(X,Y), !.
n(-,[X,Y],X-Y) :- !.

n(*,[X,Y],X) :-  equals_num(X,0), finite_exp(Y), !.
n(*,[X,Y],Y) :-  equals_num(Y,0), finite_exp(X), !.
n(*,[One,X],X) :- equals_num(One,1), !.
n(*,[X,One],X) :- equals_num(One,1), !.
n(*,[NOne,X],Xn) :- equals_num(NOne,-1), !, n(-,[X],Xn).
n(*,[X,NOne],Xn) :- equals_num(NOne,-1), !, n(-,[X],Xn).
n(*,[R1,X],Z) :- rational(R1), exp_fargs(X, [/,R2,Xd]), rational(R2), !, 
	R is R1*R2, rational(R),
	n(/,[R,Xd],Z).
n(*,[X,Y],Z) :- exp_fargs(X, [/,One,Xd]), equals_num(One,1), !,
	n(/,[Y,Xd],Z).
n(*,[X,Y],Z) :- infinite_args(X,Y), Z is X*Y, !, Z \== 1.5NaN.
n(*,[X,Y],X*Y) :- !.

n(/,[XZero,YZero],_) :- equals_num(XZero,0), equals_num(YZero,0), !, fail.  % NaN
n(/,[X,Y],Z) :- infinite_args(X,Y), Z is X/Y, !, Z \== 1.5NaN.
n(/,[X,Y],X/Y) :- !.

n(**,[_,Zero],1) :- equals_num(Zero,0), !.  % including infinities
n(**,[One,_],One) :- equals_num(One,1), !.
n(**,[X,One],X) :- equals_num(One,1), !.
n(**,[X,NOne],Z) :- equals_num(NOne,-1), !, n(/,[1,X],Z).
n(**,[X,Ry],Z) :- rational(Ry), exp_fargs(X,[**,XX,Rx]), rational(Rx),
	R is Rx+Ry, rational(R),
	!,
	n(**,[XX,R],Z).
n(**,[X,Y],Z) :- infinite_args(X,Y), Z is X**Y, !, Z \== 1.5NaN.
n(**,[X,Y],X**Y) :- !.

n(Func, Args, Z) :- Z =.. [Func|Args].

% ========== n utilities =========

infinite_args(X,Y) :- (infinite(X), number(Y); infinite(Y), number(X)).

finite_exp(X) :- (var(X) ; infinite(X)), !, fail.
finite_exp(X) :- atomic(X).
finite_exp(F) :- functor(F,Fn,_), memberchk(Fn,[sin,cos,asin,acos,atan]).  % known finite value

n_cc([B],B) :- !. 
n_cc([B1,B2|Bs],E) :- exp_fargs(B2,[**,X,R]), rational(R), !, 
	(R < 0 -> Rp is -R, NxtB1 = B1/X**Rp ; NxtB1 = B1*B2),
	n_cc([NxtB1|Bs],E).
n_cc([B,X|Bs],E) :-  exp_fargs(X, [/,1,Xi]), !,
	n_cc([B/Xi|Bs],E). 
n_cc([B,X|Bs],E) :-  
	n_cc([B*X|Bs],E). 

n_dd([CC],CC) :- !.  % terminal case
n_dd([C|CCs],E) :- compound(C), negative_exp_(C,Cp), !,  % defer leading negative, non-rational items
	n_dd(CCs,E1),
	E = E1-Cp.
n_dd([C1,C2|CCs],E) :- negative_exp_(C2,C2p), !,  % use subtract for negative second arg 
	n_dd([C1-C2p|CCs],E).
n_dd([C1,C2|CCs],E) :-                            % simple add 
	n_dd([C1+C2|CCs],E).

negative_exp_(Y,Yp) :- rational(Y), !,
	Y < 0,
	Yp is -Y.
negative_exp_(Y,Yp) :- 
	exp_fargs(Y, [-,Yp]),
	!.
negative_exp_(Y,Yp) :- 
	exp_fargs(Y, [COp,Y1,Y2]),
	prod_op_(COp),
	negative_exp_(Y1,Y1p),
	Yp =.. [COp,Y1p,Y2].

prod_op_(*).
prod_op_(/).
