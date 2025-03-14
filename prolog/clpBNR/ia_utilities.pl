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
% compatibility predicate
%
/** 
print_interval(?T) is semidet

Succeeds printing term T with interval expanded to domains and vars labelled =V=*; fails if output fails. Provided for historical compatibility, use system output facilities instead. Example:
==
?- X::real,print_interval(f(X)),X=42.
f(V0::real(-1.0e+16,1.0e+16))
X = 42.
==
@deprecated use =|format/2|=
*/
/**  
print_interval(+Stream,?T) is semidet

Same as =|print_interval|= with output to a stream. It uses =|format/3|= so extended stream options, e.g., atom(A), are supported.

@deprecated use =|format/3|=
 */
print_interval(Term) :- 
	printed_term_(Term,Out),
	format('~w',[Out]).          % safe

print_interval(Stream,Term) :-
	printed_term_(Term,Out),
	format(Stream,'~w',[Out]).   % unsafe

printed_term_(Term,Out) :-
	copy_term_nat(Term,Out),     % copy of Term without attributes for output
	term_variables(Term,TVars),
	term_variables(Out,OVars),
	name_vars_(TVars,OVars,0).   % name variables, intervals replaced by declarations

name_vars_([],[],_).
name_vars_([TVar|TVars],[OVar|OVars],N) :-
	(domain(TVar,Dom)
	 -> OVar = (V::Dom)
	  ; OVar = V
	),
	number_chars(N,C),atom_chars(V,['V'|C]),
	N1 is N+1,
	name_vars_(TVars,OVars,N1).

%
% SWIP attribute portray hook - used if write_attributes=portray
%
attr_portray_hook(interval(Type,Val,_Node,_Flags),_Int) :-
	interval_domain_(Type,Val,Dom),
	format('~w',[Dom]).                     % safe

%
% Support ellipsis format in answers
%
user:portray(Term) :-          % remove quotes on stringified number in ellipsis format
	nonvar(Term), Term = '$clpBNR...'(Out),  % avoid unifying with variable(Term) 
	string(Out),
	format('~W...',[Out,[quoted(false)]]).  % safe

%
% SWIP hooks for answer formatting - two modes : 
%	Verbose=true,  display all interval domains and associated constraints
%	Verbose=false, display var domains with no constraints - internal vars omitted
%
user:expand_answer(Bindings,Bindings) :-              % for toplevel answer control
	\+term_attvars(Bindings,[]),                      % fail to alternatives if no attributes 
	current_prolog_flag(clpBNR_verbose,Verbose),      % save verbose mode in attributes
	add_names_(Bindings,Verbose,IntFlag),
	nonvar(IntFlag).                                  % at least one interval in bindings

% annotate interval variables in Bindings
add_names_([],_,_).
add_names_([Name = Var|Bindings],Verbose,IntFlag) :-
	(get_interval_flags_(Var,Flags)
	 -> set_interval_flags_(Var,[name(Name,Verbose)|Flags]),         % mainly to attach Verbose
	    (Verbose == false -> reset_interval_nodelist_(Var) ; true),  % Nodes restored on backtrack
	    IntFlag = true
	 ;  term_attvars(Var,AVars),                     % Var not an interval, but may contain them
	    nested_bindings_(AVars,Var,NBindings),       % new bindings
	    add_names_(NBindings,Verbose,IntFlag)        % mark any internal intervals 
	),
	add_names_(Bindings,Verbose,IntFlag).

nested_bindings_([],_Var,[]).
nested_bindings_([V|Vars],Var,NVars)  :- 
	(V==Var                     % loop detection
	 -> RVars = NVars           % and removal
	 ;  NVars = ['' = V|RVars]  % no-name Var
	),
	nested_bindings_(Vars,Var,RVars).

%
%  SWISH versions:
%
:- if(current_prolog_flag(clpBNR_swish, true)).

% portray (HTML)
:- multifile(term_html:portray//2).

term_html:portray(Term,_) -->   % avoid quotes on stringified number in ellipsis format
	{ nonvar(Term), Term = '$clpBNR...'(Out),  % avoid unifying with variable(Term)
	  string(Out)
	},
	html(span(class('pl-float'), [Out, '...'])).

% for answer formatting
:- multifile(swish_trace:post_context/1).

swish_trace:post_context(Dict) :-
	expand_answer(Dict.bindings,_).

:- endif.  % current_prolog_flag(clpBNR_swish, true)

%
% Constructs goals to build interval(X)
%
attribute_goals(X) -->
	{(interval_object(X, Type, Val, Nodes)
 	  -> (get_interval_flags_(X,Flags), memberchk(name(_,false),Flags), var(Nodes) 
 	      -> intValue_(Val,Type,Dom),           % non-verbose and empty nodelist => "pretty" value
	         Goals = [X::Dom]
	      ;  interval_domain_(Type, Val, Dom),  % full copy 
	         constraints_(Nodes,X,Cs),          % reverse map to list of original constraints
	         to_comma_exp_(Cs,X::Dom,Goals)
	     )
	  ;  Goals = []
	 )
	},
	list_dcg_(Goals).  % avoids "unsafe" call to phrase/3

list_dcg_([]) --> [].
list_dcg_([H|T]) --> [H], list_dcg_(T).

constraints_([Node],_,[]) :- var(Node), !.  % end of indefinite list
constraints_([node(Op,P,_,Args)|Nodes],X,[C|Cs]) :-
	var(P),                       % skip persistent nodes (already in value)
	term_variables(Args,[V|_]),   % this ensures constraints only get output once
	V==X,
	map_constraint_op_(Op,Args,C),
	constraints_(Nodes,X,Cs).
constraints_([_|Nodes],X,Cs) :-
	constraints_(Nodes,X,Cs).
		
to_comma_exp_([],Decl,[Decl]).
to_comma_exp_([N|NCs],Decl,[(Decl,{Cs})]) :-
	to_comma_cexp_(NCs,N,Cs).

to_comma_cexp_([],In,In).
to_comma_cexp_([C|Cs],In,Out) :-
	to_comma_cexp_(Cs,(In,C),Out).

%
%  Simplified output format for interval ranges
%
% 1. Any 'real' rational bounds output as floats (conservatively rounded).
% 2. Any subnormal bounds converted to zero.
% 3. Sufficiently narrow reals output in ellipsis format.
% 4. Any real intervals with bounds zero or subnormal output as 0.0...
% 5. Query interval variables output as V = V::Domain
% 6. Subterm intervals as sub-terms printed as domain (Type(L,H)).
%
intValue_((0,1),integer,boolean).                  % boolean
intValue_((L,H),real,'$clpBNR...'(Out)) :-         % virtual zero (zero or subnormal) 
	zero_float_(L),
	zero_float_(H), !,
	format(chars(Zero),"~16f",[0.0]),
	string_chars(Out,[' '|Zero]).                  % space prefix 
intValue_((L,H),real,'$clpBNR...'(Out)) :-         % two floats with minimal leading match
	float_chars_(L,LC),
	float_chars_(H,HC),
	sign_chars_(LC,HC,ULC,UHC,Codes/Match),
	leading_zero(ULC,UHC,ZLC),
	matching_(ZLC,UHC,Match,0,Dec,MLen),
	MLen>Dec+1, !,	% minimum of one matching digit after decimal point
	string_codes(Out,Codes).
intValue_((L,H),Type,Dom) :-                       % default, just convert rationals
	rational_fraction_(L,FL),
	rational_fraction_(H,FH),
	interval_domain_(Type, (FL,FH), Dom).

zero_float_(B) :- float(B), float_class(B,C), (C=zero ; C=subnormal).

float_chars_(B,Cs) :-
	rational_fraction_(B,F),
	float(F), float_class(F, normal),
	format(chars(Cs),'~16f',[F]),  % same length after '.' (pads with trailing 0's)
	length(Cs,Len), Len=<32.       % reverts to precise format if too long

rational_fraction_(B,FB) :-
	rational(B,_,D), D \= 1, !,    % non-integer rational
	FB is float(B).
rational_fraction_(F,0.0) :- 
	float(F),
	float_class(F,subnormal), !.
rational_fraction_(B,B).

sign_chars_(['-'|LC],['-'|HC],HC,LC,[' ','-'|T]/T) :- !.  % negate, save sign and reverse bounds
sign_chars_(LC,HC,LC,HC,[' '|T]/T).  % need a character that doesn't print: 2=STX (Start of Text)

leading_zero(['9'|ULC],['1','0'|_],['0','9'|ULC]) :- !.
leading_zero(ULC,_,ULC).

% Note: match should never be exact (L=H) so [] case not required
% matching_([],[],[],N,Dec,N).
matching_([C,'.'|LCs],[C,'.'|HCs],[C,'.'|Cs],N,Dec,Nout) :-   !, % absorbing "."
	digit_(C,_),
	Dec is N+1,
	N1 is N+2,
	matching_(LCs,HCs,Cs,N1,Dec,Nout).
matching_([LC,'.',LC1|LCs],[HC,'.',HC1|HCs],[HC,'.'|Cs],N,Dec,Nout) :-  !,  % absorbing "."
	digit_match_(LC,LC1,HC,HC1),
	Dec is N+1,
	N1 is N+2,
	matching_([LC1|LCs],[HC1|HCs],Cs,N1,Dec,Nout).
matching_([C|LCs],[C|HCs],[C|Cs],N,Dec,Nout) :- !,  % matching digit
	digit_(C,_),
	N1 is N+1,
	matching_(LCs,HCs,Cs,N1,Dec,Nout).
matching_([LC,LC1|LCs],[HC,HC1|HCs],[HC|Cs],N,Dec,Nout) :- % match after rounding
	digit_match_(LC,LC1,HC,HC1), !,
	N1 is N+1,
	matching_([LC1|LCs],[HC1|HCs],Cs,N1,Dec,Nout).
matching_(_LCs,_HCs,[],N,Dec,N) :-                  % non-matching after '.'
	nonvar(Dec). 

digit_match_(LC,LC1,HC,HC1) :-  % rounding test if first digits different
	digit_(LC,L), digit_(LC1,L1), digit_(HC,H), digit_(HC1,H1),
	H is (L+1) mod 10,
	L1 >= 5, H1 < 5.

% char test for properly formatted number 
digit_(DC,D) :- atom_number(DC,D), integer(D), 0=<D,D=<9.

/** 
enumerate(?Term:term_List) is nondet

Succeeds non-deterministically by enumerating values of any Term. Enumerating is defined as follows:
* enumerating a list enumerates each item in the list (in that order).
* enumerating an interval of type =integer= sets the interval to each value in the domain starting from the lower bound.
* enumeration of any other term succeeds with no other effect.
Examples:
==
?- X::integer(1,2), enumerate(X).
X = 1 ;
X = 2.

?- Is=[X,Y], Is::integer(1,2), enumerate(Is).
Is = [1, 1],
X = Y, Y = 1 ;
Is = [1, 2],
X = 1,
Y = 2 ;
Is = [2, 1],
X = 2,
Y = 1 ;
Is = [2, 2],
X = Y, Y = 2.

?- X::real, enumerate(X).
X::real(-1.0e+16, 1.0e+16).

?- enumerate(sam).
true.

?- B::boolean, enumerate([42,-1.0,B,Z]).
B = 0 ;
B = 1.
==
*/
enumerate(X) :-
	interval_object(X, integer, (L,H), _), !,
	between(L,H,X).             % gen values, constraints run on unification
enumerate(X) :- list(X), !,     % list of ..
	enumerate_list_(X).
enumerate(_X).                  % X not enumerable, skip it

enumerate_list_([]).
enumerate_list_([X|Xs]) :-
	(integer(X) -> true ; enumerate(X)),  % optimization: X already an integer, skip it
	enumerate_list_(Xs).

/**
small(+X:numeric_List) is semidet

Succeeds if the width of the domain of Numeric is less than the value defined by the environment flag =clpBNR_default_precision= which is a positive integer specifying number of digits; otherwise fails. For example, a =clpBNR_default_precision= value of 6 (the default) defines a domain width limit of =1e-7=. Numbers have a domain width of 0, so they are always "=small=".

If Numeric is a list of numerics, all elements of the list must be "=small=". Examples:
==
?- X::real, small(X).
false.

?- X::real(-1e-10,1e-10), small(X).
X::real(-1.0000000000000002e-10, 1.0000000000000002e-10).

?- X::real(-1e-10,1e-10), small([X,42]).
X::real(-1.0000000000000002e-10, 1.0000000000000002e-10).
==
Note that this is really only useful for =real= intervals; =integer= intervals are not small until they become point values. 
 */
/**
small(+Numeric,+Precision) is semidet

Succeeds if the width of the domain of Numeric is less than the value defined by P (digits of precision); otherwise fails. As with =|small/1|=, Numeric can be a single numeric or list of numerics.

@see =|small/1|=
 */
small(V) :-
	current_prolog_flag(clpBNR_default_precision,P),
	small(V,P).

small(V,P) :- 
	Err is 10.0**(-P),
	small_(V,Err).

small_(V,Err) :- 
	getValue(V,(L,H)), !,
	chk_small(L,H,Err).
small_(L,Err) :-
	list(L),
	small_list_(L,Err).

small_list_([],_).
small_list_([X|Xs],Err) :-
	small_(X,Err),
	small_list_(Xs,Err).

chk_small(L,H,Err) :-                     % from CLIP?
	W is H-L,
	( W < Err                             % absolute error test  
	 -> true
	 ;  ErrH is Err*sqrt((L**2+H**2)/2),  % guaranteed to be a float
	    W < ErrH,                         % relative error test                 
	    ErrH \== 1.0Inf                   % overflow check
	).

/** 
global_maximum(+Exp,?Z:numeric) is semidet

Succeeds if Z unifies with the global maximum of (evaluated) expression Exp; otherwise fails. Exp must be an actual expression which can be evaluated as part of the search for the global optima, not an interval equal to the evaluated expression. Any solutions will be constrained to be at the global maximum which may result in narrowing any intervals in  Exp. 

The maximum allowable width for the generated maximum is determined by the current default precision (environment flag  =clpBNR_default_precision=). Example:
==
?- X::real(0,3r4*pi), global_maximum(X*sin(4*X),Z).
X:: 1.994...,
Z:: 1.97918... .
== 
Note that intervals in the expression may not narrow significantly if more than one maximum can found using the the initial domains. In such cases, additional "searching", e.g., using =|solve/1|=, may be necessary.

@see =|global_maximize/2|=
*/
/** 
global_maximum(+Exp,?Z:numeric,+Precision:integer) is semidet

Same as =|global_maximum/2|= with additional argument defining precision (overrides environment flag  =clpBNR_default_precision=). Example:
==
?- X::real(0,3r4*pi), global_maximum(X*sin(4*X),Z,4).
X:: 1.99...,
Z:: 1.979... .
== 

@see =|global_maximum/2|=
*/
/**
global_minimum(+Exp,?Z:numeric) is semidet

Succeeds if Z unifies with the global minimum of (evaluated) expression Exp; otherwise fails. This is analogous to =|global_maximum/2|= for finding minima. See =|global_maximum/2|= for more details. Example:
==
?- X::real(0,1r2*pi), global_minimum(X*sin(4*X),Z).
X:: 1.228...,
Z:: -1.203617... .
== 

@see =|global_maximum/2, global_minimize/2|=
*/
/** 
global_minimum(+Exp,?Z:numeric,+Precision:integer) is semidet

Same as =|global_minimum/2|= with additional argument defining precision (overrides environment flag  =clpBNR_default_precision=). Example:
==
?- X::real(0,1r2*pi),global_minimum(X*sin(4*X),Z,4).
X:: 1.23...,
Z:: -1.203... .
== 

@see =|global_minimum/2|=
*/

%
%  global_minimum(Exp,Z) - Z is an interval containing one or more global minimums of Exp.
%  global_maximum(Exp,Z) - as above but global maximums
%
%  Uses Moore-Skelboe algorithm documented in:
%  Ratschek & Rokne (June, 2007) "New Computer Methods for Global Optimization", 
%
%  The main complication is that evaluation of Exp may yield a false positive after 
%  fixed point iteration so any result must be "validated" either by a subsequent MS
%  iteration of by a final absolve (see continue/5).
%
global_maximum(Exp,Z) :-
	global_minimum(-Exp,NZ),
	add_constraint(Z== -NZ).
global_maximum(Exp,Z,P) :-
	global_minimum(-Exp,NZ,P),
	add_constraint(Z== -NZ).

global_minimum(Exp,Z) :-
	current_prolog_flag(clpBNR_default_precision,P),
	global_minimum(Exp,Z,P).
global_minimum(Exp,Z,_P) :- ground(Exp), !,
	Z is Exp.
global_minimum(Exp,Z,P) :-
	global_optimum_(Exp,Z,P,false).

/** 
global_maximize(+Exp,?Z:numeric) is semidet

Succeeds if Z unifies with the global maximum of (evaluated) expression Exp; otherwise fails. Exp must be an actual expression which can be evaluated as part of the search for the global optima, not an interval equal to the evaluated expression. Any solutions will be constrained to be at the global maximum (Z), and the intervals in Exp will be narrowed to the maximizers found for the global maximum value. If the global maximum satsfies multiple sets of maximizers, they will be lost. Finding a single set of maximizers is often sufficient for many practical problems.

The maximum allowable width for the generated maximum is determined by the current default precision (environment flag  =clpBNR_default_precision=). Example:
==
?- X::real(0,3r4*pi), global_maximize(X*sin(4*X),Z).
X:: 1.994666...,
Z:: 1.97918... .
== 

@see =|global_maximum/2|=
*/
/** 
global_maximize(+Exp,?Z:numeric,+Precision:integer) is semidet

Same as =|global_maximize/2|= with additional argument defining precision (overrides environment flag  =clpBNR_default_precision=). Example:
==
?- X::real(0,3r4*pi), global_maximize(X*sin(4*X),Z,4).
X:: 1.9947...,
Z:: 1.979... .
== 

@see =|global_maximum/3|=
*/
/**
global_minimize(+Exp,?Z:numeric) is semidet

Succeeds if Z unifies with the global minimum of (evaluated) expression Exp; otherwise fails. This is analogous to =|global_maximize/2|= for finding minima and a single set of minimizers. See =|global_maximize/2|= for more details. Example:
==
?- X::real(0,1r2*pi), global_minimize(X*sin(4*X),Z).
X:: 1.228295...,
Z:: -1.203617... .
== 

@see =|global_maximize/2|=
*/
/** 
global_minimize(+Exp,?Z:numeric,+Precision:integer) is semidet

Same as =|global_minimize/2|= with additional argument defining precision (overrides environment flag  =clpBNR_default_precision=). Example:
==
?- X::real(0,1r2*pi),global_minimize(X*sin(4*X),Z,4).
X:: 1.2283...,
Z:: -1.203... .
== 

@see =|global_minimize/2|=
*/
% Copy of global_maximum & global_minimum with BindVars=true
global_maximize(Exp,Z) :-
	global_minimize(-Exp,NZ),
	add_constraint(Z== -NZ).
global_maximize(Exp,Z,P) :-
	global_minimize(-Exp,NZ,P),
	add_constraint(Z== -NZ).

global_minimize(Exp,Z) :-
	current_prolog_flag(clpBNR_default_precision,P),
	global_minimize(Exp,Z,P).
global_minimize(Exp,Z,_P) :- ground(Exp), !,
	Z is Exp.
global_minimize(Exp,Z,P) :-
	global_optimum_(Exp,Z,P,true).

global_optimum_(Exp,Z,P,BindVars) :-
	term_variables(Exp,Xs),                           % vars to search on
	{Z==Exp},                                         % Steps 1. - 4.
	copy_box_([Z|Xs],[(Zl,Zh)|XVs]),                  % construct initial box
	iterate_MS(Z,Xs,P,Zl-(Zh,XVs),_ZTree,BindVars).   % and start iteration

% construct box from interval bounds
copy_box_([],[]).
copy_box_([X|Xs],[R|Rs]) :-
	getValue(X,R),
	copy_box_(Xs,Rs).

iterate_MS(Z,Xs,P,Zl-(Zh,XVs),ZTree,BindVars) :-
	continue_MS(Zl,Zh,P,Xs,XVs,Discard),              % Step 12., check termination condition
	widest_MS(Xs,XVs,Xf,XfMid), !,                    % Step 5., get midpoint of widest variable
	(Discard == true 
	 -> ZTree2 = ZTree                                % false positive, ignore this box
	 ;  partition_box_(low,Xs,XVs,Xf,XfMid,XVsLow),   % else partition into boxes V1 and V2
	    (eval_MS(Z,Xs,XVsLow,V1)                      % Step 6., 7. & 8. for V1	
	     -> tree_insert(ZTree,V1,ZTree1)              % Step 10. for V1
	     ;  ZTree1 = ZTree% %, MinZh1 = 1.0Inf
	    ),
	    partition_box_(hi,Xs,XVs,Xf,XfMid,XVsHi),
	    (eval_MS(Z,Xs,XVsHi,V2)                       % Step 6., 7. & 8. for V2	
	     -> tree_insert(ZTree1,V2,ZTree2)             % Step 10. for V2
	     ;  ZTree2 = ZTree1% %, MinZh2 = 1.0Inf
	    )
	),
	select_min(ZTree2,NxtY,ZTreeY),                   % Step 9. and 11., remove Y from tree
	iterate_MS(Z,Xs,P,NxtY,ZTreeY,BindVars).          % Step 13.
iterate_MS(Z,Xs,_P,Zl-(Zh,XVs),_ZTree,BindVars) :-    % termination criteria (Step 12.) met
	(BindVars == true 
	 -> build_box_MS(Xs,XVs,T/T)                      % optional minimizer narrowing
	 ;  add_constraint(Z == ::(Zl,Zh))                % just minimum value
	).

continue_MS(Zl,Zh,P,Xs,XVs,Discard) :-           % w(Y) termination criteria
	Err is 10.0**(-P),
	(chk_small(Zl,Zh,Err)                        % Z is narrow enough?
	 -> (build_box_MS(Xs,XVs,T/T),               % qualifying solution
	     SErr is 10.0**(-min(6,P+2)), % ?? heuristic
	     simplesolveall_(Xs,SErr)                % if valid solution. do not continue
	     -> fail                                 
	     ;  Discard = true                       % not a valid solution so discard
	    )
	 ;  Discard = false                          % not small so continue
	).

% Find widest interval and a point to split it into two partitions.
% The split point is nominally the midpoint to roughly equalize the size of 
% the partitions. However, splitting at a minimizer can result in more partitions
% containing the minimizer, so a small randomization about the midpoint is used. 
widest_MS([X|Xs],[XV|XVs],Xf,XfMid) :-
	widest1_MS(Xs,XVs,XV,X,Xf,XfMid).
	
widest1_MS([],[],(L,H),Xf,Xf,XfMid) :- !,
	midpoint_(L,H,Mid), XfMid is float(Mid),  %% same as 11.7 + float conversion for efficiency
	-2 is cmpr(L,XfMid) + cmpr(XfMid,H).  % L < XfMid < H
widest1_MS([X|Xs],[(L,H)|XVs],(L0,H0),_X0,Xf,XfMid) :-
	1 is cmpr((H-L),(H0-L0)), !,  % (H-L) > (H0-L0)
	widest1_MS(Xs,XVs,(L,H),X,Xf,XfMid).
widest1_MS([_X|Xs],[_XV|XVs],W0,X0,Xf,XfMid) :-
	widest1_MS(Xs,XVs,W0,X0,Xf,XfMid).

partition_box_(P,[X|_Xs],[XV|XVs],Xf,XfMid,[XVP|XVs]) :- X == Xf, !,  % partition on Xf
	XV = (L,H),
	(P == low -> XVP = (L,XfMid) ; XVP = (XfMid,H)).
partition_box_(P,[_X|Xs],[XV|XVs],Xf,XfMid,[XV|XVsP]) :-
	partition_box_(P,Xs,XVs,Xf,XfMid,XVsP).

% calculate resultant box and return it, original box left unchanged (uses global var) 
eval_MS(Z,Xs,XVs,_FV) :-                         % Step 7., calculate F(V) and save
	nb_setval('$clpBNR:eval_MS',[]),              % [] means failure to evaluate
	build_box_MS(Xs,XVs,T/T),
	copy_box_([Z|Xs],NewBox),                    % copy Z and Xs solution bounds
	nb_setval('$clpBNR:eval_MS',NewBox),          % save solution in format for Z tree
	fail.                                        % backtack to unwind 
eval_MS(_,_,_,Zl-(Zh,NXVs)) :-
	nb_getval('$clpBNR:eval_MS',[(Zl,Zh)|NXVs]).  % retrieve solution (fails if [])

sandbox:safe_global_variable('$clpBNR:eval_MS').

build_box_MS([],[],Agenda) :-
	stable_(Agenda).
build_box_MS([X|Xs],[XNew|XVs],Agenda) :-
	getValue(X,XCurrent),
	updateValue_(XCurrent,XNew,X,1,Agenda,NextAgenda), !, %%% unnecessary cut??
	build_box_MS(Xs,XVs,NextAgenda).

tree_insert(Tree,[],Tree) :-!.
tree_insert(MT,Data,Ntree) :- var(MT), !,
	Ntree = n(_L,_R,Data).
tree_insert(n(L,R,K-Data), NK-NData, Ntree) :- -1 is cmpr(NK,K), !,  % NK<K
	tree_insert(L, NK-NData, NewL),
	Ntree = n(NewL,R,K-Data).
tree_insert(n(L,R,K-Data), NK-NData, Ntree) :-  1 is cmpr(NK,K), !,  % NK>K
	tree_insert(R, NK-NData, NewR),
	Ntree = n(L,NewR,K-Data).
tree_insert(n(L,R,K-(U,Data)), K-(NU,NData), Ntree) :- -1 is cmpr(NU,U), !,  % K=NK, NU < U
	tree_insert(L, K-(NU,NData), NewL),
	Ntree = n(NewL,R,K-(U,Data)).
tree_insert(n(L,R,Data), NData, n(L,NewR,Data)) :-                   % K=NK, NU>=U
	Data = NData
	 -> NewR = R                      % if duplicate node, discard
	 ;  tree_insert(R, NData, NewR).  % else add to right branch
	
select_min(n(L,R,Min),Min,R) :- var(L), !, 
	nonvar(Min).  % fail if tree was empty
select_min(n(L,R,KData),Min,n(NewL,R,KData)) :-
	select_min(L,Min,NewL).

% Midpoint test, Step 11+:
% Discard all pairs (Z,z) from the list that satisfy F(C)<z where c = mid Y.
% Midpoint test invalid if soulution constrained
%midpoint_MS(L,H,M) :-  % L and H finite, non-zero ==> geometric/arithmetic mean
%	M is min(sqrt(abs(L)),abs(L)/2)*sign(L)+min(sqrt(abs(H)),abs(H)/2)*sign(H).

/**
solve(X:numeric_List) is nondet

Succeeds if a solution can be found for all values in X where the resultant domain of any value is narrower than the limit specified by the default precision (number of digits as defined by the environment flag  =clpBNR_default_precision=); otherwise fails. This is done by splitting any intervals in round robin order of their widths until all domains are smaller than the required limit. Splitting can only be done at points not in the solution space (unlike =|splitsolve/1|=); this avoids the splitting a single solution range into multiple solutions (although this can still occur for other reasons). Other solutions can be generated on backtracking. Examples:
==
?- X::real, {17*X**256+35*X**17-99*X==0}, solve(X).
X:: 0.0000000000000000... ;
X:: 1.005027892894011... .

?- [X,Y]::real, {X+Y==1,X-Y==1}, solve([X,Y]).
X:: 1.0000000000000...,
Y::real(-4.96269692007445e-14, 4.96269692007445e-14).
==
The two main use cases for =|solve/1|= are a) to separate multiple solutions in a within domain (or set of domains), and b) to overcome the well known dependancy issue when using interval arithmetic. (In `clpfd` terminology, =|solve/1|= is a labelling predicate.)

@see =|splitsolve/1|=
*/
/**
solve(X:numeric_List,Precision:integer) is nondet

Same as =|solve/1|= with precision defined by Precision.

@see =|solve/1|=
*/
%
%  solve(Int) - joint search on list of intervals
%
solve(X) :-
	current_prolog_flag(clpBNR_default_precision,P),
	solve(X,P).

solve(X,P) :-
	interval(X), !,               % if single interval, put it into a list
	solve([X],P).
solve(X,_P) :-
	number(X), !.                 % already a point value
solve(X,P) :-                     % assume list
	Err is 10.0**(-(P+1)),        % convert digits of precision to normalized error value 
	xpsolveall_(X,Err).

xpsolveall_([],_Err) :- !.
xpsolveall_(Xs,Err) :-
	xpsolve_each_(Xs,Us,Err),     % split once and collect successes
	xpsolveall_(Us,Err).          % continue to split remaining

xpsolve_each_([],[],_Err).
xpsolve_each_([X|Xs],[X|Us],Err) :-
	interval_object(X,Type,V,_),          % get interval type and value
	splitinterval_(Type,X,V,Err,Choices), % split interval
	!,
	xpsolve_choice(Choices),              % create choice(point)
	xpsolve_each_(Xs,Us,Err).             % split others in list
xpsolve_each_([X|Xs],Us,Err) :-           % avoid unfreeze overhead if [] unified in head
	X==[], !,                             % end of nested listed, discard
	xpsolve_each_(Xs,Us,Err).             % split remaining
xpsolve_each_([X|Xs],[U|Us],Err) :-
	list(X), !,                           % nested list
	xpsolve_each_(X,U,Err),               % split nested list
	xpsolve_each_(Xs,Us,Err).             % then others in main list
xpsolve_each_([_X|Xs],Us,Err) :-
	xpsolve_each_(Xs,Us,Err).             % split failed or already a number, drop interval from list, and keep going

xpsolve_choice(split(X,SPt)) :- add_constraint(X =< SPt).  % avoid meta call
xpsolve_choice(split(X,SPt)) :- add_constraint(SPt =< X).
xpsolve_choice(split_integer(X,SPt)) :- add_constraint(X =< SPt).
xpsolve_choice(split_integer(X,SPt)) :- add_constraint(SPt < X).
xpsolve_choice(enumerate(X)) :- enumerate(X).

%
% try to split interval - fails if unsplittable (real too narrow)
%
%splitinterval_(boolean,X,Err,Choices) :-
%	splitinterval_(integer,X,Err,Choices).
splitinterval_(integer,X,(L,H),_,Cons) :- 
	( H-L < 15
	 -> Cons = enumerate(X)                              % small enough to enumerate
	 ;  splitinterval_integer_(L,H,Pt),                  % splittable at Pt
	    Cons = split_integer(X,Pt)                       % success
	).
splitinterval_(real,X,(L,H),Err,split(X,::(SPt,SPt))) :-  % split on point value
	splitinterval_real_(L,H,Pt,Err),          % initial guess
	split_real_(X,L,H,Pt,Err,SPt).
	
%  split a real interval
split_real_(X,_,_,Pt,_,Pt) :-              % Pt not in solution space, split here
	\+ X = Pt -> !.
split_real_(X,L,_H,Pt,Err,NPt) :-          % Pt in current solution space, try lower range
	split_real_lo(X,L,Pt,NPt,Err), !.
split_real_(X,_L,H,Pt,Err,NPt) :-          % Pt in current solution space, try upper range
	split_real_hi(X,Pt,H,NPt,Err).

split_real_lo(X,L,Pt,NPt,Err) :-           % search lower range for a split point 
	splitinterval_real_(L,Pt,SPt,Err),
	(\+ X = SPt -> NPt = SPt ; split_real_lo(X,L,SPt,NPt,Err)).

split_real_hi(X,Pt,H,NPt,Err) :-           % search upper range for a split point 
	splitinterval_real_(Pt,H,SPt,Err),
	(\+ X = SPt -> NPt = SPt ; split_real_hi(X,SPt,H,NPt,Err)).

%
% splitinterval_integer_ and splitinterval_real_
%
splitinterval_integer_(L,H,0) :-
	L < 0, H > 0, !.                  % contains 0 but not bounded by 0 
splitinterval_integer_(-1.0Inf,H,Pt) :-  !,  % infinite lower bound, integers unbounded
	finite_interval(integer, (Pt,_)), % split at finite integer min if in range
	H > Pt.
splitinterval_integer_(L,1.0Inf,Pt) :-  !,  % infinite upper bound, integers unbounded
	finite_interval(integer, (_,Pt)), % split at finite integer max if in range
	L < Pt.
splitinterval_integer_(L,H,Pt) :-     % all positive or negative (including zero)  
	Pt is (L div 2) + (H div 2).      % avoid overflow

splitinterval_real_(L,H,0,E) :-       % if interval contains 0, split on (precisely) 0.
	L < 0, H > 0, !,                  % cut in case error criteria fails
	(H-L) > E.                        % fail if width is less than error criteria, overflow is OK
splitinterval_real_(-1.0Inf,H,Pt,_) :-  % neg. infinity to H=<0
	!,  % if following overflows, split failed
	Pt is float(H*10-1),               % subtract 1 in case H is 0. (-1, -11, -101, -1001, ...)
	Pt > -1.0Inf.                      % Pt must be finite
splitinterval_real_(L,1.0Inf,Pt,_) :-  % L>=0 to pos. infinity
	!,  % if following overflows, split failed
	Pt is float(L*10+1),               % add 1 in case L is 0. (1, 11, 101, 1001, ...)
	Pt < 1.0Inf.                       % Pt as float must be finite
splitinterval_real_(L,H,Pt,E) :-       % finite L,H, positive or negative but not split, Pt\=0.
	\+ chk_small(L,H,E),               % only split if not small 
	splitMean_(L,H,Pt), !,
	L < Pt,Pt < H.                     % split point must be between L and H

% (approx.) geometric mean of L and H (same sign)
splitMean_(L,H,M) :-  L >=0, !,  % positive range
	(L=:=0 -> M is min(H/2, sqrt( H)) ; M is sqrt(L)*sqrt(H)).
splitMean_(L,H,M) :-             % negative range
	(H=:=0 -> M is max(L/2,-sqrt(-L)) ; M is -sqrt(-L)*sqrt(-H)). 

/**
splitsolve(X:numeric_List) is nondet

Succeeds if a solution can be found for all values in X where the resultant domain of any value if narrower than the limit specified by the default precision (number of digits as defined by the environment flag  =clpBNR_default_precision=); otherwise fails. This is done by splitting any intervals in order of their widths until all domains are smaller than the required limit. Other solutions can be generated on backtracking.

Normally =|solve/1|= is a better choice but this predicate can be used when =|solve/1|= cannot find a suitable non-solution value to use to split an interval (or intervals). This predicate is also less computationally expensive, but may result in many solutions being produced for a single wider interval. (This is why =|solve/1|= splits on non-solutions.) 

@see =|solve/1|=
*/
/**
splitsolve(X:numeric_List,Precision:integer) is nondet

Same as =|splitsolve/1|= with precision defined by Precision.

@see =|splitsolve/1|=
*/
%
%  splitsolve(Int) - joint search on list of intervals
%  simple split, e.g., no filtering on solutions, etc.
%
splitsolve(X) :-
	current_prolog_flag(clpBNR_default_precision,P),
	splitsolve(X,P).

splitsolve(X,_P) :-
	number(X), !.                 % already a point value
splitsolve(X,P) :-
	interval(X), !,               % if single interval, put it into a list
	Err is 10.0**(-P),
	simplesolveall_([X],Err).
splitsolve(X,P) :-                % assumed to be a list
	flatten_list(X,[],XF),        % flatten before iteration
	Err is 10.0**(-P),
	simplesolveall_(XF,Err).

% flatten list(s) using difference lists
flatten_list(V,Tail,[V|Tail])   :- var(V), !.
flatten_list([],Tail,Tail)      :- !.
flatten_list([H|T], Tail, List) :- !,
	flatten_list(H, HTail, List),
	flatten_list(T, Tail, HTail).
flatten_list(N,Tail,[N|Tail]).

simplesolveall_(Xs,Err) :-
	select_wide_(Xs,_,X),
	interval_object(X, Type, V, _),
	split_choices_(Type,X,V,Err,Choices),
	!,
	xpsolve_choice(Choices),  % from solve/1, generate alternatives
	simplesolveall_(Xs,Err).
simplesolveall_(_Xs,_Err).  % terminated

select_wide_([X],_,X) :- !.        % select last remaining element
select_wide_([X1,X2|Xs],D1,X) :-   % compare widths and discard one interval
	(var(D1) -> delta(X1,D1) ; true),
	delta(X2,D2),
	(D1 >= D2
	 -> select_wide_([X1|Xs],D1,X)
	 ;  select_wide_([X2|Xs],D2,X)
	).

split_choices_(real,X,(L,H),Err,split(X,::(SPt,SPt))) :- !,
	splitinterval_real_(L,H,SPt,Err).            % from solve/1, but splits anywhere
split_choices_(integer,X,V,_Err,Cons) :-
	splitinterval_(integer,X,V,_,Cons).        % from solve/1

/**
absolve(X:numeric_List) is semidet

Succeeds if a if X is a numeric (or list of numeric); otherwise fails. =|absolve|= is intended solely to trim up the boundaries of what is essentially a single (non-point)  solution to a problem. The strategy used  is to work in from the edges of the interval ("nibbling away") at subdomains which are inconsistent until you cannot go farther, then reduce step size and resume nibbling. In this case, the the environment flag  =clpBNR_default_precision= is used to specify the number of step size reductions to apply; the initial step size is half the interval width.

=|absolve|= can be used to further narrow intervals after =|solve|= to "sharpen" the result; example:
==
?- X::real,{X**4-4*X**3+4*X**2-4*X+3==0},solve(X).
X:: 1.000000... ;
X:: 1.0000000... ;
X:: 3.000000... ;
X:: 3.000000... ;
false.

?- X::real,{X**4-4*X**3+4*X**2-4*X+3==0},solve(X),absolve(X).
X:: 1.00000000... ;
X:: 3.00000000... ;
false.
==
*/
/**
absolve(X:numeric_List,Precision:integer) is nondet

Same as =|absolve/1|= with precision defined by Precision.

@see =|absolve/1|=
*/

%  absolve( X ), for X an interval or list of intervals, is intended 
%  solely to trim up the boundaries of what is essentially a single
%  (non-point)  solution to a problem. Hence absolve- unlike the rest
%  of the solve family -  is deterministic!
%	 The strategy used in absolve( derived from the old V 3 solve) is to 
%  work in from the edges of the interval ("nibbling away") until you
%  cannot go nay farther, then reduce step size and resume nibbling.
%  Control parameters limit the number of successive halvings of the 
%  step size, which is initially half the interval width. 
%  		Note that absolve and solve each abstract a different part of
%  of the strategy used in the solve in BNRP V. 3. In this sense, the
%  combination: " solve(X), absolve(X) "  { in that order } does something
%  like what "solve(X)"did under the old system.

absolve( X ):-
	current_prolog_flag(clpBNR_default_precision,P),
	Limit is P+2,
	absolve(X,Limit),!.

absolve(X, _ ):- number(X), !.
absolve(X, Limit ):- interval_object(X, Type, Val, _), !,  % interval (a var)
	delta_(Type,Val,Delta),
	% if bound is already a solution avoid the work
	(\+(lower_bound(X)) -> absolve_l(X,Type,Delta,1,Limit) ; true),
	(\+(upper_bound(X)) -> absolve_r(X,Type,Delta,1,Limit) ; true).

absolve([],_).        % extends to lists
absolve([X|Xs],Lim):- absolve(X,Lim),!, absolve(Xs,Lim).

delta_(integer,(L,U),D) :- D is U div 2 - L div 2.
delta_(real,   (L,U),D) :- D is U/2 - L/2.

absolve_l(X, Type, DL, NL, Limit):- NL<Limit, % work on left side
	getValue(X,(LB1,UB1)), 
	trim_point_(NL,NL1,Type,Limit,DL,DL1),    % generates trim points
	Split is LB1 + DL1,
	LB1 < Split, Split < UB1,                 % in range, not endpoint
	\+(add_constraint(X=< ::(Split,Split))),!,
	add_constraint(X>= ::(Split,Split)),      % so X must be >
	absolve_l(X,Type, DL1, NL1, Limit).
absolve_l(_,_,_,_,_).                         % final result
         
absolve_r(X, Type, DU, NU, Limit):- NU<Limit, % work on right side
	getValue(X,(LB1,UB1)), 
	trim_point_(NU,NU1,Type,Limit,DU,DU1),    % generates trim points
	Split is UB1 - DU1,
	LB1 < Split, Split < UB1,                 % in range, not endpoint
	\+(add_constraint(X>= ::(Split,Split))),!,
	add_constraint(X=< ::(Split,Split)),      % so X must be <
	absolve_r(X,Type, DU1, NU1,Limit).
absolve_r(_,_,_,_,_).                         % final result

trim_point_( N,N, _Type, _Limit, Delta, Delta).
trim_point_( N,M, integer, Limit, Delta, Result):- N<Limit,N1 is N + 1,
       D is  Delta div 2,
       trim_point_(N1,M, integer, Limit,D, Result).
trim_point_( N,M, real, Limit, Delta, Result):- N<Limit,N1 is N + 1,
       D is  Delta/2,
       trim_point_(N1,M,real, Limit,D, Result).

/**
partial_derivative(+Exp, -X, ?Drv) is semidet

Suucceds if the (symbolic) partial derivative of Exp with respect to variable X is Drv; otherwise fails. The syntax of Exp is determined by normal `clpBNR` (and Prolog) arithmetic syntax. Examples:

==
?- partial_derivative(X**2,X,Drv).
Drv = 2*X.

?- partial_derivative(X/Y,X,Drv).
Drv = 1/Y.

?- partial_derivative(X/Y,Y,Drv).
Drv = -1*X/Y**2.

?- partial_derivative(max(X,Y),Y,Drv).
false.
==
This predicate can be used in generating additional constraints, e.g., local optima with a gradient of 0, or in constructing meta-contractors like the Taylor series contractor described in the [User Guide](https://ridgeworks.github.io/clpBNR/CLP_BNR_Guide/CLP_BNR_Guide.html).
*/
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

pd(F,X,DD) :-
	( var(F)
	 -> ( F==X -> DD=1 ; DD=0)
	 ;  ( atomic(F)
	     -> DD=0
	     ; pd_f(F,X,DD)
	    )
	).

:- style_check(-singleton).        % for pd_f

pd_f(-U,X,DX) :-                   % DX = -DU
	pd(U,X,DU),
	pd_minus(DU,DX).

pd_f(U+V,X,DX) :-                  % DX = DU+DV
	pd(U,X,DU), pd(V,X,DV),
	pd_add(DU,DV,DX).

pd_f(U-V,X,DX) :-                  % DX = DU-DV
	pd(U,X,DU), pd(V,X,DV),
	pd_sub(DU,DV,DX).

pd_f(U*V,X,DX) :-                  % DX = V*DU+U*DV
	pd(U,X,DU), pd(V,X,DV), 
	pd_mul(V,DU,VDU),
	pd_mul(U,DV,UDV),
	pd_add(VDU,UDV,DX).

pd_f(U/V,X,DX) :-                  % DX = (V*DU-U*DV)/(V**2)
	pd(U,X,DU), pd(V,X,DV),
	pd_mul(V,DU,VDU),
	pd_mul(U,DV,UDV),
	pd_sub(VDU,UDV,DXN),
	pd_pow(V,2,DXD),
	pd_div(DXN,DXD,DX).

pd_f(U**N,X,DX) :-                 % DX = (N*U**(N-1))*DU for real(N)
	number(N), !,
	pd(U,X,DU),
	pd_sub(N,1,N1),  %N1 is N-1,
	pd_pow(U,N1,UN1),
	pd_mul(N,UN1,DX1),
	pd_mul(DX1,DU,DX).

pd_f(A**U,X,exp(V)*DV) :-          % DX = exp(V)*DV, V = U*log(A)
	V = U*log(A),
	pd_f(V,X,DV).
	
pd_f(log(U),X,DX) :-               % DX = DU/U
	pd(U,X,DU),
	pd_div(DU,U,DX).

pd_f(exp(U),X,DX) :-               % DX = exp(U)*DU
	pd(U,X,DU),
	pd_exp(U,ExpU),
	pd_mul(ExpU,DU,DX).

pd_f(sqrt(U),X,DX) :-              % DX = DU/(2*sqrt(U))
	pd(U,X,DU),
	pd_sqrt(U,SqrtU),
	pd_mul(2,SqrtU,DXD),
	pd_div(DU,DXD,DX).

pd_f(sin(U),X,DX) :-               % DX = cos(U)*DU
	pd(U,X,DU),
	pd_cos(U,CosU),
	pd_mul(CosU,DU,DX).

pd_f(cos(U),X,DX) :-               % DX = -sin(U)*DU
	pd(U,X,DU),
	pd_sin(U,SinU),
	pd_mul(SinU,DU,DSU),
	pd_minus(DSU,DX).

pd_f(tan(U),X,DX) :-               % DX = DU/cos(U)**2
	pd(U,X,DU),
	pd_cos(U,CosU),
	pd_pow(CosU,2,DXD),
	pd_div(DU,DXD,DX).

pd_f(asin(U),X,DX) :-              % DX = DU/sqrt(1-U**2)
	pd(U,X,DU),
	pd_pow(U,2,USQ),
	pd_sub(1,USQ,USQ1),
	pd_sqrt(USQ1,DXD),
	pd_div(DU,DXD,DX).

pd_f(acos(U),X,DX) :-              % DX = -DU/sqrt(1-U**2) = -D(asin(U))
	pd(asin(U),X,DasinX),
	pd_minus(DasinX,DX).

pd_f(atan(U),X,DX) :-              % DX = DU/(1+U**2)
	pd(U,X,DU),
	pd_pow(U,2,USQ),
	pd_add(1,USQ,USQ1),
	pd_div(DU,USQ1,DX).


% optimizations
% also facilitates compiled arithmetic, avoids using catch/3 for instantiation errors
goal_expansion(pd_match(DU,Exp),     % SWIP inline optimization for pd_match/2
	           (nonvar(DU), DU = Exp)
	          ).
pd_match(DU,Exp)  :- nonvar(DU), DU = Exp.

goal_expansion(pd_identity(DU,DX),   % SWIP inline optimization for pd_identity
	           (ground(DU) -> DX is DU  ; DX = DU)
	          ).
pd_identity(DU,DX) :- ground(DU) -> DX is DU  ; DX = DU.  % conditional evaluation

pd_minus(DU,DX)   :- 
	(pd_match(DU,-DV)       %% double negative
	 -> pd_identity(DV,DX)
	 ;  (ground(DU) -> DX is -DU  ; DX = -DU)
	).

pd_add(DU,DV,DV)  :- DU==0, !.
pd_add(DU,DV,DU)  :- DV==0, !.
pd_add(DU,DV,DX)  :- ground((DU,DV)) -> DX is DU+DV ; DX = DU+DV.

pd_sub(DU,DV,DX)  :- DU==0, !, pd_minus(DV,DX).
pd_sub(DU,DV,DU)  :- DV==0, !.
pd_sub(DU,DV,DX)  :- ground((DU,DV)) -> DX is DU-DV ; DX = DU-DV.

pd_mul(DU,DV,0)   :- DU==0, !.
pd_mul(DU,DV,0)   :- DV==0, !.
pd_mul(DU,DV,DV)  :- DU==1, !.
pd_mul(DU,DV,DU)  :- DV==1, !.
pd_mul(DU,DV,DX)  :- DU== -1, !, pd_minus(DV,DX).
pd_mul(DU,DV,DX)  :- DV== -1, !, pd_minus(DU,DX).
pd_mul(DU,DV,DX)  :- ground((DU,DV)) -> DX is DU*DV ; DX = DU*DV.

pd_div(DU,DV,0)   :- DU==0, !.
pd_div(DU,DV,0)   :- DV==0, !, fail.
pd_div(DU,DV,DU)  :- DV==1, !.
pd_div(DU,DV,DU)  :- DV== -1, !, pd_minus(DU,DX).
pd_div(DU,DV,DX)  :- pd_match(DU,sin(X)), DV==  cos(X), !, 
	                 (ground(X) -> DX is  tan(X) ; DX =  tan(X)).
pd_div(DU,DV,DX)  :- pd_match(DU,sin(X)), DV== -cos(X), !, 
	                 (ground(X) -> DX is -tan(X) ; DX = -tan(X)).
pd_div(DU,DV,DX)  :- pd_match(DU,-sin(X)), pd_div(sin(X),DV,DU), !, pd_minus(DU,DX).
pd_div(DU,DV,DX)  :- ground((DU,DV)) -> DX is DU/DV ; DX = DU/DV.

pd_pow(DU,DV,0)   :- DU==0, !.
pd_pow(DU,DV,1)   :- DV==0, !.
pd_pow(DU,DV,1)   :- DU==1, !.
pd_pow(DU,DV,DU)  :- DV==1, !.
pd_pow(DU,DV,DX)  :- ground((DU,DV)) -> DX is DU**DV ; DX = DU**DV.

pd_exp(DU,DX) :- 
	(pd_match(DU,log(X))
	 -> pd_identity(X,DX)
	 ;  (ground(DU) -> DX is exp(DU)  ; DX = exp(DU))
	).

pd_sqrt(DU,DX)    :- ground(DU) -> DX is sqrt(DU) ; DX = sqrt(DU).

pd_sin(DU,DX)     :- ground(DU) -> DX is sin(DU)  ; DX = sin(DU).

pd_cos(DU,DX)     :- ground(DU) -> DX is cos(DU)  ; DX = cos(DU).

:- style_check(+singleton).  % exit pd_f
