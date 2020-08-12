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
% compatability predicates
%

% list filter
list(X) :- is_list(X).

%
%  print_interval(Term), print_interval(Stream,Term)
%	prints Term to optional Stream with intervals expanded to domains
%	uses format/3 so extended Stream options, e.g., atom(A), are supported
%
print_interval(Term) :- print_interval(current_output,Term).

print_interval(Stream,Term) :-
	mapTerm_(Term,Out), !,
	format(Stream,'~w',[Out]).

mapTerm_(Int,Out) :- 
	domain(Int,Out), !.
mapTerm_(Comp,Out) :-  % compounds, including lists, which contain intervals
	compound(Comp), acyclic_term(Comp), !,
	Comp=..[F|Ins],
	mapEach_(Ins,Outs),
	Out=..[F|Outs].
mapTerm_(In,In).

mapEach_([],[]).
mapEach_([In|Ins],[Out|Outs]) :-
	mapTerm_(In,Out), !,
	mapEach_(Ins,Outs).

%
% SWIP attribute portray hook - used if write_attributes=portray
%
:-	set_prolog_flag(write_attributes, portray).  % generally useful

attr_portray_hook(interval(Type,Val,N,F),_Int) :-
	interval_domain_(Type,Val,Dom),
	write(Dom).

%
% SWIP hook for top level output (ignores flags)
% two modes : 
%	Verbose=true, output all interval domains and associated constraints
%	Verbose=false, only output query vars with no constraints
%
project_attributes(QueryVars, _) :- % mark QueryVars for output when Verbose=false
	flag_query_vars_(QueryVars).

flag_query_vars_([]).
flag_query_vars_([QV|QueryVars]) :-
	get_interval_flags_(QV,Flags),
	set_interval_flags_(QV,[queryVar|Flags]), !,   % add 'queryVar' to Flags
	flag_query_vars_(QueryVars).
flag_query_vars_([QV|QueryVars]) :-
	flag_query_vars_(QueryVars).

attribute_goals(X) -->
	{current_prolog_flag(clpBNR_verbose,Verbose),
	 domain_goals_(Verbose,X,Goals)
	},
	Goals.
	
domain_goals_(true,X,Cs) :-         % Verbose=true, QueryVars and constraints output
	interval_object(X, Type, Val, Nodes), !,
	interval_domain_(Type, Val, Dom), 
	constraints_(Nodes,X,NCs),  % reverse map to list of original constraint
	to_comma_exp_(NCs,X::Dom,Cs).
domain_goals_(false,X,[X::Dom]) :-  % Verbose=false, only QueryVars output
	get_interval_flags_(X,Flags),
	memberchk(queryVar,Flags), !,   % set by project_attributes
	interval_object(X, Type, Val, _),
	intValue_(Val,Type,Dom).
domain_goals_(_,X,[]).         % catchall but normally non-query attvar, Verbose=false

constraints_([Node],_,[]) :- var(Node), !.  % end of indefinite list
constraints_([node(COp,_,_,Args)|Nodes],X,[C|Cs]) :-
	term_variables(Args,[V|_]),   % this ensures constraints only get output once
	V==X,
	fmap_(Op,COp,_,_,_), !,
	remap_(Op,Args,C),
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
% 3. Sufficiently narrow reals output in elipsis format.
% 4. Any real intervals with bounds zero or subnormal output as 0.0...
% 5. Query interval variables output as V = V::Domain
% 6. Subterm intervals as sub-terms printed as domain (Type(L,H)).
%
:-	(  % to avoid quoting ellipsis postfix format, also increase answer depth a bit
	 current_prolog_flag(answer_write_options,Opts),
	 lists:subtract(Opts,[quoted(_)],NOpts0),
	 lists:subtract(NOpts0,[max_depth(D)],NOpts),
	 (var(D) -> ND=20 ; ND is max(D,20)),
	 set_prolog_flag(answer_write_options, [quoted(false),max_depth(ND)|NOpts])
	).

intValue_((0,1),integer,boolean).                  % boolean
intValue_((L,H),real,Out...) :-                    % virtual zero (zero or subnormal) 
	zero_float_(L),
	zero_float_(H), !,
	format(chars(Zero),"~16f",0.0),
	string_chars(Out,[' '|Zero]).                  % space prefix 
intValue_((L,H),real,Out...) :-                    % two floats with minimal leading match
	float_chars_(L,LC),
	float_chars_(H,HC),
	sign_chars_(LC,HC,ULC,UHC,Codes/Match),
	leading_zero(ULC,UHC,ZLC),
	matching_(ZLC,UHC,Match,0,Dec,MLen),
	MLen>Dec+1, !,	% minimum of one matching digit after decimal point
	string_codes(Out,Codes).
intValue_((L,H),Type,Dom) :-                        % default, just convert rationals
	rational_fraction_(L,FL),
	rational_fraction_(H,FH),
	interval_domain_(Type, (FL,FH), Dom).

zero_float_(B) :- float(B), float_class(B,C), (C=zero ; C=subnormal).

float_chars_(B,Cs) :-
	rational_fraction_(B,F),
	float(F), float_class(F, normal),
	format(chars(Cs),'~16f',F),  % same length after '.' (pads with trailing 0's)
	length(Cs,Len), Len=<32.     % reverts to precise format if too long

rational_fraction_(B,FB) :-
	rational(B,_,D), D \= 1, !,  % non-integer rational
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
matching_(LCs,HCs,[],N,Dec,N) :-                    % non-matching after '.'
	nonvar(Dec). 

digit_match_(LC,LC1,HC,HC1) :-  % rounding test if first digits different
	digit_(LC,L), digit_(LC1,L1), digit_(HC,H), digit_(HC1,H1),
	H is (L+1) mod 10,
	L1 >= 5, H1 < 5.

% char test for properly formatted number 
digit_(DC,D) :- atom_number(DC,D), integer(D), 0=<D,D=<9.

%
%  developer trace debug code only -  used by stable_/1
%
traceIntOp_(Op, Ints, Ins, Outs) :-
	debugging(clpBNR,true),  % only while debugging clpBNR
	format('node:  ~w(',[Op]),
	traceInts(Ints),
	traceChanges(Ints, Ins, Outs),
	nl, !.
traceIntOp_(_,_,_,_).

traceInts([Int]) :- format('~w)',[Int]).
traceInts([Int|Ints]) :- format('~w,',[Int]), traceInts(Ints).

traceChanges([_Int], [In], [In]).  % no change
traceChanges([Int], [_],  [Out]) :-
	format('\n    ~p <- (~p)',[Int,Out]).
traceChanges([Int|Ints], [In|Ins], [Out|Outs]) :-
	traceChanges([Int], [In], [Out]),
	traceChanges(Ints, Ins, Outs).

%
% for monitoring changes - all actions defined here
%
monitor_action_(trace, Update, Int) :-  !, % log changes to console and enter debugger
	monitor_action_(log, Update, Int),
	trace.

monitor_action_(log, Update, Int) :-  !,  % log type change to console
	monitor_desc_(Update, Desc),
	debug_clpBNR_('~w~w to (~p)',[Desc,Int,Update]).

monitor_action_(_, _, _).  % default to noop (as in 'none')
	
monitor_desc_(Var, 'Unify ') :- var(Var), !.  % unification of two intervals (rare case)
monitor_desc_(integer, 'Set type of ') :- !.  % note: can't set integer to real
monitor_desc_(_, 'Set value of ').  % assumed to be a list or number.

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
	number(X), !,     % already bound to a point value
	enumerate_(Xs).
enumerate_([X|Xs]) :-
	interval(X),
	getValue(X,(L,H)),
	between(L,H,X),   % gen values, constraints run on unification
	enumerate_(Xs).

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
	{Z== -NZ}.
global_maximum(Exp,Z,P) :-
	global_minimum(-Exp,NZ,P),
	{Z== -NZ}.

global_minimum(Exp,Z) :-
	current_prolog_flag(clpBNR_default_precision,P),
	global_minimum(Exp,Z,P).
global_minimum(Exp,Z,P) :- ground(Exp), !,
	Z is Exp.
global_minimum(Exp,Z,P) :-
	term_variables(Exp,Xs),                      % vars to search on
	{Z==Exp},                                    % Steps 1. - 4.
	ranges_([Z|Xs],[(Zl,Zh)|XVs]),               % construct initial box
	iterate_MS(Z,Xs,P,Zl-(Zh,XVs),ZTree).     % and start iteration
	
iterate_MS(Z,Xs,P,Zl-(Zh,XVs),ZTree) :-
	continue_MS(Zl,Zh,P,Xs,XVs,False), !,        % Step 12., check termination condition
	widest_MS(Xs,XVs,Xf,XfMid),                  % Step 5., get midpoint of widest variable
	eval_MS(False,Z,Xs,XVs,Xf=<pt(XfMid),V1),    % Step 6., 7. & 8. for V1
	tree_insert(ZTree,V1,ZTree1),                % Step 10. for V1
	eval_MS(False,Z,Xs,XVs,Xf>=pt(XfMid),V2),    % Step 6., 7. & 8. for V2
	tree_insert(ZTree1,V2,ZTree2),               % Step 10. for V2
	select_min(ZTree2,NxtY,ZTreeY),              % Step 9. and 11., remove Y from tree
	iterate_MS(Z,Xs,P,NxtY,ZTreeY).              % Step 13.
iterate_MS(Z,Xs,P,Zl-(Zh,XVs),ZTree) :-          % termination criteria (Step 12.) met
	{Zl=<Z, Z=<Zh}.  % no minimizer narrowing, may be many optima

continue_MS(Zl,Zh,P,_,_,_) :-                      % w(Y) termination criteria
	(Zh-Zl)/max(1,min(abs(Zl),abs(Zh))) > 10**(-P),  % fail if narrow enough
	!.
continue_MS(_,_,P,Xs,XVs,_) :-                   % test for false positive
	build_box_MS(Xs,XVs,T/T),
	SP is min(6,P+2), % ?? heuristic
	simplesolveall_(Xs,SP),	                     % validate solution
	!, fail.  % no narrowing escapes
continue_MS(Zl,Zh,_,_,XVs,false).                % continue with false positive

% calculate resultant box and return it, original box left unchanged (uses global var) 
eval_MS(False,_,_,_,_,[]) :- False == false, !.  % if false positive return "fail" result
eval_MS(_,Z,Xs,XVs,XConstraint,FV) :-            % Step 7., calculate F(V) and save
	nb_setval(eval_MS_,[]),                      % [] means failure to evaluate
	buildConstraint_(XConstraint,T/T,Agenda),
	build_box_MS(Xs,XVs,Agenda),
	ranges_([Z|Xs],[(Zl,Zh)|NXVs]),              % copy Z and Xs solution bounds
	nb_setval(eval_MS_,Zl-(Zh,NXVs)),            % save solution in format for Z tree
	fail.                                        % backtack to unwind 
eval_MS(_,Z,Xs,XVs,XConstraint,FV) :-
	nb_getval(eval_MS_,FV).                      % retrieve solution ([] on failure)

build_box_MS([],[],Agenda) :-
	stable_(Agenda).
build_box_MS([X|Xs],[XNew|XVs],Agenda) :-
	getValue(X,XCurrent),
	updateValue_(XCurrent,XNew,X,1,Agenda,NextAgenda), !, %%% unnecessary cut??
	build_box_MS(Xs,XVs,NextAgenda).

tree_insert(Tree,[],Tree) :-!.
tree_insert(MT,Data,n(L,R,Data)) :- var(MT), !.
tree_insert(n(L,R,K-Data), NK-NData, n(NewL,R,K-Data)) :- NK<K,!,
	tree_insert(L, NK-NData, NewL).
tree_insert(n(L,R,K-Data), NK-NData, n(L,NewR,K-Data)) :- NK>K,!,
	tree_insert(R, NK-NData, NewR).
tree_insert(n(L,R,K-(U,Data)), K-(NU,NData), n(NewL,R,K-(U,Data))) :- NU<U, !, % K=NK
	tree_insert(L, K-(NU,NData), NewL).
tree_insert(n(L,R,Data), NData, n(L,NewR,Data)) :-  % K=NK, NU>=U
	tree_insert(R, NData, NewR).
	
select_min(n(L,R,Min),Min,R) :- var(L), !, 
	nonvar(Min).  % fail if tree was empty
select_min(n(L,R,KData),Min,n(NewL,R,KData)) :-
	select_min(L,Min,NewL).

%
% some possible general purpose routines
%
% construct list of interval bounds
ranges_([],[]).
ranges_([X|Xs],[R|Rs]) :-
	getValue(X,R),
	ranges_(Xs,Rs).

% find widest interval and its midpoint
widest_MS([X|Xs],[XV|XVs],Xf,XfMid) :-
	widest1_MS(Xs,XVs,XV,X,Xf,XfMid).
	
widest1_MS([],[],(L,H),Xf,Xf,XfMid) :-
	midpoint_(L,H,XfMid), !.
widest1_MS([X|Xs],[(L,H)|XVs],(L0,H0),X0,Xf,XfMid) :-
	(H-L) > (H0-L0), !,
	widest1_MS(Xs,XVs,(L,H),X,Xf,XfMid).
widest1_MS([X|Xs],[XV|XVs],W0,X0,Xf,XfMid) :-
	widest1_MS(Xs,XVs,W0,X0,Xf,XfMid).

% Midpoint test, Step 11+:
% Discard all pairs (Z,z) from the list that satisfy F(C)<z where c = mid Y.
%midpoint_MS(L,H,M) :-  % L and H finite, non-zero ==> geometric/arithmetic mean
%	M is min(sqrt(abs(L)),abs(L)/2)*sign(L)+min(sqrt(abs(H)),abs(H)/2)*sign(H).

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
splitsolve(X,P) :-                % assume list
	flatten_list(X,[],XF),        % flatten before iteration
	simplesolveall_(XF,P).

% flatten list(s) using difference lists
flatten_list(V,Tail,[V|Tail])   :- var(V), !.
flatten_list([],Tail,Tail)      :- !.
flatten_list([H|T], Tail, List) :- !,
	flatten_list(H, HTail, List),
	flatten_list(T, Tail, HTail).
flatten_list(N,Tail,[N|Tail]).

simplesolveall_(Xs,P) :-
	ranges_(Xs,XBs),
	widest_MS(Xs,XBs,X,Xmid),  % fails if Xs=[]
	interval_object(X,Type,XVal,_),   %getValue(X,[Xl,Xh]),
	choice_generator_(Type,X,XVal,Xmid,P,Choices),
	!,
	Choices,  % generate alternatives
	simplesolveall_(Xs,P).
simplesolveall_(Xs,P).  % terminated
	
%	bisect_interval(real,X,[Xl,Xh],Xmid,P,({X=<pt(Xmid)};{pt(Xmid)=<X})) :-
choice_generator_(real,X,(Xl,Xh),Xmid,P,bisect_interval_(real,X,Xmid)) :-
	(Xh-Xl)/max(1,min(abs(Xl),abs(Xh))) > 10**(-P).
choice_generator_(integer,X,(Xl,Xh),Xmid,_,enumerate(X)):-            % enumerate narrow integers
	Xh-Xl =< 16, !.
choice_generator_(integer,X,_,Xmid,_,bisect_interval_(integer,X,Xmid)).  % bisect the rest

bisect_interval_(_,X,Pt) :-
	buildConstraint_(X=<pt(Pt),T/T,Agenda),
	stable_(Agenda).
bisect_interval_(real,X,Pt) :-
	buildConstraint_(pt(Pt)=<X,T/T,Agenda),   % must use =<
	stable_(Agenda).
bisect_interval_(integer,X,Pt) :-
	buildConstraint_(pt(Pt)<X,T/T,Agenda),    % can use <
	stable_(Agenda).

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
%  step size, which is initially half the interval width. 
%  		Note that absolve and solve each abstract a different part of
%  of the strategy used in the solve in BNRP V. 3. In this sense, the
%  combination: " solve(X), absolve(X) "  { in that order } does something
%  like what "solve(X)"did under the old system.


absolve( X ):-
	current_prolog_flag(clpBNR_default_precision,P),
	absolve(X,P),!.

absolve(X, _ ):- number(X), !.
absolve(X, Limit ):- interval_object(X, Type, Val, _), !,  % interval
	delta_(Type,Val,Delta),
	% if bound is already a solution avoid the work
	(not(not(lower_bound(X))) -> true ; absolve_l(X,Type,Delta,1,Limit)),
	(not(not(upper_bound(X))) -> true ; absolve_r(X,Type,Delta,1,Limit)).

absolve([],_).		% extends to lists
absolve([X|Xs],Lim):- absolve(X,Lim),!, absolve(Xs,Lim).

delta_(integer,(L,U),D) :- D is U div 2 - L div 2.
delta_(real,   (L,U),D) :- D is U/2 - L/2.

absolve_l(X, Type, DL, NL, Limit):- NL<Limit, % work on left side
	getValue(X,(LB1,UB1)), 
	trim_point_(NL,NL1,Type,Limit,DL,DL1),    % generates trim points
	Split is LB1 + DL1,
	LB1 < Split, Split < UB1,                 % in range, not endpoint
	not({X=<pt(Split)}),!,
	{X>=pt(Split)},                           % so X must be >
	absolve_l(X,Type, DL1, NL1, Limit).
absolve_l(_,_,_,_,_).                         % final result
         
absolve_r(X, Type, DU, NU, Limit):- NU<Limit, % work on right side
	getValue(X,(LB1,UB1)), 
	trim_point_(NU,NU1,Type,Limit,DU,DU1),    % generates trim points
	Split is UB1 - DU1,
	LB1 < Split, Split < UB1,                 % in range, not endpoint
	not({X>=pt(Split)}),!,
	{X=<pt(Split)},                           % so X must be <
	absolve_r(X,Type, DU1, NU1,Limit).
absolve_r(_,_,_,_,_).                         % final result

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
	number(X), !.                 % already a point value
solve(X,P) :-                     % assume list
	Err is 10.0**(-(P+1)),          % convert digits of precision to normalized error value 
	xpsolveall_(X,Err).

xpsolveall_([],Err) :- !.
xpsolveall_(Xs,Err) :-
	xpsolve_each_(Xs,Us,Err),     % split once and collect successes
	xpsolveall_(Us,Err).          % continue to split remaining

xpsolve_each_([],[],Err).
xpsolve_each_([X|Xs],[X|Us],Err) :-
	interval_object(X,Type,V,_),          % get interval type and value
	splitinterval_(Type,X,V,Err,Choices),   % split interval
	!,
	Choices,                              % create choice(point)
	xpsolve_each_(Xs,Us,Err).             % split others in list
xpsolve_each_([X|Xs],Us,Err) :-           % avoid freeze overhead if [] unified in head
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

splitinterval_(real,X,V,Err,({X =< SPt};{SPt =< X})) :-
	%	getValue(X,V),
	splitinterval_real_(V,Pt,Err), !,           % initial guess
	split_real_(X,V,Pt,Err,SPt).

splitinterval_(integer,X,V,_,({X =< Pt};{Pt < X})) :-   % try to split and on failure use enumerate/1 .
	%	getValue(X,V),
	splitinterval_integer_(V,Pt), !.
splitinterval_(integer,X,_,_,enumerate_([X])).           % failed to split, so enumerate

%splitinterval_(boolean,X,Err,Choices) :-
%	splitinterval_(integer,X,Err,Choices).


%  split a real interval
split_real_(X,_,Pt,_,pt(Pt)) :-            % Pt not in solution space, split here
	X\=Pt, !.
%	not({X==Pt}), !.
split_real_(X,(L,H),Pt,Err,pt(NPt)) :-     % Pt in current solution space, try lower range
	split_real_lo(X,(L,Pt),NPt,Err), !.
split_real_(X,(L,H),Pt,Err,pt(NPt)) :-     % Pt in current solution space, try upper range
	split_real_hi(X,(Pt,H),NPt,Err).

split_real_lo(X,(L,Pt),NPt,Err) :-         % search lower range for a split point 
	splitinterval_real_((L,Pt),SPt,Err), !,
	(X\=SPt -> NPt=SPt ; split_real_lo(X,(L,SPt),NPt,Err)).

split_real_hi(X,(Pt,H),NPt,Err) :-         % search upper range for a split point 
	splitinterval_real_((Pt,H),SPt,Err), !,
	(X\=SPt -> NPt=SPt ; split_real_hi(X,(SPt,H),NPt,Err)).


%
% splitinterval_integer_ and splitinterval_real_ require ! at point of call.
%
	
splitinterval_integer_((L,H),0) :-
	L < 0, H > 0.                     % contains 0 but not 0 
splitinterval_integer_((-1.0Inf,H),Pt) :-
	Pt is H*10-5.                     % subtract 5 in case H is 0. (-5, -15, -105, -1005, ...)
splitinterval_integer_((L,-1.0Inf),Pt) :-
	Pt is L*10+5.                     % add 5 in case L is 0. (5, 15, 105, 1005, ...)
splitinterval_integer_((L,H),Pt) :- 
	H-L >= 16,                        % don't split ranges smaller than 16
	Pt is (L div 2) + (H div 2).      % avoid overflow


splitinterval_real_((L,H),0,E) :-     % if interval contains 0, split on 0.
	L < 0, H > 0, !,                  % cut in case error criteria fails
	(H-L) > E.                        % fail if width is less than error criteria, overflow is OK

splitinterval_real_((-1.0Inf,H),Pt,_) :-   % neg. infinity to H=<0
	!,  % if following overflows, split failed
	Pt is H*10-1,                         % subtract 1 in case H is 0. (-1, -11, -101, -1001, ...)
	Pt > -1.0Inf.                         % Pt must be finite
splitinterval_real_((L,1.0Inf),Pt,_) :-   % L>=0 to pos. infinity
	!,  % if following overflows, split failed
	Pt is L*10+1,
	Pt < 1.0Inf.                          % Pt must be finite

splitinterval_real_((L,H),Pt,E) :-    % finite L,H, positive or negative but not split, Pt\=0.
	splitMean_(L,H,Pt),
	Pt =\= 0,                         % if calculated split point zero, underflow occurred -> fail
	(H-L) > max(abs(Pt),1)*E.         % fail if width is less than relative error, overflow is OK

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
	%	simplify(DD,DX),
	%	simplify(DX,DFX).  % post re-simplify for insurance??

pd(Y,X,D) :-
	var(Y), (X==Y -> D=1 ; D=0), !.

pd(C,_,0) :-                     % DX = 0
	atomic(C), !.                % atom, number, ..

pd(-U,X,DX) :-                   % DX = -DU
	pd(U,X,DU),
	pd_minus(DU,DX).

pd(U+V,X,DX) :-                  % DX = DU+DV
	pd(U,X,DU), pd(V,X,DV),
	pd_add(DU,DV,DX).

pd(U-V,X,DX) :-                  % DX = DU-DV
	pd(U,X,DU), pd(V,X,DV),
	pd_sub(DU,DV,DX).

pd(U*V,X,DX) :-                  % DX = V*DU+U*DV
	pd(U,X,DU), pd(V,X,DV), 
	pd_mul(V,DU,VDU),
	pd_mul(U,DV,UDV),
	pd_add(VDU,UDV,DX).

pd(U/V,X,DX) :-                  % DX = (V*DU-U*DV)/(V**2)
	pd(U,X,DU), pd(V,X,DV),
	pd_mul(V,DU,VDU),
	pd_mul(U,DV,UDV),
	pd_sub(VDU,UDV,DXN),
	pd_pow(V,2,DXD),
	pd_div(DXN,DXD,DX).

pd(U**N,X,DX) :-                 % DX = (N*U**(N-1))*DU
	pd(U,X,DU),
	pd_sub(N,1,N1),  %N1 is N-1,
	pd_pow(U,N1,UN1),
	pd_mul(N,UN1,DX1),
	pd_mul(DX1,DU,DX).

pd(log(U),X,DX) :-               % DX = DU/U
	pd(U,X,DU),
	pd_div(DU,U,DX).

pd(exp(U),X,DX) :-               % DX = exp(U)*DU
	pd(U,X,DU),
	pd_tryeval(exp(U),ExpU),
	pd_mul(ExpU,DU,DX).

pd(sqrt(U),X,DX) :-              % DX = DU/(2*sqrt(U))
	pd(U,X,DU),
	pd_tryeval(sqrt(U),SqrtU),
	pd_mul(2,SqrtU,DXD),
	pd_div(DU,DXD,DX).

pd(sin(U),X,DX) :-               % DX = cos(U)*DU
	pd(U,X,DU),
	pd_tryeval(cos(U),CosU),
	pd_mul(CosU,DU,DX).

pd(cos(U),X,DX) :-               % DX = -sin(U)*DU
	pd(U,X,DU),
	pd_tryeval(sin(U),SinU),
	pd_mul(SinU,DU,DSU),
	pd_minus(DSU,DX).

pd(tan(U),X,DX) :-               % DX = DU/cos(U)**2
	pd(U,X,DU),
	pd_tryeval(cos(U),CosU),
	pd_pow(CosU,2,DXD),
	pd_div(DU,DXD,DX).

pd(asin(U),X,DX) :-              % DX = DU/sqrt(1-U**2)
	pd(U,X,DU),
	pd_pow(U,2,USQ),
	pd_sub(1,USQ,USQ1),
	pd_tryeval(sqrt(USQ1),DXD),
	pd_div(DU,DXD,DX).

pd(acos(U),X,DX) :-              % DX = -DU/sqrt(1-U**2) = -D(asin(U))
	pd(asin(U),X,DasinX),
	pd_minus(DasinX,DX).

pd(atan(U),X,DX) :-              % DX = DU/(1+U**2)
	pd(U,X,DU),
	pd_pow(U,2,USQ),
	pd_add(1,USQ,USQ1),
	pd_div(DU,USQ1,DX).


pd_minus(DU,DX)  :- pd_tryeval(-DU,DX).

pd_add(DU,DV,DV) :- DU==0, !.
pd_add(DU,DV,DU) :- DV==0, !.
pd_add(DU,DV,DX) :- pd_tryeval(DU+DV,DX).

pd_sub(DU,DV,DX) :- DU==0, !, pd_minus(DV,DX).
pd_sub(DU,DV,DU) :- DV==0, !.
pd_sub(DU,DV,DX) :- pd_tryeval(DU-DV,DX).

pd_mul(DU,DV,0)  :- DU==0, !.
pd_mul(DU,DV,0)  :- DV==0, !.
pd_mul(DU,DV,DV) :- DU==1, !.
pd_mul(DU,DV,DU) :- DV==1, !.
pd_mul(DU,DV,DX) :- DU== -1, !, pd_minus(DV,DX).
pd_mul(DU,DV,DX) :- DV== -1, !, pd_minus(DU,DX).
pd_mul(DU,DV,DX) :- pd_tryeval(DU*DV,DX).

pd_div(DU,DV,0)  :- DU==0, !.
pd_div(DU,DV,0)  :- DV==0, !, fail.
pd_div(DU,DV,DU) :- DV==1, !.
pd_div(DU,DV,DU) :- DV== -1, !, pd_minus(DU,DX).
pd_div(DU,DV,DX) :- pd_tryeval(DU/DV,DX).

pd_pow(DU,DV,0)  :- DU==0, !.
pd_pow(DU,DV,1)  :- DV==0, !.
pd_pow(DU,DV,1)  :- DU==1, !.
pd_pow(DU,DV,DU) :- DV==1, !.
pd_pow(DU,DV,DX) :- pd_tryeval(DU**DV,DX).


pd_tryeval(Exp,DX) :-  % DX is Exp or DX=Exp
	catch(DX is Exp, error(instantiation_error, _), DX=Exp).

%
% safe declarations must be after the predicate definitions
%
% the following use meta-predicates
sandbox:safe_primitive(clpBNR:solve(_)).
sandbox:safe_primitive(clpBNR:solve(_,_)).
sandbox:safe_primitive(clpBNR:splitsolve(_)).
sandbox:safe_primitive(clpBNR:splitsolve(_,_)).
sandbox:safe_primitive(clpBNR:global_minimum(_,_)).
sandbox:safe_primitive(clpBNR:global_minimum(_,_,_)).
sandbox:safe_primitive(clpBNR:global_maximum(_,_)).
sandbox:safe_primitive(clpBNR:global_maximum(_,_,_)).
sandbox:safe_primitive(clpBNR:partial_derivative(_,_,_)).
