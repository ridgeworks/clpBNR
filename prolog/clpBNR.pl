%
% CLP(BNR) == Constraints On Boolean, Integer, and Real Intervals
%
/*	The MIT License (MIT)
 *
 *	Copyright (c) 2019,2020,2021 Rick Workman
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
:- module(clpBNR,          % SWI module declaration
	[
	op(700, xfx, ::),
	op(150, xf,  ...),     % postfix op currently just for output
	(::)/2,                % declare interval
	{}/1,                  % define constraint
	interval/1,            % filter for clpBNR constrained var
	list/1,                % O(1) list filter (also for compatibility)
	domain/2, range/2,     % get type and bounds (domain)
	delta/2,               % width (span) of an interval or numeric (also arithmetic function)
	midpoint/2,            % midpoint of an interval (or numeric) (also arithmetic function)
	median/2,              % median of an interval (or numeric) (also arithmetic function)
	lower_bound/1,         % narrow interval to point equal to lower bound
	upper_bound/1,         % narrow interval to point equal to upper bound

	% additional constraint operators
	op(200, fy, ~),        % boolean 'not'
	op(500, yfx, and),     % boolean 'and'
	op(500, yfx, or),      % boolean 'or'
	op(500, yfx, nand),    % boolean 'nand'
	op(500, yfx, nor),     % boolean 'nor'
	op(500, yfx, xor),     % boolean 'xor'
	op(700, xfx, <>),      % integer not equal
	op(700, xfx, <=),      % set inclusion
	op(700, xfx, =>),      % set inclusion

	% utilities
	print_interval/1, print_interval/2,      % pretty print interval with optional stream
	small/1, small/2,      % defines small interval width based on precision value
	solve/1, solve/2,      % solve (list of) intervals using split to find point solutions
	splitsolve/1, splitsolve/2,   % solve (list of) intervals using split
	absolve/1, absolve/2,  % absolve (list of) intervals, narrows by nibbling bounds
	enumerate/1,           % "enumerate" integers
	global_minimum/2,      % find interval containing global minimums for an expression
	global_minimum/3,      % global_minimum/2 with definable precision
	global_maximum/2,      % find interval containing global minimums for an expression
	global_maximum/3,      % global_maximum/2 with definable precision
	nb_setbounds/2,        % non-backtracking set bounds (use with branch and bound)
	partial_derivative/3,  % differentiate Exp wrt. X and simplify
	clpStatistics/0,       % reset
	clpStatistic/1,        % get selected
	clpStatistics/1,       % get all defined in a list
	watch/2                % enable monitoring of changes for interval or (nested) list of intervals
	]).

/*		missing(?) functionality: utility accumulate/2.		*/

/* supported interval relations:

+	-	*	/                         %% arithmetic
**                                    %% includes real exponent, odd/even integer
abs                                   %% absolute value
sqrt                                  %% positive square root
min	max                               %% binary min/max
==	is	<>	=<	>=	<	>             %% comparison
<=	=>                                %% inclusion
and	or	nand	nor	xor	->            %% boolean
-	~                                 %% unary negate and not
exp	log                               %% exp/ln
sin	asin	cos	acos	tan	atan      %% trig functions

*/

version("0.9.7").

:- style_check([-singleton, -discontiguous]).  % :- discontiguous ... not reliable.

%
% clpBNR specific Prolog environment flags
%
:- create_prolog_flag(clpBNR_iteration_limit,3000,[type(integer),keep(true)]).
:- create_prolog_flag(clpBNR_default_precision,6,[type(integer),keep(true)]).
:- create_prolog_flag(clpBNR_verbose,false,[type(boolean),keep(true)]).

%
% SWIP optimise control - set flag to true for compiled arithmetic
%
:-  (current_prolog_flag(optimise,Opt),
	 nb_setval('clpBNR:temp',Opt),  % save current value to restore on :- initialization/1
	 set_prolog_flag(optimise,false)
	).

restore_optimise :-  % by :- initialization.
	% restore "optimise" flag
	(nb_current('clpBNR:temp',Opt) 
	 -> (nb_delete('clpBNR:temp'), set_prolog_flag(optimise,Opt))
	 ; true
	).

%
% Define debug_clpBNR_/2 before turning on optimizer removing debug calls.
%
debug_clpBNR_(FString,Args) :- debug(clpBNR,FString,Args).

:- set_prolog_flag(optimise,true).

current_node_(Node) :-  % look back to find current Op being excuted for debug messages
	prolog_current_frame(F),  % this is a little grungy, but necessary to get intervals
	prolog_frame_attribute(F,parent_goal,doNode_(Arg,Op,_,_,_,_)),
	Arg =.. [_|Args],
	Node=..[Op|Args].

%
% statistics
%

% assign,increment/read global counter (assumed to be ground value so use _linkval)
g_assign(G,V)  :- nb_linkval(G,V).
g_inc(G)       :- nb_getval(G,N), N1 is N+1, nb_linkval(G,N1).
g_incb(G)      :- nb_getval(G,N), N1 is N+1, b_setval(G,N1).    % undone on backtrack
g_read(G,V)    :- nb_getval(G,V).

:- discontiguous 
	clpBNR:clpStatistics/0, clpBNR:clpStatistic/1, 
	sandbox:safe_global_variable/1.

sandbox:safe_global_variable('clpBNR:userTime').
sandbox:safe_global_variable('clpBNR:inferences').
sandbox:safe_global_variable('clpBNR:gc_time').

% 
% Global var statistics are per thread and therefore must be "lazily" initialized
% This exception handler will be invoked the first time one of the vars is read
% 
user:exception(undefined_global_variable,GlobalVar,retry) :-
	atom_concat('clpBNR:',_,GlobalVar),
	% uninitialized clpBNR global, probably in another thread, reinitialize all 
	clpStatistics.               

clpStatistics :-
	% garbage_collect,  % ? do gc before time snapshots
	statistics(cputime,T), g_assign('clpBNR:userTime',T),   % thread based
	statistics(inferences,I), g_assign('clpBNR:inferences',I),
	statistics(garbage_collection,[_,_,G,_]), g_assign('clpBNR:gc_time',G),
	fail.  % backtrack to reset other statistics.

clpStatistic(userTime(T)) :- statistics(cputime,T1), g_read('clpBNR:userTime',T0), T is T1-T0.

clpStatistic(gcTime(G)) :- statistics(garbage_collection,[_,_,G1,_]), g_read('clpBNR:gc_time',G0), G is (G1-G0)/1000.0.

clpStatistic(globalStack(U/T)) :- statistics(globalused,U), statistics(global,T).

clpStatistic(trailStack(U/T)) :- statistics(trailused,U), statistics(trail,T).

clpStatistic(localStack(U/T)) :- statistics(localused,U), statistics(local,T).

clpStatistic(inferences(I)) :- statistics(inferences,I1), g_read('clpBNR:inferences',I0), I is I1-I0.

%
% list filter for compatibility
%	Note: not equivalent to is_list/1 but executes in O(1) time.
%
list(X) :- compound(X) ->  X=[_|_] ; X==[].

%
% Set required arithmetic flags
%
set_prolog_flags :-	
	set_prolog_flag(prefer_rationals, true),           % enable rational arithmetic
	set_prolog_flag(max_rational_size, 16),            % rational size in bytes before ..
	set_prolog_flag(max_rational_size_action, float),  % conversion to float

	set_prolog_flag(float_overflow,infinity),          % enable IEEE continuation values
	set_prolog_flag(float_zero_div,infinity),
	set_prolog_flag(float_undefined,nan).
	
:- include(clpBNR/ia_primitives).  % interval arithmetic relations via evalNode/4.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%  SWI-Prolog implementation of IA
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% Intervals are constrained (attributed) variables.
%
% Current interval bounds updates via setarg(Val) which is backtrackable
%
%  interval(X)  - filter
%
interval(X) :- get_attr(X, clpBNR, _).

% internal abstraction
interval_object(Int, Type, Val, Nodelist) :-
	get_attr(Int, clpBNR, interval(Type, Val, Nodelist, Flags)).

% flags (list)  abstraction
get_interval_flags_(Int,Flags) :-
	get_attr(Int, clpBNR, interval(Type, Val, Nodelist, Flags)).
	
set_interval_flags_(Int,Flags) :-  % flags assumed to be ground so no copy required
	get_attr(Int, clpBNR, interval(Type, Val, Nodelist, _)),
	put_attr(Int, clpBNR, interval(Type, Val, Nodelist, Flags)).

%
% Interval value constants
%
universal_interval((-1.0Inf,1.0Inf)).

empty_interval((1.0Inf,-1.0Inf)).

% Finite intervals - 64 bit IEEE reals, 
finite_interval(real,    (-1.0e+16,1.0e+16)).
finite_interval(integer, (L,H)) :-  %% SWIP:
	current_prolog_flag(bounded,false),!,  % integers are unbounded, but use tagged limits for finite default
	current_prolog_flag(min_tagged_integer,L),
	current_prolog_flag(max_tagged_integer,H).
finite_interval(boolean, (0,1)).

%
%  non-backtracking set bounds for use with branch and bound
%
nb_setbounds(Int, [L,U]) :- 
	get_attr(Int, clpBNR, Def),
	Def = interval(_, Val, _, _),
	^(Val,(L,U),NewVal),          % new range is intersection (from ia_primitives)
	nb_setarg(2, Def, NewVal).

%
% get current value
%
getValue(Int, Val) :- 
	number(Int)
	 -> Val=(Int,Int)                                   % numeric point value
	 ;  get_attr(Int, clpBNR, interval(_, Val, _, _)).  % interval, optimized for SWIP

%
% set monitor action on an interval
%
watch(Int,Action) :-
	atom(Action), 
	get_interval_flags_(Int,Flags), !,
	remove_(Flags,watch(_),Flags1),
	(Action = none -> Flags2=Flags1 ; Flags2=[watch(Action)|Flags1]),
	set_interval_flags_(Int,Flags2).
watch(Ints,Action) :-
	list(Ints),
	watch_list_(Ints,Action).

remove_([],_,[]).
remove_([X|Xs],X,Xs) :- !.
remove_([X|Xs],X,[X|Ys]) :-
	remove_(Xs,X,Ys).

watch_list_([],Action).
watch_list_([Int|Ints],Action) :-
	watch(Int,Action),
	watch_list_(Ints,Action).

% check if watch enabled on this interval
check_monitor_(Int, Update, interval(Type,Val,Nodelist,Flags)) :-
	(memberchk(watch(Action), Flags)
	 -> once(monitor_action_(Action, Update, Int))  % in ia_utilities
	 ; true
	).

%
% set interval value (assumes bounds check has already been done)
%
putValue_(New, Int, NodeList) :- 
	get_attr(Int, clpBNR, Def), !,     % still an interval
	(debugging(clpBNR,true) -> check_monitor_(Int, New, Def) ; true),
	Def = interval(Type,_,Nodes,_),    % get Type and Nodes
	(New = (L,H), L=:=H                % narrowed to a point, unify with interval
	 -> setarg(3,Def,_NL),             % clear node list (so nothing done in unify)
		(rational(L) -> Int=L ; Int=H) % if either bound rational (precise), use it
	 ;	setarg(2,Def,New)              % update value in interval (backtrackable)
	),
	queue_nodes_(Type,New,Int,Nodes,NodeList).   % construct node list to schedule
putValue_((L,H), Num, _) :- number(Num),  % catch things like (0,-0.0)
	L=:=Num, H=:=Num.

queue_nodes_(real,_,_,Nodes,Nodes).           % type real - just use Nodes
queue_nodes_(integer,(L,H),_,Nodes,Nodes) :-  % type integer #1 with integral bounds
	integral_(L), integral_(H), !.              % run Nodes if bounds integers or infinities 
queue_nodes_(integer,_,Int,_,[node(integral,_,0,$(Int))|_]).  % type integer #2
	% schedule an "integral" node to re-adjust bounds (Nodes run on adjustment)

integral_(1.0Inf).
integral_(-1.0Inf).
integral_(B) :- integer(B).

%
%  range(Int, Bounds) for compatability 
%
% for interval(Int) and number(Int), check if value is (always) in specified range, unifying any vars with current value
range(Int, [L,H]) :- getValue(Int, (IL,IH)), number(IL), !,  % existing interval
	(var(L) -> L=IL ; L=<IL),  % range check, no narrowing
	(var(H) -> H=IH ; IH=<H).
% for var(Int), constrain it to be an interval with specified bounds (like a declaration)
range(Int, [L,H]) :- var(Int),  % new interval
	int_decl_(real, (L,H), Int),
	getValue(Int, (L,H)).       % will bind any intput var's to values

%
%  domain(Int, Dom) for interval(Int) for compatability 
%
domain(Int, Dom) :-
	interval_object(Int, Type, Val, _),
	interval_domain_(Type, Val, Dom).

interval_domain_(integer,(0,1),boolean) :- !.  % integer(0,1) is synonomous with boolean
interval_domain_(T,(L,H),Dom) :- Dom=..[T,L,H].

%
%  delta(Int, Wid) width/span of an interval or numeric value, can be infinite
%
:- arithmetic_function(user:(delta/1)).

delta(Int, Wid) :-
	getValue(Int,(L,H)),
	Wid is roundtoward(H-L,to_positive).

%
%  midpoint(Int, Wid) midpoint of an interval or numeric value
% based on:
%	Frédéric Goualard. How do you compute the midpoint of an interval?. 
%	ACM Transactions on Mathematical Software, Association for Computing Machinery, 2014,
%	40 (2), 10.1145/2493882. hal-00576641v1
% Exception, single infinite bound treated as largest finite FP value
%
:- arithmetic_function(user:(midpoint/1)).

midpoint(Int, Mid) :-
	getValue(Int,(L,H)),
	midpoint_(L,H,Mid).

midpoint_(L,H,M)       :- L =:= -H, !, M=0.              % symmetric including (-inf,inf)
midpoint_(-1.0Inf,H,M) :- !, M is nexttoward(-1.0Inf,0)/2 + H/2.
midpoint_(L,1.0Inf,M)  :- !, M is L/2 + nexttoward(1.0Inf,0)/2.
midpoint_(L,H,M)       :- M1 is L/2 + H/2, M=M1.        % general case

%
% median(Int,Med) from CLP(RI)
% Med = 0 if Int contains 0, else a number which divides Int into equal
% numbers of FP values. Med is always a float
%
:- arithmetic_function(user:(median/1)).

median(Int, Med) :-
	getValue(Int,(L,H)),
	median_bound_(lo,L,FL),
	median_bound_(hi,H,FH),
	median_(FL,FH,Med), !.
	
median_bound_(lo,B,FB) :- B=:=0, FB is nexttoward(B,1.0).
median_bound_(lo,-1.0Inf,FB) :- FB is nexttoward(-1.0Inf,0.0).
median_bound_(lo,B,FB) :- FB is roundtoward(float(B), to_negative).

median_bound_(hi,B,FB) :- B=:=0, !, FB is nexttoward(B,-1.0).
median_bound_(hi,1.0Inf,FB) :- FB is nexttoward(1.0Inf,0.0).
median_bound_(hi,B,FB) :- FB is roundtoward(float(B), to_positive).

median_(B,B,B).                          % point interval
median_(L,H,0.0) :- L < 0.0, H > 0.0.    % contains 0 (handles (-inf,inf)
median_(L,H,M)   :- M is copysign(sqrt(abs(L))*sqrt(abs(H)),L).      % L and H have same sign

%
%  lower_bound and upper_bound
%
lower_bound(Int) :-
	getValue(Int,(L,H)),
	Int=L.

upper_bound(Int) :-
	getValue(Int,(L,H)),
	Int=H.

%
% Interval declarations
%

Ints::Dom :- list(Ints),!,
	intervals_(Ints,Dom).
	
R::Dom :- var(R), var(Dom), !,  % declare R = real(L,H), Note: R can be interval 
	int_decl_(real,(_,_),R),
	domain(R,Dom).

R::Dom :-  var(Dom), !,         % domain query (if interval(R) else fail)
	domain(R,Dom). % "domain" query, unify interval Type and Bounds

R::Dom :-                       % interval(R) or number(R) and nonvar(Dom) 
	Dom=..[Type|Bounds],
	(Bounds=[] -> Val=(_,_) ; Val=..[,|Bounds]),
	int_decl_(Type,Val,R).

int_decl_(boolean,_,R) :- !,      % boolean is integer; 0=false, 1=true, ignore any bounds.
	int_decl_(integer,(0,1),R).
	
int_decl_(Type,(L,H),R) :- interval_object(R,_IType,CVal,_NL), !,  % already interval
	lower_bound_val_(Type,L,IL),  % changing type,bounds?
	upper_bound_val_(Type,H,IH),
	applyType_(Type, R, T/T, Agenda),           % coerce reals to integers (or no-op).
	^(CVal,(IL,IH),New),          % low level functional primitive
	updateValue_(CVal, New, R, 1, Agenda, NewAgenda),  % update value (Agenda empty if no value change)
	stable_(NewAgenda).           % then execute Agenda

int_decl_(Type,(L,H),R) :- var(R), !,        % new interval (R can't be existing interval)
	lower_bound_val_(Type,L,IL),
	upper_bound_val_(Type,H,IH),
	IL=<IH,           % valid range
	(IL=IH -> 
		R=IL ;  % point range, can unify now
		put_attr(R, clpBNR, interval(Type, (IL,IH), _NL, []))  % attach clpBNR attribute
	).

int_decl_(Type,(L,H),R) :- (Type=integer -> integer(R) ; number(R)), !,    % R already a point value, check range
	lower_bound_val_(Type,L,IL), IL=<R,
	upper_bound_val_(Type,H,IH), R=<IH.

int_decl_(Type,(,),R) :- !,                   % no bounds, fill with vars
	int_decl_(Type,(_,_),R).

intervals_([],_Def).
intervals_([Int|Ints],Def) :-
	Int::Def, !,
	intervals_(Ints,Def).

lower_bound_val_(Type,L,IL) :- var(L), !,  % unspecified bound, make it finite
	finite_interval(Type,(IL,_)).
lower_bound_val_(real,L,IL) :-             % real: evaluate and round outward (if float)
	Lv is L, Lv\= 1.0Inf,
	(rational(Lv) -> IL=Lv ; IL is nexttoward(Lv,-1.0Inf)).
lower_bound_val_(integer,L,IL) :-          % integer: make integer, fail if inf
	IL is ceiling(L), IL \= 1.0Inf.
lower_bound_val_(boolean,L,IL) :-          % boolean: narrow to L=0
	IL is max(0,ceiling(L)).

upper_bound_val_(Type,H,IH) :- var(H), !,  % unspecified bound, make it finite
	finite_interval(Type,(_,IH)).
upper_bound_val_(real,H,IH) :-             % real: evaluate and round outward (if float)
	Hv is H, Hv\= -1.0Inf,
	(rational(Hv) -> IH=Hv ; IH is nexttoward(Hv,1.0Inf)).
upper_bound_val_(integer,H,IH) :-          % integer: make integer, fail if -inf
	IH is floor(H), IH \= -1.0Inf.
upper_bound_val_(boolean,H,IH) :-          % boolean: narrow to H=1
	IH is min(1,floor(H)).

applyType_(NewType, Int, Agenda, NewAgenda) :-      % narrow Int to Type
	get_attr(Int,clpBNR,interval(Type,Val,NodeList,Flags)),
	narrower_type_(NewType,Type), !,
	(debugging(clpBNR,true) -> check_monitor_(Int, NewType, interval(Type,Val,NodeList,Flags)) ; true),
	Val = (L,H),
	lower_bound_val_(NewType,L,IL),
	upper_bound_val_(NewType,H,IH),
	(IL=IH
	 -> Int=IL  % narrowed to point
	 ; 	(put_attr(Int,clpBNR,interval(integer,(IL,IH),NodeList,Flags)),  % set Type (only case allowed)
		 linkNodeList_(NodeList, Agenda, NewAgenda)
		)
	).
applyType_(NewType, Int, Agenda, Agenda).            % anything else: no change

narrower_type_(integer,real).
narrower_type_(boolean,integer).
narrower_type_(boolean,real).

%
% this goal gets triggered whenever an interval is unified, valid for a numeric value or another interval
%
attr_unify_hook(IntDef, Num) :-         % unify an interval with a numeric
	number(Num),
	IntDef = interval(Type,(L,H),Nodelist,Flags),
	(Type=integer -> integer(Num) ; true),   % check that Num is consistent with Type
	L=<Num, Num=<H, !,                       % and in range
	(debugging(clpBNR,true) -> monitor_unify_(IntDef, Num) ; true),
	linkNodeList_(Nodelist, T/T, Agenda),
	stable_(Agenda).                    % broadcast change

attr_unify_hook(interval(Type1,V1,Nodelist1,Flags1), Int) :-   % unifying two intervals
	get_attr(Int, clpBNR, interval(Type2,V2,Nodelist2,Flags2)),  %%SWIP attribute def.
	mergeType_(Type1, Type2, NewType),  % unified Type=integer if either is an integer
	^(V1,V2,V), !,                      % unified range is intersection (from ia_primitives),
	mergeNodes_(Nodelist2,Nodelist1,Newlist),  % unified node list is a merge of two lists
	mergeFlags_(Flags1,Flags2,Flags),
	(debugging(clpBNR,true) -> monitor_unify_(interval(Type1,V1,_,Flags), Int) ; true),
	% update new type, value and constraint list, undone on backtracking
	put_attr(Int,clpBNR,interval(NewType,V,Newlist,Flags)),
	linkNodeList_(Newlist, T/T, Agenda),
	stable_(Agenda).                    % broadcast change

attr_unify_hook(interval(Type,Val,Nodelist,Flags), V) :-   % new value out of range
	g_inc('clpBNR:evalNodeFail'),  % count of primitive call failures
	debugging(clpBNR, true),       % fail immediately unless debug=true
	debug_clpBNR_('Failed to unify ~w::~w with ~w',[Type,Val,V]),
	fail.

% awkward monitor case because original interval gone
monitor_unify_(IntDef, Update) :-  % debbuging, manufacture temporary interval
	put_attr(Temp,clpBNR,IntDef),
	check_monitor_(Temp, Update, IntDef).

% if both real, result type is real, else one is integer so result type integer
mergeType_(real, real, real) :- !.
mergeType_(_,    _,    integer).

% optimize for one or both lists (dominant case)
mergeFlags_([],Flags2,Flags2) :- !.
mergeFlags_(Flags1,[],Flags1) :- !.
mergeFlags_([F1|Flags1],Flags2,Flags) :-   % discard if F in Flags2 
	functor(F1,N,1),                       % ignore value
	functor(F2,N,1),
	memberchk(F2,Flags2), !,
	mergeFlags_(Flags1,Flags2,Flags).
mergeFlags_([F1|Flags1],Flags2,[F1|Flags]) :-  % keep F, not in Flags2 
	mergeFlags_(Flags1,Flags2,Flags).

% merge two node lists removing duplicates based on operation and arguments
mergeNodes_([N],NodeList,NodeList) :- var(N),!.         % end of list
mergeNodes_([node(Op,_,_,Ops)|Ns],NodeList,NewList) :-  % if same Op and Ops, discard
	matching_node_(NodeList,Op,Ops), !,
	mergeNodes_(Ns,NodeList,NewList).
mergeNodes_([N|Ns],NodeList,[N|NewList]) :-             % not a duplicate, retain
	mergeNodes_(Ns,NodeList,NewList).

matching_node_([node(Op,_,_,NOps)|Ns],Op,Ops) :-
	NOps==Ops, !.  % identical args
matching_node_([N|Ns],Op,Ops) :-
	nonvar(N),     % not end of list
	matching_node_(Ns,Op,Ops).

%
% New Constraints use { ... } syntax.
%
{}.
{Cons} :-
	term_variables(Cons, CVars),
	declare_vars_(CVars),                     % convert any plain vars to intervals
	addConstraints_(Cons,T/T,Agenda),         % add constraints
	stable_(Agenda).                          % then execute Agenda

declare_vars_([]).
declare_vars_([CV|CVars]) :-
	(interval(CV) -> true ; new_interval_(CV,real)),
	declare_vars_(CVars).

new_interval_(V,Type) :-
	universal_interval(UI),
	int_decl_(Type,UI,V).

addConstraints_(C,Agenda,NewAgenda) :-
	constraint_(C), !, % a constraint is a boolean expression that evaluates to true
	simplify(C,CS),    % optional
	buildConstraint_(CS, Agenda, NewAgenda).
addConstraints_((C,Cs),Agenda,NewAgenda) :-  % Note: comma as operator
	nonvar(C),
	addConstraints_(C,Agenda,NextAgenda), !,
	addConstraints_(Cs,NextAgenda,NewAgenda).
addConstraints_([],Agenda,Agenda).
addConstraints_([C|Cs],Agenda,NewAgenda) :-
	nonvar(C),
	addConstraints_(C,Agenda,NextAgenda), !,
	addConstraints_(Cs,NextAgenda,NewAgenda).

% low overhead version for internal use	
constrain_(C) :- 
	buildConstraint_(C,T/T,Agenda),
	stable_(Agenda).
	
buildConstraint_(C,Agenda,NewAgenda) :-
	debug_clpBNR_('Add ~p',{C}),
	build_(C, 1, boolean, Agenda, NewAgenda), !.
buildConstraint_(C,Agenda,NewAgenda) :-
	debug_clpBNR_('{} failure due to bad constraint: ~p',{C}),
	fail.

:- include(clpBNR/ia_simplify).  % simplifies constraints to a hopefully more efficient equivalent

%
% build a node from an expression
%
build_(Int, Int, VarType, Agenda, NewAgenda) :-
	interval(Int), !,                                   % existing interval object
	applyType_(VarType, Int, Agenda, NewAgenda).        % coerces exsiting intervals to required type
build_(Var, Var, VarType, Agenda, Agenda) :-            % implicit interval creation.
	var(Var), !,
	new_interval_(Var,VarType).
build_(Num, Num, _, Agenda, Agenda) :-                  % rational numeric value is precise
	rational(Num), !.
build_(Num, Int, VarType, Agenda, Agenda) :-            % floating point constant, may not be precise
	float(Num), !,
	(
	float_class(Num,infinite)
	 -> Int=Num                                         % infinities are point values
	 ;	int_decl_(VarType,(Num,Num),Int)                % may be fuzzed, so not a point
	).
build_(pt(Num), Num, _, Agenda, Agenda) :-              % point value, must be a number
	number(Num), !.
build_(Exp, Num, VarType, Agenda, Agenda) :-            % pre-compile ground Exp (including pi and e)
	ground(Exp),
	safe_(Exp),                                         % safe to evaluate 
	L is roundtoward(Exp,to_negative),                  % rounding only affects float evaluation
	H is roundtoward(Exp,to_positive),
	(L==H 
	 -> build_(L, Num, VarType, Agenda, Agenda)         % point value
	 ;	int_decl_(VarType,(L,H),Num)                    % imprecise so interval
	), !.
build_(Exp, Z, _, Agenda, NewAgenda) :-                 % deconstruct to primitives
	Exp =.. [F|Args],
	fmap_(F,Op,[Z|Args],ArgsR,Types), !,                % supported arithmetic op
	build_args_(ArgsR,Objs,Types,Agenda,ObjAgenda),
	newNode_(Op,Objs,ObjAgenda,NewAgenda).

build_args_([],[],_,Agenda,Agenda).
build_args_([Arg|ArgsR],[Obj|Objs],[Type|Types],Agenda,NewAgenda) :-
	build_(Arg,Obj,Type,Agenda,NxtAgenda),
	build_args_(ArgsR,Objs,Types,NxtAgenda,NewAgenda).

% only called when argument is ground
safe_(E) :- atomic(E), !.  % all atomics, including []
safe_([A|As]) :- !,
	safe_(A),
	safe_(As).
safe_(_/Z) :- (Z==0.0 ; Z== -0.0), !,                   % division by 0.0 requires fuzzed 0.0
	fail.
safe_(F) :- 
	current_arithmetic_function(F),                     % evaluable by is/2
	F =.. [Op|Args],
	\+memberchk(Op,[**,sin,cos,tan,asin,acos,atan]),    % unsafe operations due to uncertain precision
	safe_(Args).

%  a constraint must evaluate to a boolean 
constraint_(C) :- nonvar(C), C =..[Op|_], fmap_(Op,_,_,_,[boolean|_]), !.

%  map constraint operator to primitive/arity/types
fmap_(+,    add,   ZXY,     ZXY,     [real,real,real]).
fmap_(-,    add,   [Z,X,Y], [X,Z,Y], [real,real,real]).     % note subtract before minus 
fmap_(*,    mul,   ZXY,     ZXY,     [real,real,real]).
fmap_(/,    mul,   [Z,X,Y], [X,Z,Y], [real,real,real]).
fmap_(**,   pow,   ZXY,     ZXY,     [real,real,real]).
fmap_(min,  min,   ZXY,     ZXY,     [real,real,real]).
fmap_(max,  max,   ZXY,     ZXY,     [real,real,real]).
fmap_(==,   eq,    ZXY,     ZXY,     [boolean,real,real]).  % strict equality
fmap_(=:=,  eq,    ZXY,     ZXY,     [boolean,real,real]).  % Prolog compatible, strict equality
fmap_(is,   eq,    ZXY,     ZXY,     [boolean,real,real]).
fmap_(<>,   ne,    ZXY,     ZXY,     [boolean,integer,integer]).
fmap_(=\=,  ne,    ZXY,     ZXY,     [boolean,integer,integer]).  % Prolog compatible
fmap_(=<,   le,    ZXY,     ZXY,     [boolean,real,real]).
fmap_(>=,   le,    [Z,X,Y], [Z,Y,X], [boolean,real,real]).
fmap_(<,    lt,    ZXY,     ZXY,     [boolean,real,real]).
fmap_(>,    lt,    [Z,X,Y], [Z,Y,X], [boolean,real,real]).
fmap_(<=,   in,    ZXY,     ZXY,     [boolean,real,real]).  % inclusion/subinterval
fmap_(=>,   in,    [Z,X,Y], [Z,Y,X], [boolean,real,real]).  % inclusion/subinterval

fmap_(and,  and,   ZXY,     ZXY,     [boolean,boolean,boolean]).
fmap_(or,   or,    ZXY,     ZXY,     [boolean,boolean,boolean]).
fmap_(nand, nand,  ZXY,     ZXY,     [boolean,boolean,boolean]).
fmap_(nor,  nor,   ZXY,     ZXY,     [boolean,boolean,boolean]).
fmap_(xor,  xor,   ZXY,     ZXY,     [boolean,boolean,boolean]).
fmap_(->,   imB,   ZXY,     ZXY,     [boolean,boolean,boolean]).

fmap_(sqrt,sqrt,  ZX,       ZX,      [real,real]).          % pos. root version vs. **(1/2)
fmap_(-,   minus, ZX,       ZX,      [real,real]).
fmap_(~,   not,   ZX,       ZX,      [boolean,boolean]).
fmap_(exp, exp,   ZX,       ZX,      [real,real]).
fmap_(log, exp,   [Z,X],    [X,Z],   [real,real]).
fmap_(abs, abs,   ZX,       ZX,      [real,real]).
fmap_(sin, sin,   ZX,       ZX,      [real,real]).
fmap_(asin,sin,   [Z,X],    [X,Z],   [real,real]).
fmap_(cos, cos,   ZX,       ZX,      [real,real]).
fmap_(acos,cos,   [Z,X],    [X,Z],   [real,real]).
fmap_(tan, tan,   ZX,       ZX,      [real,real]).
fmap_(atan,tan,   [Z,X],    [X,Z],   [real,real]).

% reverse map from Op and Args (used by "verbose" top level output to reverse compile constraints)
remap_(Op,$(Z,X,Y),C) :- constraint_(Op), Z==1, !,  % simplification for constraints
	C=..[Op,X,Y]. 
remap_(Op,$(Z,X,Y),Z==C) :- !,
	C=..[Op,X,Y].
remap_(Op,$(Z,X),Z==C) :-
	C=..[Op,X].

%
% Node constructor
%
% First clause is an optimization for E1 == E2
%	In that case just unify E1 and E2; heavy lifting done by attr_unify_hook.
newNode_(eq, [Z,X,Y], Agenda, Agenda) :- Z==1, !, X=Y.
newNode_(Op, Objs, Agenda, NewAgenda) :-
	Args =.. [$|Objs],  % store arguments as $/N where N=1..3
	NewNode = node(Op, P, 0, Args),  % L=0
	addNode_(Objs,NewNode),
	% increment count of added nodes, will be decremented on backtracking/failure
	g_incb('clpBNR:node_count'),
	linkNode_(Agenda, NewNode, NewAgenda).

addNode_([],_Node).
addNode_([Arg|Args],Node) :-
	(interval_object(Arg, _Type, _Val, Nodelist) -> newmember(Nodelist, Node) ; true),
	addNode_(Args,Node).

sandbox:safe_global_variable('clpBNR:node_count').

clpStatistics :-
	g_assign('clpBNR:node_count',0),  % reset/initialize node count to 0
	fail.  % backtrack to reset other statistics.

clpStatistic(node_count(C)) :-
	g_read('clpBNR:node_count',C).

% extend list with X
newmember([X|Xs],N) :- 
	nonvar(X), !,       % not end of (indefinite) list
	newmember(Xs,N).
newmember([N|_],N).     % end of list

%
% Process Agenda to narrow intervals (fixed point iteration)
%
stable_([]/[]) :- !.  % small optimization when agenda is empty
stable_(Agenda) :-
	current_prolog_flag(clpBNR_iteration_limit,Ops),  % budget for current operation
	stableLoop_(Agenda,Ops),
	!.  % achieved stable state with empty Agenda -> commit.

stableLoop_([]/[], OpsLeft) :- !,           % terminate successfully when agenda comes to an end
	g_read('clpBNR:iterations',Cur),        % maintain "low" water mark (can be negative)
	(OpsLeft<Cur -> g_assign('clpBNR:iterations',OpsLeft) ; true),
	(OpsLeft<0 -> E is -OpsLeft, debug_clpBNR_('Iteration throttle limit exceeded by ~w ops.',E) ; true).
stableLoop_([Node|Agenda]/T, OpsLeft) :-
	Node = node(Op,P,_,Args),  % if node on queue ignore link bit (was: Node = node(Op,P,1,Args))
	doNode_(Args, Op, P, OpsLeft, Agenda/T, NewAgenda),  % undoable on backtrack
	nb_setarg(3,Node,0),                    % reset linked bit
	RemainingOps is OpsLeft-1,              % decrement OpsLeft (can go negative)
	stableLoop_(NewAgenda,RemainingOps).

% support for max_iterations statistic
sandbox:safe_global_variable('clpBNR:iterations').

clpStatistics :-
	current_prolog_flag(clpBNR_iteration_limit,L), 
	g_assign('clpBNR:iterations',L),  % set "low" water mark to upper limit
	fail.  % backtrack to reset other statistics.

clpStatistic(max_iterations(O/L)) :-
	g_read('clpBNR:iterations',Ops),
	current_prolog_flag(clpBNR_iteration_limit,L),
	O is L-Ops.  % convert "low" water mark to high water mark

%
% Execute a node on the queue
%
:- if(current_predicate(system:expand_goal/2)).

% Comment out the following to enable Op tracing:
goal_expansion(traceIntOp_(Op, Args, PrimArgs, New),true).

:- endif.

doNode_($(ZArg,XArg,YArg), Op, P, OpsLeft, Agenda, NewAgenda) :-  % Arity 3 Op
	var(P), !,                                    % check persistent bit
	%	nonground(Args,_), !,  % not safe, unifications happens before attr_unify_hook
	getValue(ZArg,ZVal),
	getValue(XArg,XVal),
	getValue(YArg,YVal),
	evalNode(Op, P, $(ZVal,XVal,YVal), $(NZVal,NXVal,NYVal)),  % can fail causing stable_ to fail => backtracking
	% constraint consistency check - if two var arguments are the same, they must narrow to same value
	(var(ZArg)
	 ->	(ZArg==XArg -> NZVal=NXVal ; true),
		(ZArg==YArg -> NZVal=NYVal ; true)
	 ; true
	),
	(var(XArg)
	 -> (XArg==YArg -> NXVal=NYVal ; true)   % even if not specified as such
	 ;	true
	),
	traceIntOp_(Op, [ZArg,XArg,YArg], [ZVal,XVal,YVal], [NZVal,NXVal,NYVal]),  % in ia_utilities
	updateValue_(ZVal, NZVal, ZArg, OpsLeft, Agenda, AgendaZ),	
	updateValue_(XVal, NXVal, XArg, OpsLeft, AgendaZ, AgendaZX),	
	updateValue_(YVal, NYVal, YArg, OpsLeft, AgendaZX, NewAgenda).	

doNode_($(ZArg,XArg), Op, P, OpsLeft, Agenda, NewAgenda) :-        % Arity 2 Op
	var(P), !,                                    % check persistent bit
	%	nonground(Args,_), !,  % not safe, unifications happens before attr_unify_hook
	getValue(ZArg,ZVal),
	getValue(XArg,XVal),
	evalNode(Op, P, $(ZVal,XVal), $(NZVal,NXVal)),        % can fail causing stable_ to fail => backtracking
	% constraint consistency check - if two var arguments are the same, they must narrow to same value
	(var(ZArg)
	 -> (ZArg==XArg -> NZVal=NXVal ; true)
	 ;	true
	),
	traceIntOp_(Op, [ZArg,XArg], [ZVal,XVal], [NZVal,NXVal]), % in ia_utilities
	updateValue_(ZVal, NZVal, ZArg, OpsLeft, Agenda, AgendaZ),
	updateValue_(XVal, NXVal, XArg, OpsLeft, AgendaZ, NewAgenda).

doNode_($(Arg), Op, P, OpsLeft, Agenda, NewAgenda) :-              % Arity 1 Op
	var(P), !,                                    % check persistent bit
	%	nonground(Args,_), !,  % not safe, unifications happens before attr_unify_hook
	getValue(Arg,Val),
	evalNode(Op, P, $(Val), $(NVal)),                     % can fail causing stable_ to fail => backtracking
	traceIntOp_(Op, [Arg], [Val], [NVal]),              % in ia_utilities
	updateValue_(Val, NVal, Arg, 1, Agenda,NewAgenda).  % always update value regardless of OpsLeft limiter	

doNode_(Args, Op, p, _, Agenda, Agenda) :-    % persistent bit "set", skip node and trim
	trim_ops_(Args).

%
% called whenever a persistent node is encountered in FP iteration
%	remove it from any node arguments
%
trim_ops_($(Op1,Op2,Op3)) :-
	trim_op_(Op1),
	trim_op_(Op2),
	trim_op_(Op3).
trim_ops_($(Op1,Op2)) :-
	trim_op_(Op1),
	trim_op_(Op2).
trim_ops_($(Op1)) :-
	trim_op_(Op1).

trim_op_(Arg) :- 
	(number(Arg)
	 -> true
	 ;	get_attr(Arg, clpBNR, Def),     % an interval ?
		arg(3,Def,NList),  %%Def = interval(_, _, NList, _),
		trim_persistent_(NList,TrimList),
		% if trimmed list empty, set to a new unshared var to avoid cycles(?) on backtracking
		(var(TrimList) -> setarg(3,Def,_) ; setarg(3,Def,TrimList))  % write trimmed node list
	).

trim_persistent_(T,T) :- var(T), !.    % end of indefinite list  
trim_persistent_([node(_,P,_,_)|Ns],TNs) :- nonvar(P), !, trim_persistent_(Ns,TNs).
trim_persistent_([N|Ns],[N|TNs]) :- trim_persistent_(Ns,TNs).

%
% Any changes in interval values should come through here.
% Note: This captures all updated state for undoing on backtracking
%
updateValue_(Old, Old, _, _, Agenda, Agenda) :- !.                  % no change in value (constant?)

updateValue_(Old, New, Int, OpsLeft, Agenda, NewAgenda) :-          % set interval value to New
	% New = [NewL,NewH], (NewL > NewH -> trace ; true),
	% NewL=<NewH,  % check unnecessary if primitives do their job
	chk_float_overwrite(Old, New, New1),         % change, check for unnecessary float conversions on bounds
	(OpsLeft>0 -> true ; propagate_if_(Old, New1)), !,  % if OpsLeft >0 or narrowing sufficent
	putValue_(New1, Int, Nodelist),              % update value (may fail)
	linkNodeList_(Nodelist, Agenda, NewAgenda).  % then propagate change

updateValue_(_, _, _, _, Agenda, Agenda).        % otherwise just continue with Agenda

% check that a precise bound isn't overwritten by equivalent float
% fail if recalculated New same as Old
chk_float_overwrite((OL,OH), (NL,NH), (NL1,NH1)) :-
	(rational(OL), float(NL), OL =:= NL -> NL1 = OL ; NL1 = NL),
	(rational(OH), float(NH), OH =:= NH -> NH1 = OH ; NH1 = NH),
	(NL1 = OL, NH1 = OH -> fail ; true).

% propgate if sufficient narrowing (> 10%)
propagate_if_((OL,OH), (NL,NH)) :- (NH-NL)/(OH-OL) < 0.9.  % any overflow in calculation will propagate

linkNodeList_([X|Xs], List, NewList) :-
	(var(X)                                      % end of list? ...
	 -> NewList=List                             % Yes - don't make it definite
	 ;  (arg(3,X,1)                              % No  - test linked flag
	 	 -> NextList = List                      % already linked
		 ;  linkNode_(List, X, NextList)         % not linked add it to list
		),
		linkNodeList_(Xs, NextList, NewList)     % add rest of the node list
	).

% Assumes persistant nodes are pre-trimmed (see putValue_/3)
linkNode_(List/[X|NextTail], X, List/NextTail) :-  % add to list
	setarg(3,X,1).                               % set linked bit

:- include(clpBNR/ia_utilities).  % print,solve, etc.

%
% Get all defined statistics
%
clpStatistics(Ss) :- findall(S, clpStatistic(S), Ss).

% end of reset chain succeeds. Need cut since predicate is "discontiguous".
clpStatistics :- !.

%
% module initialization
%
check_features :-
	(current_prolog_flag(bounded,true)
	 -> print_message(error, clpBNR(bounded))
	 ;  true
	),
	(current_prolog_flag(float_overflow,_)
	 -> true
	 ;  print_message(error, clpBNR(no_IEEE))
	).

version_info :-
	print_message(informational, clpBNR(versionInfo)).

set_min_free(Amount) :-
	once(prolog_stack_property(global,min_free(Free))), % minimum free cells (8 bytes/cell)
	(Free < Amount ->	set_prolog_stack(global,min_free(Amount)) ; true).

:- multifile prolog:message//1.	

prolog:message(clpBNR(bounded)) -->
	[ 'clpBNR requires unbounded integers and rationals.'-[] ].

prolog:message(clpBNR(no_IEEE)) -->
	[ 'clpBNR requires support for IEEE arithmetic.'-[] ].

prolog:message(clpBNR(versionInfo)) -->
	{ version(Version) },
	[ '*** clpBNR v~walpha ***.'-[Version] ].

init_clpBNR :-
	restore_optimise,
	version_info,
	check_features,
	set_prolog_flags,
	set_min_free(8196).

:- initialization(init_clpBNR, now).
