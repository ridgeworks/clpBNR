%
% CLP(BNR) == Constraints On Boolean, Integer, and Real Intervals
%
/*	The MIT License (MIT)
 *
 *	Copyright (c) 2019-2023 Rick Workman
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

:- if((current_prolog_flag(version,V), V < 90105)).

% Use history(expanded(...) from boot/messages.pl to avoid additional message template
:- print_message(error,history(expanded("This version of clpBNR requires SWIP 9.1.5 or greater"))).

:- op(1199, xfx, ::).         % suppresses errors while parsing
:- style_check(-singleton).   % suppresses warnings while parsing

:- else.

:- module(clpBNR,          % SWI module declaration
	[
	op(700, xfx, ::),
	(::)/2,                % declare interval
	{}/1,                  % define constraint
	interval/1,            % filter for clpBNR constrained var
	interval_degree/2,     % number of constraints on clpBNR constrained var
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
	% op(500, yfx, xor),   % boolean 'xor', but operator already defined (P=400) for arithmetic
	op(700, xfx, <>),      % integer not equal
	op(700, xfx, <=),      % included (one way narrowing)

	% utilities
	print_interval/1, print_interval/2,      % pretty print interval with optional stream
	small/1, small/2,      % defines small interval width based on precision value
	solve/1, solve/2,      % solve (list of) intervals using split to find point solutions
	splitsolve/1, splitsolve/2,   % solve (list of) intervals using split
	absolve/1, absolve/2,  % absolve (list of) intervals, narrows by nibbling bounds
	enumerate/1,           % "enumerate" integers
	global_minimum/2,      % find interval containing global minimum(s) for an expression
	global_minimum/3,      % global_minimum/2 with definable precision
	global_maximum/2,      % find interval containing global maximum(s) for an expression
	global_maximum/3,      % global_maximum/2 with definable precision
	global_minimize/2,     % global_minimum/2 plus narrow vars to found minimizers
	global_minimize/3,     % global_minimum/3 plus narrow vars to found minimizers
	global_maximize/2,     % global_maximum/2 plus narrow vars to found maximizers
	global_maximize/3,     % global_maximum/3 plus narrow vars to found maximizers
	nb_setbounds/2,        % non-backtracking set bounds (use with branch and bound)
	partial_derivative/3,  % differentiate Exp wrt. X and simplify
	clpStatistics/0,       % reset
	clpStatistic/1,        % get selected
	clpStatistics/1,       % get all defined in a list
	watch/2,               % enable monitoring of changes for interval or (nested) list of intervals
	trace_clpBNR/1         % enable/disable tracing of clpBNR narrowing ops
	]).

/*		missing(?) functionality from original CLP(BNR): utility accumulate/2.		*/

/* supported interval relations:

+	-	*	/                         %% arithmetic
**                                    %% includes real exponent, odd/even integer
abs                                   %% absolute value
sqrt                                  %% positive square root
min	max                               %% binary min/max
==	is	<>	=<	>=	<	>             %% comparison (`is` synonym for `==`)
<=	                                  %% included (one way narrowing)
and	or	nand	nor	xor	->	,         %% boolean (`,` synonym for `and`)
-	~                                 %% unary negate and not
exp	log                               %% exp/ln
sin	asin	cos	acos	tan	atan      %% trig functions
integer                               %% must be an integer value

*/

version("0.11.2").

:- style_check([-singleton, -discontiguous]).  % :- discontiguous ... not reliable.

%
% Define debug_clpBNR_/2 before turning on optimizer removing debug calls.
% Note: global "optimise" flag will be restored after load completes.
%
:- set_prolog_flag(optimise,false).

debug_clpBNR_(FString,Args) :- debug(clpBNR,FString,Args).

trace_clpBNR_(FString,Args) :- debug(clpBNR(trace),FString,Args).

:- set_prolog_flag(optimise,true).

current_node_(Node) :-  % look back to find current Op being executed for debug messages
	prolog_current_frame(F),  % this is a little grungy, but necessary to get intervals
	prolog_frame_attribute(F,parent_goal,doNode_(Args,Op,_,_,_,_,_)),
	map_constraint_op_(Op,Args,Node),
	!.

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

sandbox:safe_global_variable('clpBNR:thread_init_done').
sandbox:safe_global_variable('clpBNR:userTime').
sandbox:safe_global_variable('clpBNR:inferences').
sandbox:safe_global_variable('clpBNR:gc_time').

%  
% Global var statistics are per thread and therefore must be "lazily" initialized
% Also ensures that thread copies of flags are properly set.
% This exception handler will be invoked the first time 'clpBNR:thread_init_done' is read
% Public predicates ::. {}. and range read this global before proceeding. 
%
user:exception(undefined_global_variable,'clpBNR:thread_init_done',retry) :- !,
	set_prolog_flags,  % initialize/check environment flags  
	clpStatistics,     % define remaining globals 
	g_assign('clpBNR:thread_init_done',1).

%
% Set required arithmetic flags (see module/thread initialization)
%
set_prolog_flags :-
	set_prolog_flag(prefer_rationals, true),           % enable rational arithmetic
	(current_prolog_flag(max_rational_size,_)
	 -> true                                           % already defined, leave as is
	 ;  set_prolog_flag(max_rational_size, 16)         % rational size in bytes before ..
	),
	set_prolog_flag(max_rational_size_action, float),  % conversion to float

	set_prolog_flag(float_overflow,infinity),          % enable IEEE continuation values
	set_prolog_flag(float_zero_div,infinity),
	set_prolog_flag(float_undefined,nan),
	
	% clpBNR specific Prolog environment flags - overwrite if necessary
	(current_prolog_flag(clpBNR_iteration_limit,_)
	 -> true
	 ;  create_prolog_flag(clpBNR_iteration_limit,3000,[type(integer),keep(true)])
	),
	(current_prolog_flag(clpBNR_default_precision,_)
	 -> true
	 ;  create_prolog_flag(clpBNR_default_precision,6,[type(integer),keep(true)])
	),
	(current_prolog_flag(clpBNR_verbose,_)
	 -> true
	 ;  create_prolog_flag(clpBNR_verbose,false,[type(boolean),keep(true)])
	).

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
%  interval(Int)  - filter
%
interval(Int) :- get_attr(Int, clpBNR, _).

%
%  interval_degree/2   % N = number of constraints on interval(Int), 0 for number(Int)
%
interval_degree(X, N) :- 
	interval_object(X, _, _, Nodelist)
	-> system:'$skip_list'(N, Nodelist, _) % optimized for SWIP, handles indefinite lists
	;  number(X), N = 0.                   % number -> no constraints ; fail

% internal abstraction
interval_object(Int, Type, Val, Nodelist) :-
	get_attr(Int, clpBNR, interval(Type, Val, Nodelist, _)).

% flags (list)  abstraction
get_interval_flags_(Int, Flags) :-
	get_attr(Int, clpBNR, interval(_, _, _, Flags)).
	
set_interval_flags_(Int, Flags) :-  % flags assumed to be ground so no copy required
	interval_object(Int, Type, Val, Nodelist),
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

% legal integer bounds values
integerBnd(1.0Inf).
integerBnd(-1.0Inf).
integerBnd(B) :- integer(B).

% precise bounds values
preciseBnd(1.0Inf).
preciseBnd(-1.0Inf).
preciseBnd(B) :- rational(B).

%
%  non-backtracking set bounds for use with branch and bound
%
nb_setbounds(Int, [L,U]) :- 
	get_attr(Int, clpBNR, Def),
	arg(2, Def, Val),             % WAM code
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
% set interval value (assumes bounds check has already been done)
% Note: putValue_ cannot modify the new value since the narrowing op is still in the Agenda
%	and may not be run again. Insert `integral` op for integer bounds adjustment.
%
putValue_(New, Int, NodeList) :- 
	get_attr(Int, clpBNR, Def)             % still an interval ?
	 -> (debugging(clpBNR,true) -> check_monitor_(Int, New, Def) ; true),
	    Def = interval(Type,_,Nodes,_),    % get Type and Nodes for queueing
	    New = (L,H),
	    ( 0 is cmpr(L,H)                   % point interval ->
	     -> setarg(3,Def,_NL),             % clear node list (so nothing done in unify)
	        pointValue_(L,H,Int),          % unify, avoiding -0.0 and preferring rational (invokes hook)
	        NodeList = Nodes               % still add Nodes to Agenda
	     ;  setarg(2,Def,New),             % update value in interval (backtrackable)
	        % if integer has non-integral bounds, schedule `integral` op to fix it
	        (Type == integer
	         -> ( integerBnd(L), integerBnd(H) -> NodeList = Nodes ; NodeList = [node(integral,_,0,$(Int))|_] )
	         ;  NodeList = Nodes
	        )
	    )
	 ; true.  % no longer an interval, NodeList is empty

pointValue_(-0.0,_,0.0) :-!.
pointValue_(L,H,Int) :- (rational(L) -> Int = L ; Int = H).

%
%  range(Int, Bounds) for compatibility 
%
% for interval(Int) and number(Int), check if value is (always) in specified range, unifying any vars with current value
range(Int, [L,H]) :- getValue(Int, (IL,IH)), number(IL), !,  % existing interval
	(var(L) -> L=IL ; non_empty(L,IL)),  % range check (L=<IL,IH=<H), no narrowing
	(var(H) -> H=IH ; non_empty(IH,H)).
% for var(Int), constrain it to be an interval with specified bounds (like a declaration)
range(Int, [L,H]) :- var(Int),  % new interval
	g_read('clpBNR:thread_init_done',_),  % ensures per-thread initialization
	int_decl_(real, (L,H), Int),
	getValue(Int, (L,H)).       % will bind any input var's to values

%
%  domain(Int, Dom) for interval(Int)
%
domain(Int, Dom) :-
	interval_object(Int, Type, Val, _),
	interval_domain_(Type, Val, Dom).

interval_domain_(integer,(0,1),boolean) :- !.  % integer(0,1) is synonymous with boolean
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
	g_read('clpBNR:thread_init_done',_),  % ensures per-thread initialization
	int_decl_(real,(_,_),R),
	domain(R,Dom).

R::Dom :-  var(Dom), !,         % domain query (if interval(R) else fail)
	domain(R,Dom). % "domain" query, unify interval Type and Bounds

R::Dom :-                       % interval(R) or number(R) and nonvar(Dom) 
	Dom=..[Type|Bounds],
	(Bounds=[] -> Val=(_,_) ; Val=..[','|Bounds]),
	g_read('clpBNR:thread_init_done',_),  % ensures per-thread initialization
	int_decl_(Type,Val,R).

int_decl_(boolean,_,R) :- !,      % boolean is integer; 0=false, 1=true, ignore any bounds.
	int_decl_(integer,(0,1),R).
	
int_decl_(Type,Val,R) :- interval_object(R,CType,CVal,_NL), !,  % already interval
	(Type = CType, Val = CVal         % query, no change
	 -> true
	 ;	Val = (L,H),                  % changing type,bounds?
	    lower_bound_val_(Type,L,IL),
	    upper_bound_val_(Type,H,IH),
	    applyType_(Type, R, T/T, Agenda),           % coerce reals to integers (or no-op).
	    ^(CVal,(IL,IH),New),          % low level functional primitive
	    updateValue_(CVal, New, R, 1, Agenda, NewAgenda),  % update value (Agenda empty if no value change)
	    stable_(NewAgenda)            % then execute Agenda
	).

int_decl_(Type,(L,H),R) :- var(R), !,        % new interval (R can't be existing interval)
	lower_bound_val_(Type,L,IL),
	upper_bound_val_(Type,H,IH),
	C is cmpr(IL,IH),  % compare bounds
	(C == 0
	 -> (rational(IL) -> R=IL ; R = IH)  % point range, can unify now
	 ;  C == -1,                         % necessary condition: IL < IH
	    put_attr(R, clpBNR, interval(Type, (IL,IH), _NL, []))  % attach clpBNR attribute
	).

int_decl_(Type,(L,H),R) :- (Type=integer -> integer(R) ; number(R)), !,    % R already a point value, check range
	lower_bound_val_(Type,L,IL), non_empty(IL,R),  % IL=<R,
	upper_bound_val_(Type,H,IH), non_empty(R,IH).  % R=<IH.

int_decl_(Type,(','),R) :- !,                   % no bounds, fill with vars
	int_decl_(Type,(_,_),R).

intervals_([],_Def).
intervals_([Int|Ints],Def) :-
	Int::Def, !,
	intervals_(Ints,Def).

lower_bound_val_(Type,L,IL) :- var(L), !,  % unspecified bound, make it finite
	finite_interval(Type,(IL,_)).
lower_bound_val_(real,L,IL) :-             % real: evaluate and round outward (if float)
	((L == pi ; L == e)
	 -> IL is roundtoward(L,to_negative)
	 ;  Lv is L,
	    (preciseBnd(Lv) -> IL=Lv ; IL is nexttoward(Lv,-1.0Inf)) 
	).
lower_bound_val_(integer,L,IL) :-          % integer: make integer, fail if inf
	IL is ceiling(L), IL \= 1.0Inf.
lower_bound_val_(boolean,L,IL) :-          % boolean: narrow to L=0
	IL is max(0,ceiling(L)).

upper_bound_val_(Type,H,IH) :- var(H), !,  % unspecified bound, make it finite
	finite_interval(Type,(_,IH)).
upper_bound_val_(real,H,IH) :-             % real: evaluate and round outward (if float)
	((H == pi ; H == e)
	 -> IH is roundtoward(H,to_positive)
	 ;  Hv is H,
	    (preciseBnd(Hv) -> IH=Hv ; IH is nexttoward(Hv,1.0Inf)) 
	).
upper_bound_val_(integer,H,IH) :-          % integer: make integer, fail if -inf
	IH is floor(H), IH \= -1.0Inf.
upper_bound_val_(boolean,H,IH) :-          % boolean: narrow to H=1
	IH is min(1,floor(H)).

applyType_(NewType, Int, Agenda, NewAgenda) :-      % narrow Int to Type
	get_attr(Int,clpBNR,interval(Type,Val,NodeList,Flags)),
	(NewType @< Type    % standard order of atoms:  boolean @< integer @< real
	 -> (debugging(clpBNR,true) -> check_monitor_(Int, NewType, interval(Type,Val,NodeList,Flags)) ; true),
	    Val = (L,H),
	    lower_bound_val_(NewType,L,IL),
	    upper_bound_val_(NewType,H,IH),
	    (IL=IH
	     -> Int=IL  % narrowed to point
	     ; 	(put_attr(Int,clpBNR,interval(integer,(IL,IH),NodeList,Flags)),  % set Type (only case allowed)
		     linkNodeList_(NodeList, Agenda, NewAgenda)
		    )
	    )
	 ; NewAgenda = Agenda
	).

%
% this goal gets triggered whenever an interval is unified, valid for a numeric value or another interval
%
attr_unify_hook(IntDef, Num) :-         % unify an interval with a numeric
	number(Num),
	IntDef = interval(Type,(L,H),Nodelist,Flags),
	(Type=integer -> integer(Num) ; true),   % check that Num is consistent with Type
	% L=<Num, Num=<H, assumes L < H
	cmpr(L,Num) + cmpr(Num,H) < 0, !,        % and in range (not NaN)
	(debugging(clpBNR,true) -> monitor_unify_(IntDef, Num) ; true),
	(var(Nodelist)
	 -> true                                 % nothing to do
	 ;  linkNodeList_(Nodelist, T/T, Agenda),
	    stable_(Agenda)                      % broadcast change
	).

attr_unify_hook(interval(Type1,V1,Nodelist1,Flags1), Int) :-   % unifying two intervals
	get_attr(Int, clpBNR, interval(Type2,V2,Nodelist2,Flags2)),  %%SWIP attribute def.
	^(V1,V2,R),                     % unified range is intersection (from ia_primitives),
	mergeValues_(Type1, Type2, NewType, R, NewR), !,
	mergeNodes_(Nodelist2,Nodelist1,Newlist),  % unified node list is a merge of two lists
	mergeFlags_(Flags1,Flags2,Flags),
	(debugging(clpBNR,true) -> monitor_unify_(interval(Type1,V1,_,Flags), Int) ; true),
	% update new type, value and constraint list, undone on backtracking
	put_attr(Int,clpBNR,interval(NewType,NewR,Newlist,Flags)),
	(var(Newlist)
	 -> true                                 % nothing to do
	 ;  linkNodeList_(Newlist, T/T, Agenda),
	    stable_(Agenda)                      % broadcast change
	).

attr_unify_hook(interval(Type,Val,Nodelist,Flags), V) :-   % new value out of range
	g_inc('clpBNR:evalNodeFail'),  % count of primitive call failures
	debugging(clpBNR, true),       % fail immediately unless debug=true
	debug_clpBNR_('Failed to unify ~w::(~w) with ~w',[Type,Val,V]),
	fail.

% awkward monitor case because original interval gone
monitor_unify_(IntDef, Update) :-  % debugging, manufacture temporary interval
	put_attr(Temp,clpBNR,IntDef),
	check_monitor_(Temp, Update, IntDef).

% if types identical, result type and bounds unchanged,
% else one is integer so result type integer, and integer bounds applied
mergeValues_(T, T, T, R, R) :- !.
mergeValues_(_, _, integer, (L,H), (IL,IH)) :-
	lower_bound_val_(integer,L,IL),     % type check bounds
	upper_bound_val_(integer,H,IH),
	non_empty(IL,IH).                   % still non-empty

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
	g_read('clpBNR:thread_init_done',_),      % ensures per-thread initialization
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

addConstraints_([],Agenda,Agenda) :- !.
addConstraints_([C|Cs],Agenda,NewAgenda) :-
	nonvar(C),
	addConstraints_(C,Agenda,NextAgenda), !,
	addConstraints_(Cs,NextAgenda,NewAgenda).
addConstraints_((C,Cs),Agenda,NewAgenda) :-  % Note: comma as operator
	nonvar(C),
	addConstraints_(C,Agenda,NextAgenda), !,
	addConstraints_(Cs,NextAgenda,NewAgenda).
addConstraints_(C,Agenda,NewAgenda) :-
	constraint_(C),    % a constraint is a boolean expression that evaluates to true
	simplify(C,CS),    % optional
	buildConstraint_(CS, Agenda, NewAgenda).

% low overhead version for internal use (also used by arithmetic_types pack)
constrain_(C) :- 
	buildConstraint_(C,T/T,Agenda),
	stable_(Agenda).
	
buildConstraint_(C,Agenda,NewAgenda) :-
	debug_clpBNR_('Add ~p',{C}),
	% need to catch errors from ground expression evaluation
	catch(build_(C, 1, boolean, Agenda, NewAgenda),_Err,fail), !.
buildConstraint_(C,Agenda,NewAgenda) :-
	debug_clpBNR_('{} failure due to bad or inconsistent constraint: ~p',{C}),
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
build_(Num, Int, VarType, Agenda, Agenda) :-            % floating point constant, may not be precise
	float(Num), !,
	(
	float_class(Num,infinite)
	 -> Int=Num                                         % infinities are point values
	 ;	int_decl_(VarType,(Num,Num),Int)                % may be fuzzed, so not a point
	).
build_(::(L,H), Int, VarType, Agenda, Agenda) :-        % hidden :: feature: interval bounds literal
	number(L), number(H), !,
	S is integer(sign(H-L)), 
	C is cmpr(L,H),  % compare bounds
	(C == 0
	 -> (rational(L) -> Int=L ; Int=H)                  % point value, if either bound rational (precise), use it
	 ;	C == -1,                                        % necessary condition: L < H
	    once(VarType == real ; true),                   % if undefined Type, use 'real'
	    put_attr(Int, clpBNR, interval(VarType, (L,H), _NL, []))  % create clpBNR attribute
	).
build_(Num, Int, VarType, Agenda, Agenda) :-            % pre-compile constants pi and e
	(Num == pi ; Num == e), !,
	int_decl_(VarType,(Num,Num),Int).  
build_(Exp, Num, VarType, Agenda, Agenda) :-            % pre-compile any ground precise Exp
	ground(Exp),
	safe_(Exp),                                         % safe to evaluate using is/2
	Num is Exp,
	% (Num == 1.5NaN -> !, fail ; preciseBnd(Num))      % fail build_ if nan
	preciseBnd(Num),                                    % precise result
	!.
build_(Exp, Z, _, Agenda, NewAgenda) :-                 % deconstruct to primitives
	Exp =.. [F|Args],
	fmap_(F,Op,[Z|Args],ArgsR,Types), !,                % supported arithmetic op
	build_args_(ArgsR,Objs,Types,Agenda,ObjAgenda),
	newNode_(Op,Objs,ObjAgenda,NewAgenda).
build_(Exp, Z, _, Agenda, NewAgenda) :-                 % user defined
	Exp =.. [F|Args],
	UsrHead =..[F,'$op',_,_,_],
	current_predicate(_,clpBNR:UsrHead),
	build_args_([Z|Args],Objs,Types,Agenda,ObjAgenda),
	newNode_(user(F),Objs,ObjAgenda,NewAgenda).

build_args_([],[],_,Agenda,Agenda).
build_args_([Arg|ArgsR],[Obj|Objs],[Type|Types],Agenda,NewAgenda) :-
	(var(Type) -> Type=real ; true),                    % var if user defined
	build_(Arg,Obj,Type,Agenda,NxtAgenda),
	build_args_(ArgsR,Objs,Types,NxtAgenda,NewAgenda).

% only called when argument is ground
safe_(E) :- atomic(E), !.  % all atomics, including [] - allows possibility of user defined arithmetic types
safe_([A|As]) :- !,
	safe_(A),
	safe_(As).
safe_(_ xor _) :- !,                                    % clpBNR xor incompatible with `is` xor
	fail.
safe_(integer(_)) :- !,                                 % clpBNR integer incompatible with `is` integer
	fail.
safe_(_/Z) :- 0.0 is abs(Z), !,                         % division by 0.0 (or -0.0) requires fuzzed 0.0
	fail.
safe_(F) :- 
	current_arithmetic_function(F),                     % evaluable by is/2
	F =.. [Op|Args],
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

fmap_(and,  and,   ZXY,     ZXY,     [boolean,boolean,boolean]).
fmap_(',',  and,   ZXY,     ZXY,     [boolean,boolean,boolean]).  % for usability
fmap_(or,   or,    ZXY,     ZXY,     [boolean,boolean,boolean]).
fmap_(nand, nand,  ZXY,     ZXY,     [boolean,boolean,boolean]).
fmap_(nor,  nor,   ZXY,     ZXY,     [boolean,boolean,boolean]).
fmap_(xor,  xor,   ZXY,     ZXY,     [boolean,boolean,boolean]).
fmap_(->,   imB,   ZXY,     ZXY,     [boolean,boolean,boolean]).

fmap_(sqrt, sqrt,  ZX,      ZX,      [real,real]).          % pos. root version vs. **(1/2)
fmap_(-,    minus, ZX,      ZX,      [real,real]).
fmap_(~,    not,   ZX,      ZX,      [boolean,boolean]).
fmap_(integer,int, ZX,      ZX,      [boolean,real]).
fmap_(exp,  exp,   ZX,      ZX,      [real,real]).
fmap_(log,  exp,   [Z,X],   [X,Z],   [real,real]).
fmap_(abs,  abs,   ZX,      ZX,      [real,real]).
fmap_(sin,  sin,   ZX,      ZX,      [real,real]).
fmap_(asin, sin,   [Z,X],   [X,Z],   [real,real]).
fmap_(cos,  cos,   ZX,      ZX,      [real,real]).
fmap_(acos, cos,   [Z,X],   [X,Z],   [real,real]).
fmap_(tan,  tan,   ZX,      ZX,      [real,real]).
fmap_(atan, tan,   [Z,X],   [X,Z],   [real,real]).

% reverse map node info to a facsimile of the original constraint
map_constraint_op_(integral,$(V),integral(V)) :- !.
map_constraint_op_(user(Func),Args,C) :- !,
	remap_(Func,Args,C).
map_constraint_op_(Op,Args,C) :-
	fmap_(COp,Op,_,_,_),
	remap_(COp,Args,C),
	!.

remap_(Op,$(Z,X,Y),C) :- constraint_(Op), Z==1, !,  % simplification for binary constraints
	C=..[Op,X,Y]. 
remap_(Op,$(Z,X),C) :- constraint_(Op), Z==1, !,    % simplification for unary constraints (~)
	C=..[Op,X].
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

% extend list with N
newmember([X|Xs],N) :- 
	(nonvar(X)
	 -> newmember(Xs,N) % not end of (indefinite) list.
     ;  X = N           % end of list, insert N and new tail Xs
    ).

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
	doNode_(Args, Op, P, OpsLeft, DoOver, Agenda/T, NxtAgenda),  % undoable on backtrack
	nb_setarg(3,Node,0),                    % reset linked bit
	% if doNode_ requested DoOver and above Ops threshold, put Node back at the end of the queue 
	(atom(DoOver), OpsLeft > 0 -> linkNode_(NxtAgenda,Node,NewAgenda) ; NewAgenda = NxtAgenda),
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
% doNode_/7 : Evaluate a node and add new nodes to end of queue. `evalNode` primitives can
%	 fail, resulting in eventual failure of `stable_`, i.e., inconsistent constraint set.
%
% Note: primitives operate on interval values (sets) only, unaware of common arguments,
% so additional consistency checks required on update.
%
doNode_($(ZArg,XArg,YArg), Op, P, OpsLeft, DoOver, Agenda, NewAgenda) :-  % Arity 3 Op
	(var(P)                                          % check persistent bit
	 -> getValue(ZArg,ZVal),
	    getValue(XArg,XVal),
	    getValue(YArg,YVal),
	    evalNode(Op, P, $(ZVal,XVal,YVal), $(NZVal,NXVal,NYVal)),  % can fail
	    % enforce consistency for common arguments by intersecting and redoing as required.
	    (var(ZArg)                % if Z == X and/or Y
	     -> (ZArg==XArg -> consistent_value_(NZVal,NXVal,NZ1,DoOver) ; NZ1 = NZVal),
	        (ZArg==YArg -> consistent_value_(NZ1,  NYVal,NZ2,DoOver) ; NZ2 = NZ1),
	        updateValue_(ZVal, NZ2, ZArg, OpsLeft, Agenda, AgendaZ)
	     ;  AgendaZ = Agenda
	    ),
	    (var(XArg), XArg==YArg    % if X==Y
	     -> consistent_value_(NXVal,NYVal,NVal,DoOver),
	        updateValue_(XVal, NVal,  XArg, OpsLeft, AgendaZ, NewAgenda)  % only one update needed
	     ;  updateValue_(XVal, NXVal, XArg, OpsLeft, AgendaZ, AgendaZX),
	        updateValue_(YVal, NYVal, YArg, OpsLeft, AgendaZX, NewAgenda)
	    )
	 ; % P = p, trim persistent nodes from all arguments
	    trim_op_(ZArg), trim_op_(XArg), trim_op_(YArg),  
	    NewAgenda = Agenda
	).

doNode_($(ZArg,XArg), Op, P, OpsLeft, DoOver, Agenda, NewAgenda) :-       % Arity 2 Op
	(var(P)                                          % check persistent bit
	 -> getValue(ZArg,ZVal),
	    getValue(XArg,XVal),
	    evalNode(Op, P, $(ZVal,XVal), $(NZVal,NXVal)),      % can fail
	    % enforce consistency for common arguments by intersecting and redoing as required.
	    (var(ZArg), ZArg==XArg    % if Z==X
	     -> consistent_value_(NZVal,NXVal,NVal,DoOver),     % consistent value, DoOver if needed
	        updateValue_(ZVal, NVal,  ZArg, OpsLeft, Agenda, NewAgenda)  % only one update needed
	     ;  updateValue_(ZVal, NZVal, ZArg, OpsLeft, Agenda, AgendaZ),
	        updateValue_(XVal, NXVal, XArg, OpsLeft, AgendaZ, NewAgenda)
	    )
	 ; % P = p, trim persistent nodes from all arguments
	    trim_op_(ZArg), trim_op_(XArg),
	    NewAgenda = Agenda
	).
 
doNode_($(Arg), Op, P, OpsLeft, _, Agenda, NewAgenda) :-                  % Arity 1 Op
	(var(P)                                          % check persistent bit
	 -> getValue(Arg,Val),
	    evalNode(Op, P, $(Val), $(NVal)),                   % can fail causing stable_ to fail => backtracking
	    updateValue_(Val, NVal, Arg, 1, Agenda,NewAgenda)   % always update value regardless of OpsLeft limiter	
	 ;  % P = p, trim persistent nodes from argument
	    trim_op_(Arg),
	    NewAgenda = Agenda
	).

consistent_value_(Val,Val,Val,_) :- !.                       % same value
consistent_value_(Val1,Val2,Val,true) :- ^(Val1,Val2,Val).   % different values, intersect

%
% remove any persistent nodes from Arg
%	called whenever a persistent node is encountered in FP iteration
%
trim_op_(Arg) :- 
	( get_attr(Arg, clpBNR, Def)     % an interval ?
	 -> arg(3,Def,NList),  %%Def = interval(_, _, NList, _),
		trim_persistent_(NList,TrimList),
		% if trimmed list empty, set to a new unshared var to avoid cycles(?) on backtracking
		(var(TrimList) -> setarg(3,Def,_) ; setarg(3,Def,TrimList))  % write trimmed node list
	 ; true  % assumed to be a number, nothing to trim
	).

trim_persistent_(T,T) :- var(T), !.    % end of indefinite node list
trim_persistent_([node(_,P,_,_)|Ns],TNs) :- nonvar(P), !, trim_persistent_(Ns,TNs).
trim_persistent_([N|Ns],[N|TNs]) :- trim_persistent_(Ns,TNs).

%
% Any changes in interval values should come through here.
% Note: This captures all updated state for undoing on backtracking
%
updateValue_(Old, Old, _, _, Agenda, Agenda) :- !.                  % no change in value (constant?)

updateValue_(Old, New, Int, OpsLeft, Agenda, NewAgenda) :-          % set interval value to New
	(OpsLeft>0 -> true ; propagate_if_(Old, New)), !,  % if OpsLeft >0 or narrowing sufficent
	putValue_(New, Int, Nodelist),               % update value (may fail)
	linkNodeList_(Nodelist, Agenda, NewAgenda).  % then propagate change

updateValue_(_, _, _, _, Agenda, Agenda).        % otherwise just continue with Agenda

% propgate if sufficient narrowing (> 10%)
propagate_if_((OL,OH), (NL,NH)) :- (NH-NL)/(OH-OL) < 0.9.  % any overflow in calculation will propagate

linkNodeList_(X, List, List) :- var(X), !.       % end of indefinite list? ...
linkNodeList_([X|Xs], List, NewList) :-
	(arg(3,X,Linked), Linked == 1                % test linked flag (only SWIP VM codes)
	 -> linkNodeList_(Xs, List, NewList)         % add rest of the node list
	 ;  linkNode_(List, X, NextList),            % not linked add it to list
	    linkNodeList_(Xs, NextList, NewList)     % add rest of the node list
	).

linkNode_(List/[X|NextTail], X, List/NextTail) :-  % add to list
	setarg(3,X,1).                               % set linked bit

:- include(clpBNR/ia_utilities).  % print,solve, etc.

%
% set monitor action on an interval using `watch` flags
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
	 -> once(monitor_action_(Action, Update, Int))
	 ; true
	).

%
% for monitoring changes - all actions defined here
%
monitor_action_(trace, Update, Int) :-  !, % log changes to console and enter debugger
	monitor_action_(log, Update, Int),
	trace.
monitor_action_(log, Update, Int) :-  var(Update), !,  % log interval unify
	debug_clpBNR_('Unify ~p with ~p',[Int,Update]).
monitor_action_(log, Update, Int) :-  number(Update), !,    % log interval unify with number
	domain(Int,Dom),
	debug_clpBNR_('Unify _?{~p} with ~p',[Dom,Update]).
monitor_action_(log, integer, Int) :-  !,  % change type to integer
	debug_clpBNR_('Set type of  ~p to ~p',[Int,integer]).
monitor_action_(log, Val, Int) :-  !,  % narrow range
	debug_clpBNR_('Set value of ~p to (~p)',[Int,Val]).
monitor_action_(_, _, _).  % default to noop (as in 'none')

%
% tracing doNode_ support - depends on SWI-Prolog hook prolog_trace_interception/4
%
trace_clpBNR(V) :-
	var(V), !,
	debugging(clpBNR(trace),V).
trace_clpBNR(true) :-
	debug(clpBNR(trace)),
	spy(clpBNR:doNode_).
trace_clpBNR(false) :-
	% only remove spy point if it was (possibly) set by trace_clpBNR
	(debugging(clpBNR(trace),true) -> nospy(clpBNR:doNode_) ; true),
	nodebug(clpBNR(trace)).

% prolog_trace_interception/4 is undefined by default, so need to do this now
:- dynamic user:prolog_trace_interception/4.
:- multifile user:prolog_trace_interception/4.

user:prolog_trace_interception(Port,Frame,_Choice,Action) :-
	debugging(clpBNR(trace),true),  % peg(trace) enabled?
	prolog_frame_attribute(Frame,goal,Goal),  % separate goal unification required?
	Goal = clpBNR:doNode_(Args, Op, _P, _, _, _, _),
	map_constraint_op_(Op,Args,C),
	clpBNR_trace_port(Port,C,Action),
	!.  % defensive, remove any CP's

clpBNR_trace_port(call,C,continue).  % ignore
clpBNR_trace_port(redo,C,continue).  % ignore (just used for trimming?)
clpBNR_trace_port(fail,C,fail) :-
	trace_clpBNR_("** fail ** ~p.",C).
clpBNR_trace_port(exit,C,continue) :-
	trace_clpBNR_("~p.",C).

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
	).

version_info :-
	print_message(informational, clpBNR(versionInfo)),
	print_message(informational, clpBNR(arithmeticFlags)).

set_min_free(Amount) :-
	once(prolog_stack_property(global,min_free(Free))), % minimum free cells (8 bytes/cell)
	(Free < Amount -> set_prolog_stack(global,min_free(Amount)) ; true).

:- multifile prolog:message//1.	

prolog:message(clpBNR(bounded)) -->
	[ 'clpBNR requires unbounded integers and rationals.'-[] ].

prolog:message(clpBNR(versionInfo)) -->
	{ version(Version) },
	[ '*** clpBNR v~w ***.'-[Version] ].

prolog:message(clpBNR(arithmeticFlags)) -->
	[ '  Arithmetic global flags set to prefer rationals and IEEE continuation values.'-[] ].

init_clpBNR :-
	version_info,
	check_features,
	set_min_free(8196),
	set_prolog_flags,     % initialize/check environment flags (can't rely on lazy init via `thread_init_done`)  
	clpStatistics,        % reset statistics
	trace_clpBNR(false).  % reset tracing on reload

:- initialization(init_clpBNR, now).

:- endif.

% remove possible temporary op definition
:- (current_op(1199,A,::) -> op(0,A,::) ; true).