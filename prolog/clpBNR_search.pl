/*	The MIT License (MIT)
 *
 *	Copyright (c) 2024-5 Rick Workman
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

/* adapted from ECLiPSe source file `generic_search.ecl` under 
 *    Mozilla Public License Version 1.1 (https://www.eclipseclp.org/license/)
 *
 *  Unsupported:
 *  Tree drawing via daVinci
 *  Hooks for user definintions
 *  Selection method `max_regret`
 *  Search methods based on ECLiPSe libraries `sbds` and GAP based `sbds` and `sbdd`
 *  `real`s are only searched using `split` and `indomain_split` using `splitsolve/1`
 *     but selection criteria (from a list) may use any "choice" or "search" methods
 *
 *  Adds `indomain_solve`/`solve`
 *
 *  Dependency: Uses `add_constraint/1` from v0.12.x
 *
 */

:- module(clpBNR_search,[   %  exports:
	 search/6,       % backtracking search for solutions on list of vars or like-terms
	 delete/5,
	 indomain/2
	]).

/** <module> clpBNR_search: Support for alternative search strategies based on ECLiPSe family of search libraries
This module is intended to be the equivalent of ECLiPSe's [fd_search](https://eclipseclp.org/doc/bips/lib/fd_search/search-6.html) library but extended to support `real` domains. (See the predicate documentation for details.) Support for drawing search trees, user defined extensions, and the SBDS library in `fd_search` has not been implemented in `clpBNR_search`. 
*/

:- use_module(library(lists),[flatten/2]).          % for flattening search input lists
:- use_module(library(option),[option/3]).          % for option list processing
:- use_module(library(clpBNR)).

% sandboxing for SWISH
:- multifile(sandbox:safe_global_variable/1).
:- multifile(sandbox:safe_primitive/1).

:- set_prolog_flag(optimise,true).                  % scoped to file/module

%
% clpBNR access support
%
get_size(X,0) :- number(X), !.  % constants have size 0
get_size(X,Size) :- 
	domain(X,integer(Min,Max)) -> Size is Max-Min+1; delta(X,Size).

get_lwb(X,LB) :-
	get_bounds(X,LB,_).

get_upb(X,UB) :-
	get_bounds(X,_,UB).

get_bounds(X,Min,Max) :-
	range(X,[Min,Max]).

%
% Minimal support for global var equivalent of ECLiPSe shelf create/destroy
% Global vars are created on global stack so will be garbage collected on success
%
shelf_create(Shelf,Value) :-
	gensym('$clpBNR_shelf_handle',Shelf),                % new shelf handle
	(nb_linkval(Shelf,Value) ; nb_delete(Shelf), fail).  % delete on backtracking
%   declare safe (non-ground global names)
sandbox:safe_primitive(clpBNR_search:shelf_create(_Shelf,_Value)). 

/**
search(+Vars:list,+Arg:integer,+Select:atom,+Choice:atom,+Method:atom,Options:list) is nondet

Succeeds if a solution can be found for the list of Vars (numbers, constrained vars or terms containing such vars) given the search strategy specified by Method, Select, and Choice; fails otherwise. On backtracking, alternative solutions are generated. Method and Select apply uniformly to intervals of either type (`real` or `integer`. The semantics of Choice may depend on type (see below).

If a Vars list element cannot be reduced to an interval (see Arg below), it is just ignored. This means, given suitable values for the other arguments, search/6 will succeed unless no solution can be found. In addition, for continuous domains, this may result in solutions in which it can't be conclusively proven that they contain no solutions with narrower domains, due to narrowing or precision restrictions. (This may also apply to finite domains if the search Method is not `complete`.) 

If Arg has a value `N` greater than 0, the 'N`th  argument of elements in the Vars list will be subjects for the search; if 0 the element itself (must be an interval) is used.

Supported Method's include:
* `complete`: a complete search routine which explores all alternative choices.
* `bbs(Steps)`: a bounded backtracking search allowing Steps backtracking steps.
* `lds(Disc)`: a form of the limited discrepancy search . This method iteratively tries 0, 1, 2 .. Disc changes against the heuristic (first) value. Typical values are between 1 and 3 (which already may create too many alternatives for large problems).
* `dbs(Level, Method)`: a depth bounded search which explores the first Level choices (must be positive integer) in the search tree completely, i.e. it tries all values for the first Level selected variables. After that, it switches to search Method, which can be `bbs(Steps)`, `lds(Disc)` or a integer specify the number of steps to be used in a `bbs` search.
* `credit(Credit,Method)`: a credit based search that explores the top of the search tree completely. Credit (a positive integer) specifies the initial number of credits.  At each choice point, the first alternative gets half of the available credit, the second alternative half of the remaining credit, and so on. When the credit run out, the system switches to another search routine specified by Method; supported methods are the same as the `dbs` method. Typical values for Credit are either N or N*N, where N is the number of entries in the collection.

The Select argument determines the order in which the elements of Vars are selected. After one is selected and narrowed, the same criteria then is used on the remaining elements. Supported values are:
* `input_order`: select the first entry in the list.
* `first_fail`: select the entry with the smallest domain size (see below).
* `anti_first_fail`: select the entry with the largest domain size (see below).
* `smallest`: select the entry with the smallest lower bound.
* `largest`: select the entry with the largest upper bound.
* `occurrence`: select the entry with the largest number of attached constraints.
* `most_constrained`: select the entry with the smallest domain size. If several entries have the same domain size, select the entry with the largest number of attached constraints.

The "size" of an `integer` interval is the number of possible values in the domain (upper bound - lower bound +1). The size of a `real is the width of the interval (upper bound - lower bound).

The Choice argument determines how the selected interval is enumerated/split and the semantics depends on the domain type. The choice names are mapped to indomain/2 heuristics as follows:

|	`Choice`				|`indomin/2` Heuristic	|
|	`indomain`				|	`enum` 				|
|	`indomain_min`			|	`min`				|
|	`indomain_max`			|	`max`				|
|	`outdomain_reverse_min`	|	`reverse_min`		|
|	`outdomain_reverse_max`	|	`reverse_max`		|
|	`indomain_reverse_min`	|	`reverse_min`		|
|	`indomain_reverse_max`	|	`reverse_max`		|
|	`indomain_middle`		|	`middle` 			|
|	`indomain_median`		|	`median` 			|
|	`indomain_split`		|	`split`				|
|	`indomain_reverse_split`|	`reverse_split`		|
|	`indomain_solve`		|	`solve`				|
|	`indomain_random`		|	`random`			|
|	`indomain_interval`		|	`interval`			|

Note that many of the enumerating Choice's have no effect on `real` intervals. This can be helpful when searching a list of mixed `integer` and `real` domains. The effective options for `real` domains are `indomain_middle`, `indomain_median`, `indomain_split`, `indomain_reverse_split`, `indomain_solve`, `indomain_random` and `indomain_interval`. (`indomain_split`, `indomain_reverse_split` and `indomain_interval` are of questionable value for `real domains.)

Options is a list of 0 or more options including:
* `backtrack(-N)` unifies N with the number of backtracking steps used in the search
* `nodes(+N)` sets an upper limit (default 2000) on the number of nodes explored in the search. If the given limit is exceeded, the search routine stops the exploration of the search tree.
*/

search(Vars,Arg,Select,Choice,Method,Option) :-
	flatten(Vars, List),  % flat list of Vars/Terms
	integer(Arg),
	callable(Select),
	callable(Choice),
	is_search_method(Method),
	is_list(Option),
	!,
	reset_backtrack_count(Option),
	% top-level block to handle the limited number of nodes
	catch(search1(Method,List,Arg,Select,Choice),
	      error(domain_error(nodes,(N,Max)),_),
	      fail_error_message(clpBNR(search_nodes_failed(N,Max)))
	     ),  %%search_nodes_failed(N,Max)),
	get_backtrack_count(Option).
search(Vars,Arg,Select,Choice,Method,Option) :-
	fail_error_message(clpBNR(search((Vars,Arg,Select,Choice,Method,Option)))).

fail_error_message(Msg) :-
	print_message(error,Msg),
	fail.

:- multifile prolog:message//1.

prolog:message(clpBNR(search(Args))) -->
	[ "Invalid argument: search(~w).\n"-[Args] ].

prolog:message(clpBNR(search_nodes_failed(N,Max))) -->
	[ "Node count = ~w, excceeded limit of ~w\n"-[N,Max] ].


% branch one the different search methods
search1(complete,L,Arg,Select,Choice):-
	labeling(L,Arg,Select,Choice).
search1(bbs(Steps),L,Arg,Select,Choice):-
	bbs(L,Arg,Select,Choice,Steps).
search1(credit(Credit,Steps),L,Arg,Select,Choice):-
	credit(L,Arg,Select,Choice,Credit,Steps).
search1(lds(Disc),L,Arg,Select,Choice):-
	lds(L,Arg,Select,Choice,Disc).
search1(dbs(Level,Steps),L,Arg,Select,Choice):-
	dbs(Level,Steps,L,Arg,Select,Choice).

is_search_method(complete) :- !.
is_search_method(bbs(N)) :- integer(N), !.
is_search_method(credit(N,M)) :- integer(N), integer(M), !.
is_search_method(credit(N,bbs(M))) :- integer(N), integer(M), !.
is_search_method(credit(N,lds(M))) :- integer(N), integer(M), !.
is_search_method(lds(N)) :- integer(N), !.
is_search_method(dbs(N,M)) :- integer(N), integer(M), !.
is_search_method(dbs(N,bbs(M))) :- integer(N), integer(M), !.
is_search_method(dbs(N,lds(M))) :- integer(N), integer(M), !.

%
%  different search methods
%

% labeling(+List:list,
%           ++Arg:integer,
%	   ++Select:atom,
%	   +Choice:atom)
%
labeling(Xs,Arg,Select,Choice):-
	(delete(X,Xs,R,Arg,Select)
	 -> choose(X,Arg,Choice),
	    inc_backtrack_count,  % for reporting in backtrack option
	    labeling(R,Arg,Select,Choice)
	 ;  true
	).


% bbs(+List:list,
%        ++Arg:integer,
%	++Select:atom,
%	+Choice:atom,
%	++Steps:integer)
% same as labeling, but stops after Steps backtracking steps
%
bbs(L,Arg,Select,Choice,Steps):-
	b_getval('$clpBNR_search:backtrack', CurrentBacktracks),
	BacktrackLimit is CurrentBacktracks+Steps,
	nb_setval('$clpBNR_search:backtrack_limit',BacktrackLimit),
	catch(bbs1(L,Arg,Select,Choice),error(domain_error(backtracks,_),_),fail).

bbs1(Xs,Arg,Select,Choice):-
	(delete(X,Xs,R,Arg,Select)
	 -> choose(X,Arg,Choice),
	    inc_backtrack_count_check,
	    bbs1(R,Arg,Select,Choice)
	 ;  true
	).


% credit(+List:list,++Arg:integer,++Select:atom,+Choice:atom or p/2,
%	 ++Credit:integer,
%	 ++Extra:integer or bbs(integer) or lds(integer))
% same as labeling, but uses credit to control search
% always give half the credit to the first child,
% half of the remaining credit to the next child, etc

credit([],_Arg,_Select,_Choice,_Credit,_Extra) :- !.
credit(L,Arg,Select,Choice,Credit,Extra):-  %	L = [_|_],
	credit1(Credit,Extra,L,Arg,Select,Choice).

credit1(1,bbs(Extra),Xs,Arg,Select,Choice):-
	!,
	bbs(Xs,Arg,Select,Choice,Extra).
credit1(1,lds(Extra),Xs,Arg,Select,Choice):-
	!,
	lds(Xs,Arg,Select,Choice,Extra).
credit1(1,Extra,Xs,Arg,Select,Choice):-
	integer(Extra),
	!,
	bbs(Xs,Arg,Select,Choice,Extra).
credit1(Credit,Extra,Xs,Arg,Select,Choice):-
	Credit > 1,
	(delete(X,Xs,R,Arg,Select)
	 -> shelf_create(Shelf,Credit),  % on backtracking, shelf destroyed
	    credit_choice(X,Arg,Choice,Shelf,Credit_child),
	    credit1(Credit_child,Extra,R,Arg,Select,Choice)
	 ;  true
	).

credit_choice(X,Arg,Choice,Shelf,Credit_child) :-
	    choose(X,Arg,Choice),
	    inc_backtrack_count,
	    distribute_credit(Shelf,Credit_child,Rest),
	    (Rest == 0 -> !  % no more credit, cut away remaining choices in choose
	     ; true
	    ).

% the credit distribution
% always give (a bit more than) half the credit to the next child
% keep the rest of the credit for the other children
% do not use up credit yourself
% if credit remains, and there are no more children, the credit is lost
% if children do not use their credit, it is lost
distribute_credit(Shelf,Credit,Rest):-
	b_getval(Shelf,Old),
	Credit is (Old+1)//2,
	Rest is Old-Credit,
	nb_linkval(Shelf,Rest).
%   declare safe (non-ground global names)
sandbox:safe_primitive(clpBNR_search:distribute_credit(_Shelf,_Credit,_Rest)). 


% lds(+List:list,++Arg:integer,++Select:atom,++Choice:atom,++LDS:integer)
% same as labeling, but only allows max LDS discrepancies against heuristic
% solution
% first tries 0, then 1, then 2, up to LDS discrepancies
%
lds(L,Arg,Select,Choice,Lds):-
	between(0,Lds,Disc),  % between(0,Lds,1,Disc),
	lds1(L,Arg,Select,Choice,Disc).

lds1(Xs,Arg,Select,Choice,Disc):-
	(delete(X,Xs,R,Arg,Select)
	 -> (Disc==0
		 -> once(choose(X,Arg,Choice)), % allows only shallow backtracking
		    update_nodes_counter, % create new node name
		    lds1(R,Arg,Select,Choice,0)
	     ;  shelf_create(Shelf,Disc),	% Disc >= 1
	     	lds_choice(X,Arg,Choice,Shelf,Disc1),
		    lds1(R,Arg,Select,Choice,Disc1)
	    )
	 ;  Disc == 0  % do not allow to use less than given discrepancies
	).

lds_choice(X,Arg,Choice,Shelf,Disc) :-
	choose(X,Arg,Choice),
	inc_backtrack_count,
	(dec_discrepancy(Shelf,Disc) -> true
	 ;  !,  % cut away remaining choices in choose
		Disc = 0
	).

dec_discrepancy(Shelf,Disc):-
	b_getval(Shelf,Disc),
	Disc > 0,	% fail if already 0
	Disc1 is Disc - 1,
	nb_linkval(Shelf,Disc1).
%   declare safe (non-ground global names)
sandbox:safe_primitive(clpBNR_search:dec_discrepancy(_Shelf,_Disc)). 


% dbs(++Level:integer,
%	  ++Extra:integer or bbs(integer) or lds(integer),
%	  +List:list,++Arg:integer,++Select:atom,+Choice:atom)
%	 
% same as labeling, but uses depth bounded search to control search
% explore all choice points in the first Level variables
dbs(0,bbs(Extra),Xs,Arg,Select,Choice):-
	!,
	bbs(Xs,Arg,Select,Choice,Extra).
dbs(0,lds(Extra),Xs,Arg,Select,Choice):-
	!,
	lds(Xs,Arg,Select,Choice,Extra).
dbs(0,Extra,Xs,Arg,Select,Choice):-
	integer(Extra),
	!,
	bbs(Xs,Arg,Select,Choice,Extra).
dbs(Level,Extra,Xs,Arg,Select,Choice):-
	Level >= 1,
	(delete(X,Xs,R,Arg,Select)
	 -> choose(X,Arg,Choice),
	    inc_backtrack_count,
	    Level1 is Level-1,
	    dbs(Level1,Extra,R,Arg,Select,Choice)
	 ;  true
	).


% choose(?X,++Arg:integer,++Choice:atom)
% this predicate chooses a value for the selected term
% this choice is non-deterministic
choose(X,N,Choice):-
	translate_indomain_atom(Choice, Method),
	!,  % green cut??
	access(X,N,Var),
	indomain(Var,Method).

% Translate search/6's indomain choice atoms to those used by indomain/2
%% no sbds or gap_* searches supported
translate_indomain_atom(indomain, enum).
translate_indomain_atom(indomain_min, min).
translate_indomain_atom(indomain_max, max).
translate_indomain_atom(outdomain_min, reverse_min).	% Zinc
translate_indomain_atom(outdomain_max, reverse_max).	% Zinc
translate_indomain_atom(indomain_reverse_min, reverse_min).
translate_indomain_atom(indomain_reverse_max, reverse_max).
translate_indomain_atom(indomain_middle, middle).
translate_indomain_atom(indomain_median, median).
translate_indomain_atom(indomain_split, split).
translate_indomain_atom(indomain_solve, solve).
translate_indomain_atom(indomain_reverse_split, reverse_split).
translate_indomain_atom(indomain_interval, interval).
translate_indomain_atom(indomain_random, random).


% access argument N of term X, if N=0, X is returned
access(X,0,X) :- !.          % most common case?
access(X,_,X) :- var(X), !.  % var = value 
access(X,N,Var):-
	N > 0,
	arg(N,X,Var).


%
% Backtracks and Nodes support
%
sandbox:safe_global_variable('$clpBNR_search:node_limit').
sandbox:safe_global_variable('$clpBNR_search:nodes').
sandbox:safe_global_variable('$clpBNR_search:backtrack').
sandbox:safe_global_variable('$clpBNR_search:one_level').
sandbox:safe_global_variable('$clpBNR_search:backtrack_limit').

reset_backtrack_count(Option):-
	option(nodes(N),Option,2000),
	nb_setval('$clpBNR_search:node_limit',N),
	nb_setval('$clpBNR_search:nodes',0),
	nb_setval('$clpBNR_search:backtrack',0).

get_backtrack_count(L):-
	option(backtrack(N),L,_),  % unifies var in option with backtack count
	b_getval('$clpBNR_search:backtrack',N).

inc_backtrack_count:-
	update_nodes_counter,
	nb_setval('$clpBNR_search:one_level',true).
inc_backtrack_count:-
	update_backtrack_count(_),
	fail.

inc_backtrack_count_check :-  % only called by `bbs1`
	update_nodes_counter,
	nb_setval('$clpBNR_search:one_level',true).
inc_backtrack_count_check :-
	update_backtrack_count(N1),
	b_getval('$clpBNR_search:backtrack_limit',L),  % initialized by `bbs` Method
	N1 > L,
	domain_error(backtracks,N1). %exit_block(bbs)

update_backtrack_count(N1) :-
	b_getval('$clpBNR_search:one_level',true),
	nb_setval('$clpBNR_search:one_level',false),
	b_getval('$clpBNR_search:backtrack',N), N1 is N+1, nb_linkval('$clpBNR_search:backtrack',N1).

update_nodes_counter:-
	nb_getval('$clpBNR_search:nodes',N), N1 is N+1, nb_linkval('$clpBNR_search:nodes',N1),
	b_getval('$clpBNR_search:node_limit', Max),
	(N1 >= Max
	 -> domain_error(nodes,(N1,Max)) %exit_block(nodes)
	 ;  true
	).

/**
delete(?X:numeric,+Terms:list,?Rest:list,+Arg:integer,+Select:atom) is semidet

Succeeds if X can be unified with an numeric element (number or interval) selected from the Terms list according to Select; the rest of the list is unified with Rest (includes any non-numeric). Fails if there are no numeric values in Terms or if an invalid Select method is specified. Terms may include numbers, `clpBNR` domain variables, or terms whose Arg argument is a number or domain variable. (Arg = 0 implies use of `Vars` element itself.)

Valid values of Select are documented in search/6.

*/
% delete(-X,+List:non_empty_list,-R:list,++Arg:integer,++Select:atom)
% choose one entry in the list based on a heuristic; this is a deterministic selection
% a special case for input_order to speed up the selection in that case
% Note clpBNR integer and real
delete(X,Terms,Rest,Arg,Select) :- 
	delete1(Select,X,Terms,Rest,Arg).       % reorder arguments

delete1(input_order,X,List,Rest,Arg) :- !,  % select in list order
	List = [Term|Terms],
	(delete_valid(Arg,Term)
	 -> X = Term,
	    Rest = Terms
	 ;  delete1(input_order,X,Terms,Tail,Arg),
	    Rest = [Term|Tail]
	).
delete1(Select,X,List,Rest,Arg) :-          % select based on criterion
	(memberchk(Select,                      % rest of supported values ...
[first_fail, anti_first_fail, smallest, largest, occurrence, most_constrained]
	          )
	 -> NaN is nan,
	    (Select == most_constrained -> Crit = crit(NaN,NaN) ; Crit = NaN),
	    find_best_and_rest(List,Crit,_,X,Rest/Rest,Arg,Select),  % scan for best           
	    delete_valid(Arg,X)                 % ensure numeric
	 ;  fail_error_message(clpBNR(delete_method(Select)))  
	).                     

prolog:message(clpBNR(delete_method(Select))) -->
	[ "Invalid Select method: ~w .\n"-[Select] ].

delete_valid(0,X) :- !,
	(number(X) -> true ; interval(X)).
delete_valid(Arg,X) :- 
	compound(X), 
	Arg > 0, 
	arg(Arg,X,Val),
	delete_valid(0,Val).

find_best_and_rest([], _CritOld, BestTerm, BestTerm, _Rest/[], _Arg, _Select) :- !.
find_best_and_rest([Term|Terms], CritOld, BestTerm, X, Rest/Tail, Arg, Select) :-
	access(Term,Arg,Var), access(BestTerm,Arg,BestVal),
	(number(Var)                        % pick constants and stop
	 -> X = Term, 
	    (interval(BestVal) -> Tail = [BestTerm|Terms] ; Tail = Terms)
	 ;  find_value(Select,Var,CritNew),
	    (better_item(CritNew,CritOld) 	% better than the old one ?
	     -> (interval(BestVal) -> Tail = [BestTerm|NxtTail] ; NxtTail = Tail),  % put interval(Best) in Rest
	        find_best_and_rest(Terms, CritNew, Term, X, Rest/NxtTail, Arg, Select)
	     ;  Tail = [Term|NxtTail],      % put Term in Rest
	        find_best_and_rest(Terms, CritOld, BestTerm, X, Rest/NxtTail, Arg, Select)
	    )
	).

better_item(crit(SizeNew,NumberNew),crit(SizeOld,NumberOld)) :-  % most_constrained
	(better_item(SizeNew,SizeOld)
	 -> true
	 ;  better_item(NumberNew,NumberOld)
	).
better_item(CritNew,CritOld) :- number(CritNew), number(CritOld),
	(CritNew is nan
	 -> fail                                          % nan is never better
	 ; (CritOld is nan
	    -> true                                       % non-nan is better than nan
	    ;  CritNew < CritOld)                         % othewise less is better 
	).

% find_value(++Select:atom,?X:dvarint,
%	     -Crit:number or crit(number,number))
%
% Find a heuristic value from a domain variable: the smaller, the better.
% Values will be compared using @<, so be aware of standard term ordering!
% If the Criterion remains uninstantiated, this indicates an optimal value,
% which will be picked without looking any further down the list.
% Note: should work for clpBNR integer and real intervals
find_value(first_fail,X,Size) :-
	get_size(X,Size), !.
find_value(anti_first_fail,X,Number) :- !,
	get_size(X,Size), !,		    % can be 1.0Inf
	Number is -Size.				% -1.0Inf @< -99
find_value(smallest,X,Min) :-
	get_lwb(X,Min), !.
find_value(largest,X,Number) :-
	get_upb(X,Max), !,
	Number is -Max.
find_value(occurrence,X,Number) :-
	interval_degree(X,Nr), !,       % constants have degree 0, cheap op for clpBNR)
	Number is -Nr.
find_value(most_constrained,X,crit(Size,Number)) :-
	find_value(first_fail,X,Size),
	find_value(occurrence,X,Number),
	!.
find_value(_Select,_X,Crit) :-
	Crit is nan.      % invalid X, Crit = nan


/**
indomain(?X:numeric,+Choice:atom) is semidet

Succeeds if X (`number` or interval) can be narrowed or instantiated according to the heuristic specified by Choice, subject to any constraints. On backtracking alternative values are generated. Fails if the first argument is non-numeric, the heuristic is not supported, or no values can be found subject by the heuristic subject to current constraints.

For `integer` domains, indomain/2 will generate `integer` values from the domain in an order defined by the heuristic; for `real` domains, sub-domains will be generated by splitting at a point defined by the heuristic. In the latter case, the predicate may succeed without splitting, e.g., some heuristics may choose not to split on a point solution (`middle`, `solve`, ..).

Supported values for Choice include:
* `enum`: For `integer` domains, start enumeration from the smallest value upwards. `real` domains cannot be enumerated so the interval is unchanged.
* `min`: For `integer` domains, start enumeration from the smallest value upwards. On backtracking the domain is constrained to not contain the value. `real` domains cannot be enumerated so the domain is unchanged.
* `max`: For `integer` domains, start the enumeration from the largest value downwards. On backtracking the domain is constrained to not contain the value. `real` domains cannot be enumerated so the domain is unchanged.
* `reverse_min`: For `integer` domains, the domain is constrained to not contain the smallest value. On backtracking, the interval is unified with that value, i.e., values are excluded first, then assigned. Point values cannot be excluded from real domains (`<`, `>` and `<>` are unsound on continuous domains) so the domain is unchanged.
* `reverse_max`: For `integer` domains, the domain is constrained to not contain the largest value. On backtracking, the interval is unified with that value, i.e., values are excluded first, then assigned. See `reverse_min` for `real` domains.
* `middle`: For `integer` domains, start the enumeration from the integer closest (rounded down) to the midpoint of the domain. On backtracking, this chooses alternatively values above and below the midpoint, until all alternatives have been tested. For `real` domains, `middle` is the same as `split`.
* `median`: For `integer` domains, this is equivalent to `middle` (`clpBNR` domains are compact). For `real` domains, this is equivalent to `middle` except the median value of the domain is used. 
* `split`: For `integer` domains, enumerate by splitting the domain successively into halves until a ground value is reached. For `real` domains, successively split the domain into sub-domains, favouring the lower half, until the clpBNR precision limit is reached (see small/1). (`split` is equivalent to splitsolve/1 on a single interval.)
* `reverse_split`: Like `split`, but tries the upper half of the domain first.
* `solve`: Uses `clpBNR:solve` to enumerate/narrow `integer` and `real` domains.
* `interval`: Same as `split` (retained for `fd_search` compatibility).
* `random`: For `integer` domains, enumerate in a random order. On backtracking, the previously tested value is removed. (This method uses random/1 to create random numbers, use seed/1 before to make results reproducible.) For `real` domains recursively split on a random point in the domain that isn't a solution until the clpBNR precision limit is reached (see small/1), favouring the lowering sub-domain on each split. On backtracking, alternatives using the upper domain sub-domain are generated. If a random split point which is not a solution cannot be found within a small number of attempts, splitting stops (like solve/1).
* `Value:number`: For `integer` domains, like `middle`, but start with the given `Value` which must be an integer. For `real` domains, split the domain at `Value` (must be in the domain) if it is not a solution generating the lower sub-interval. On backtracking the higher sub-interval is generated. If `Value` is a solution, the interval is not split. (Unlike many other heuristics, this is not recursively  applied.)
*/

% indomain(?X:dvarint,++Method:atomic)
% IndomainType is either one of min, max, middle or an integer
% these indomain versions remove the previous value on backtracking
% Note: only assigns values to finite domain (i.e., clpBNR integer) variables
indomain(X,Method):-
	domain_type(X,Type) -> indomain1(Method,X,Type) ; number(X).

domain_type(X,Type)    :- 
	domain(X,D),          % fails if not an interval
	functor(D,Type,2).    % D=Type(_,_).
	
indomain1(enum,X,Type) :- !,
	indomain_enum(Type,X).
indomain1(min,X,Type) :- !,
	get_lwb(X,Min),
	indomain_min(Type,X,Min).
indomain1(max,X,Type):- !,
	get_upb(X,Max),
	indomain_max(Type,X,Max).
indomain1(reverse_min,X,Type) :- !,
	get_lwb(X,Min),
	outdomain_min(Type,X,Min).
indomain1(reverse_max,X,Type) :- !,
	get_upb(X,Max),
	outdomain_max(Type,X,Max).
indomain1(middle,X,Type) :- !,
	indomain_middle(Type,X).
indomain1(median,X,Type) :- !,
	indomain_median(Type,X).
indomain1(split,X,Type) :- !,
	indomain_split(Type,X).
indomain1(reverse_split,X,Type) :- !,
	indomain_reverse_split(Type,X).
indomain1(solve,X,_Type) :- !,
	solve(X).
indomain1(interval,X,Type) :- !,    % clpBNR intervals are compact (no gaps), so use split
	indomain_split(Type,X).
indomain1(random,X,Type) :- !,
	indomain_random(Type,X).
indomain1(Value,X,integer):- !,
	integer(Value),
	get_bounds(X,Min,Max),
	( Value =< Min ->
	    % if the starting value is too small, use indomain_min
	    indomain_min(integer,X,Min)
	; Value >= Max ->
	    % if the starting value is too large, use indomain_max
	    indomain_max(integer,X,Max)
	;   % enumerate from a starting value inside the domain
	    % From fd_search: is this enough in all cases ??
	    Range is 2*max(Max-Value,Value-Min)+1,
	    indomain_from(X,Value,1,Range)
	).
indomain1(Value,X,real):-
	number(Value),
	get_bounds(X,Min,Max),
	( (Min >= Value ; Value >=Max)
	 -> fail   % Value not in domain, cannot do anything
	 ;   % if Value is not a solution split the domain if not a solution
	    (\+(X=Value)
	     -> (add_constraint(X =< Value) ; add_constraint(Value =< X))
	     ;  true        % Value is in domain, can't split real on this value
	    )
	).

indomain_enum(integer,X) :-
	enumerate(X).	
indomain_enum(real,_X).  % enumeration of real - succeed with no narrowing or choicepoint

% indomain_min(?X:dvar, ++Value:integer)
% the choice consists in either taking the proposed value or in excluding it
% and choosing another one
indomain_min(integer,X,X).
indomain_min(integer,X,Min):-  % if integer, can remove current lb
	add_constraint(X > Min),
	get_lwb(X,New),
	indomain_min(integer,X,New).
indomain_min(real,_X,_Min).     % if real, can't narrow further

outdomain_min(integer,X,Min):-
	add_constraint(X > Min),
	get_lwb(X,New),
	outdomain_min(integer,X,New).
outdomain_min(integer,X,X).
outdomain_min(real,_X,_Min).

% indomain_max(?X:dvar, ++Value:integer)
% the choice consists in either taking the proposed value or in excluding it
% and choosing another one
indomain_max(integer,X,X).
indomain_max(integer,X,Max):- % if integer, can remove current ub
	add_constraint(X < Max),
	get_upb(X,New),
	indomain_max(integer,X,New).
indomain_max(real,_X,_Max).     % if real, can't narrow further

outdomain_max(integer,X,Max):-
	add_constraint(X < Max),
	get_upb(X,New),
	outdomain_max(integer,X,New).
outdomain_max(integer,X,X).
outdomain_max(real,_X,_Max).

indomain_middle(integer,X) :-
	get_bounds(X,Min,Max),
	Value is (Min+Max)//2,    % default rounds toward 0, different from split	
	indomain1(Value,X,integer).  % alternating around value
indomain_middle(real,X) :-    % same as splitsolve on single var
	(small(X) 
	 -> true                  % small, don't split further
	 ;  midpoint(X,Middle),   % split at midpoint
	    ( add_constraint(X =< Middle) ; add_constraint(Middle =< X) ),
	    indomain_middle(real,X)
	).

indomain_median(integer,X) :- % same as middle for integers (intervals are compact)
	indomain_middle(integer,X).
indomain_median(real,X) :-
	(small(X) 
	 -> true                  % small, don't split further
	 ;  median(X,Median),     % split at median
	    (add_constraint(X =< Median) ; add_constraint(Median =< X) ),
	    indomain_median(real,X)
	).

% split the domain until only an integer value is left or real interval sufficiently narrow
indomain_split(_Type,X):-
	number(X),
	!.
indomain_split(integer,X):-
	get_bounds(X,Min,Max),
	Middle is (Min+Max) div 2,  % Note rounds toward -inf, different definition of middle 
	( add_constraint(X =< Middle) ; add_constraint(Middle < X) ),
	indomain_split(integer,X).
indomain_split(real,X):- 
	indomain_middle(real,X).

indomain_reverse_split(integer,X):-
	integer(X),
	!.
indomain_reverse_split(integer,X):-
	get_bounds(X,Min,Max),
	Middle is (Min+Max) div 2,    % Note rounds toward -inf, different definition of middle 
	( add_constraint(X > Middle) ; add_constraint(Middle >= X) ),
	indomain_reverse_split(integer,X).
indomain_reverse_split(real,X):-
	(small(X) 
	 -> true  % don't split further
	 ;  midpoint(X,Middle),
	    ( add_constraint(X >= Middle) ; add_constraint(Middle >= X) ),
	    indomain_reverse_split(real,X)
	).

% choose values from the domain at random; on backtracking, the previous value
% is removed, so that it can be used for a complete enumeration
indomain_random(Type,X):-
	random_value(Type,X,Try),	
	indomain_random(Type,X,Try).

random_value(integer,X,Try) :-
	get_bounds(X,Min,Max),
	Try is Min+random(Max-Min+1).      % random:random_between/3
random_value(real,X,Try) :-
	get_bounds(X,Min,Max),
	Try is Min+random_float*(Max-Min).

indomain_random(integer,X,X).
indomain_random(integer,X,Try):-
	add_constraint(X <> Try),
	indomain_random(integer,X).
indomain_random(real,X,Try) :-
	split_random(10,X,Try).           % try up to 10 random values for non-solution

split_random(0,_X,_Try) :- !.         % stop, failed to find splittable point
split_random(_Ct,X,_Try) :-
	small(X), !.                      % stop, too small to split  
split_random(Ct,X,Try) :-
	(\+(X = Try)                      % split on non-solution 
	 -> ( add_constraint(X =< Try) ; add_constraint(Try =< X) ),
	    indomain_random(real,X)       % rinse and repeat
	 ;  random_value(real,X,NxtTry),  % can't split on this Value, try another 
	 	NxtCt is Ct-1,                % decrement Ct
	 	split_random(NxtCt,X,NxtTry)  % rinse and repeat
	).

% indomain_from(?X:dvar, ++Value:integer, ++Inc:integer, ++Range:integer)
% the choice consists in either taking the proposed value or in excluding it
% and choosing another one
% the next value is always the old value plus the increment
% the next increment is one bigger than the previous, but of opposite sign
% 1, -2, 3, -4, 5, -6, 7 ...
% if the increment becomes too large, you can stop
indomain_from(X,X,_,_).
indomain_from(X,Value,Inc,Range):-
	add_constraint(X <> Value),
	Value1 is Value+Inc,
	Inc1 is -sign(Inc)*(abs(Inc)+1),  % sgn
	Range >= abs(Inc1),
	indomain_from(X,Value1,Inc1,Range).
