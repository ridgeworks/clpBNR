# CLP(BNR)
This repository is a re-implementation of CLP(BNR) in Prolog and packaged as an SWI-Prolog module. The original implementation was a component of BNR Prolog (.ca 1988-1996) on Apple Macintosh and Unix. (For a source archive of the last release of BNR Prolog, see [BNR Prolog Source Archive][BNRParchive].) This is an attempt to capture the design and provide a platform for executing the numerous examples found in the [literature][bnrpp]. As it is constrained by the host environment (SWI-Prolog) it can't be 100% compliant with the original implementation(s), but required changes should be minimal.
 
In the process of recreating this version of CLP(BNR) subsequent work in relational interval arithmetic has been used, in particular [Efficient Implementation of Interval Arithmetic Narrowing Using IEEE Arithmetic][ia1] and [Interval Arithmetic: from Principles to Implementation][ia2]. In addition, there is at least one comparable system [CLIP][clip] that is targeted at GNU Prolog, ([download CLIP][cldl]). While earlier implementations typically use a low level  of the relational arithmetic primitives, advances in computing technology enable this Prolog version of CLP(BNR) to achieve acceptable performance while maintaining a certain degree of platform independence (addressed by SWI-Prolog) and facilitating experimentation (no "building" required). [SWI-Prolog][swip] was used due it's long history (.ca 1987) as free, open-source software and for supporting attributed variables (`freeze` in previous versions of this repository) which is a key mechanism in implementing constrained logic variables. Starting with `v0.9`, CLP(BNR) requires features that are  supported in SWI-Prolog version `8.2` (or about `8.1.25` of the development stream) which include native rational numbers and IEEE floating point special values and rounding modes.

## A Brief Introduction

An interval in CLP(BNR) is a logic variable representing a closed set of real numbers between (and including) a numeric lower bound and upper bound. Intervals are declared using the `::` infix operator, e.g.,

	?- X::real, [A,B]::real(0,1).
	X::real(-1.0e+16,1.0e+16),
	A::real(0,1),
	B::real(0,1).

Standard practice for outputting attributed variables at the top level is to format them as a (residual) goal. (For narrow `real` intervals a more compact domain form is used as described below). If bounds are not specified (`X` above), the defaults are large, but finite, platform dependent values. The infinities (`inf` and `-inf`) are supported but must be explicitly specified in the declaration.

To constrain an interval to integer values, type `integer` can be used in place of `real`:

	?- I::integer, [J,K]::integer(-1,1).
	I::integer(-72057594037927936,72057594037927935),
	J::integer(-1,1),
	K::integer(-1,1).

Finally, a `boolean` is an `integer` constrained to have values `0` and `1` (meaning `false` and `true` respectively).

	?- B::boolean.
	B::boolean.

Note that no bounds are displayed for booleans because `(0,1)` is implicit in the `boolean` type.

Interval declarations define the initial bounds of the interval which are narrowed over the course of program execution. Narrowing is controlled by defining constraints in curly brackets, e.g.,

	?- [M,N]::integer(0,8), {M == 3*N}.
	M::integer(0,6),
	N::integer(0,2).

	?- [M,N]::integer(0,8), {M == 3*N}, {M>3}.
	M = 6,
	N = 2.

	?- [X,Y]::real, {1==X + 2*Y, Y - 3*X==0}.
	X:: 0.1428571428571428...,
	Y:: 0.428571428571428... .

In the first example, both `M` and `N` are narrowed by applying the constraint `{M == 3*N}`. Applying the additional constraint `{M>3}` further narrows the intervals to single values so the original variables are unified with the point (integer) values.
 
In the last example, the constraint causes the bounds to contract almost to a single point value, but not quite. The underlying reason for this is that standard floating point arithmetic is mathematically unsound due to floating point rounding errors and cannot represent all the real numbers in any case, due to the finite bit length of the floating point representation. Therefore all the interval arithmetic primitives in CLP(BNR) round any computed result outwards (lower bound towards -inifinity, upper bound towards infinity) to ensure that any answer is included in the resulting interval, and so is mathematically sound. (This is just a brief, informal description; see the literature on interval arithmetic for a more complete justification and analysis.) This example also demonstrates the more compact "elipsis postfix" form used to output `real` intervals whose bounds have narrowed so that at least the first 3 digits match. This is not actually a goal but does present the domain in a more readable form. (A strict "goal" format including constraints is supported by enabling a CLP(BNR) environment flag.)

Sound constraints over real intervals (since interval ranges are closed) include `==`, `=<`, and `>=`, while `<>`, `<` and `>` are provided for `integer`'s. A fairly complete set of standard arithmetic operators (`+`, `-`, `*`, `/`, `**`), boolean operators (`and`, `or`, `xor`, `nand`, `nor`) and common functions (`exp`, `log`, `sqrt`, `abs`, `min`, `max` and standard trig and inverse trig functions) provided as interval relations. Note that these are relations so `{X==exp(Y)}` is the same as `{log(X)==Y}`. A few more examples:

	?- {X==cos(X)}.
	X:: 0.73908513321516... .

	?- {X>=0,Y>=0, tan(X)==Y, X**2 + Y**2 == 5}.
	X:: 1.096668128705471...,
	Y:: 1.94867108960995... .

	?- {Z==exp(5/2)-1, Y==(cos(Z)/Z)**(1/3), X==1+log((Y+3/Z)/Z)}.
	Z:: 11.18249396070347...,
	Y:: 0.25518872031002...,
	X:: -2.0616342622472... .

These examples did not require an explicit `::` declaration since the constraints were sufficient to narrow the values to acceptable answers. Internally, any undeclared interval is assigned infinite bounds which often inhibits narrowing possibilities, so it's good practice to always declare intervals with reasonable (or default) bounds values.  

It is often the case that the fixed point iteration that executes as a consequence of applying constraints is unable to generate meaningful solutions without applying additional constraints. This may be due to multiple distinct solutions within the interval range, or because the interval iteration is insufficiently "clever". For example:

	?- {2==X*X}.
	X::real(-1.4142135623730951,1.4142135623730951).
but 

	?- {2==X*X, X>=0}.
	X:: 1.414213562373095... .

In more complicated examples, it may not be obvious what the additional constraints might be. In these cases a higher level search technique can be used, e.g., enumerating integer values or applying "branch and bound" algorithms over real intervals. A general predicate called `solve/1` is provided for this purpose. Additional application specific techniques can also be implemented. Some examples:

	?- {2==X*X},solve(X).
	X:: -1.414213562373095... ;
	X:: 1.414213562373095... .

	?- X::real, {0 == 35*X**256 - 14*X**17 + X}, solve(X).
	X:: -0.847943660827315... ;
	X:: 0.0... ;
	X:: 0.847943660827315... ;
	X:: 0.995842494200498... .

	?- {Y**3+X**3==2*X*Y, X**2+Y**2==1},solve([X,Y]).
	Y:: 0.39105200...,
	X:: -0.92036858... ;
	Y:: -0.920368584...,
	X:: 0.39105200... ;
	Y:: 0.8931356...,
	X:: 0.4497874... ;
	Y:: 0.449787...,
	X:: 0.8931356... ;
	false.

Note that all of these examples produce multiple solutions that are produced by backtracking in the top-leval listener (just like any other top level query). `solve/1` is one of several predicates in CLP(BNR) which "search" for solutions.

Here is the current set of operators and functions supported in this version:

	== is <> =< >= < >                    %% equalities and inequalities
	+ - * /                               %% basic arithmetic
	**                                    %% includes real exponent, odd/even integer
	abs                                   %% absolute value
	sqrt                                  %% square root (needed?)
	min max                               %% min/max (arity 2)
	<= =>                                 %% inclusion
	and or nand nor xor ->                %% boolean
	- ~                                   %% unary negate and not
	exp log                               %% exp/ln
	sin asin cos acos tan atan            %% trig functions

Further explanation and examples can be found at [BNR Prolog Papers][bnrpp] and in the [Guide to CLP(BNR)][clpBNR_UG] (a work in progress).

[ia1]:         http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.44.6767
[ia2]:         http://fab.cba.mit.edu/classes/S62.12/docs/Hickey_interval.pdf
[clip]:        https://scholar.lib.vt.edu/ejournals/JFLP/jflp-mirror/articles/2001/S01-02/JFLP-A01-07.pdf
[cldl]:        http://interval.sourceforge.net/interval/index.html
[swip]:        http://www.swi-prolog.org
[bnrpp]:       https://ridgeworks.github.io/BNRProlog-Papers
[clpBNR_UG]:   https://ridgeworks.github.io/clpBNR_pl/CLP_BNR_Guide/CLP_BNR_Guide.html
[BNRParchive]: https://github.com/ridgeworks/BNRProlog-Source-Archive

### Engineering Considerations

Intervals are narrowed through a constraint propgation mechanism. When a new constraint is added, existing constraints must be checked and any intervals in those constraints may be narrowed. This iterative process normally continues until no further changes in interval values occur; the constraint network is now again in a stable state, and further constraints can now be added. Depending on the specific network, this could happen very quickly or take a very long time, particularly given the high precision of 64 bit floating point numbers.

A simple example example is the quadratic equation `{X**2-2*X+1 == 0}` which has a single root at `X=1`. This will converge very, very slowly on the solution, in fact so slowly that few people will have the patience to wait for it, particularly when it be be easily solved by factoring the left hand side in a few seconds. To mitigate against this apparent non-termination, there is an internal limit on the number of narrowing operations that will executed after the addition of a constraint. Once this limit is exceeded, only intervals which narrow by a significant degree will cause the effects to be propagated to the other constraints. This stays in effect until the pending queue is emptied and the network is deemed stable. As a result, the intervals may not be narrowed to the full extent defined by the constraint network, but they will still contain and solutions and they will be generated in a reasonable time.

The default value for the iteration limit is 3,000, and can be controlled by the Prolog flag `clpBNR_iteration_limit`. To demonstrate the effect, here's the query from the above paragraph:

	?- clpStatistics,X::real,{X**2-2*X+1 == 0},clpStatistics(SS).
	SS = [userTime(0.04670699999996941), gcTime(0.003), globalStack(293320/1048544), trailStack(45776/264168), localStack(2432/118648), inferences(178237), narrowingOps(3001), narrowingFails(0), node_count(5), max_iterations(3001/3000)],
	X:: 1.00... .

So the interval bounds have narrowed to about 3 decimal places of precision using the default value. The `clpStatistics` shows that the maximum number of iterations has exceeded the default, indicating the iteration limiter has been activated (with an additional two narrowing operations required to clear the queue. To show the effects of increasing the limit:

	?- set_prolog_flag(clpBNR_iteration_limit,100000),clpStatistics,X::real,{X**2-2*X+1 == 0},clpStatistics(SS).
	SS = [userTime(1.5168969999999717), gcTime(0.101), globalStack(1030800/1048544), trailStack(341808/526312), localStack(2432/118648), inferences(5925487), narrowingOps(100001), narrowingFails(0), node_count(5), max_iterations(100001/100000)],
	X:: 1.000... .

A small increase in precision has been achieved, but it still exceeded the limit and took significantly longer. Decreasing the limit has the opposite effect:

	?- set_prolog_flag(clpBNR_iteration_limit,1000),clpStatistics,X::real,{X**2-2*X+1 == 0},clpStatistics(SS).
	SS = [userTime(0.015356999999994514), gcTime(0.001), globalStack(670376/1048544), trailStack(233712/264168), localStack(2432/118648), inferences(59737), narrowingOps(1001), narrowingFails(0), node_count(5), max_iterations(1001/1000)],
	X::real(0.9921663400256505, 1.0083828203198095).

Generally, the default provides adequate precision for most problems, and in many cases, limiting isn't even activated. When the problem requires additional precision and `clpStatistics` indicates limiting has occurred, the limit can be adjusted using the Prolog flag. Keep in mind that any positive answer is conditional since it indicates that there is no contradiction detected at the level of precision used in the arithmetic operations. This is true whether or not limiting is activated.

There is a second Prolog flag defined, `clpBNR_default_precision`, which affects the precision of answers returned from search predicates, e.g., `solve/1`. These predicates typically split intervals into sub-ranges to search for solutions and this flag determines how small the interval can get before splitting fails. The value of the flag roughly specifies the number of digits of precision. The default value is 6, which is adequate for most purposes. In some cases the solver supports an additional argument to override the default value for the scope that call.

## Getting Started

If SWI-Prolog has not been installed, see [downloads](http://www.swi-prolog.org/Download.html). A current development release or stable release 8.2 or greater is required.

If you do not want to download this entire repo, a package can be installed using the URL `https://ridgeworks.github.io/clpBNR_pl/Package/clpBNR-0.9.1.zip`. Once installed, it can be loaded with `use_module/1`. For example:

	?- pack_install(clpBNR,[url('https://ridgeworks.github.io/clpBNR_pl/Package/clpBNR-0.9.1.zip')]).
	Verify package status (anonymously)
		at "http://www.swi-prolog.org/pack/query" Y/n? 
	Package:                clpBNR
	Title:                  CLP over Reals using Interval Arithmetic - includes includes Rational, Integer and Boolean domains as subsets.
	Installed version:      0.9.1
	Author:                 Rick Workman <ridgeworks@mac.com>
	Home page:              https://github.com/ridgeworks/clpBNR_pl
	Install "clpBNR-0.9.1zip" (35,158 bytes) Y/n? 
	
	?- use_module(library(clpBNR)).
	
	*** clpBNR v0.9.0alpha ***
	true.
   
Or if the respository has been down downloaded, just consult `clpBNR.pl` (in `src/` directory) which will automatically include `ia_primitives.pl`, `ia_utilities.pl`, and `ia_simplify.pl`.

The `clpBNR` module declaration is:

	:- module(clpBNR,          % SWI module declaration
		[
		op(700, xfx, ::),
		op(150, xf,  ...),     % postfix op currently just for output
		(::)/2,                % declare interval
		{}/1,                  % define constraint
		interval/1,            % filter for clpBNR constrained var
		domain/2, range/2,     % for compatibility
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
		list/1,                % for compatibility
		print_interval/1, print_interval/2,      % pretty print interval with optional stream
		solve/1, solve/2,      % solve (list of) intervals using split to find point solutions
		splitsolve/1, splitsolve/2,   % solve (list of) intervals using split
		absolve/1, absolve/2,  % absolve (list of) intervals, narrows by nibbling bounds
		enumerate/1,           % "enumerate" integers
		global_minimum/2,      % find interval containing global minimums for an expression
		global_minimum/3,      % global_minimum/2 with definable precision
		global_maximum/2,      % find interval containing global minimums for an expression
		global_maximum/3,      % global_maximum/2 with definable precision
		partial_derivative/3,  % differentiate Exp wrt. X and simplify
		clpStatistics/0,       % reset
		clpStatistic/1,        % get selected
		clpStatistics/1,       % get all defined in a list
		watch/2                % enable monitoring of changes for interval or (nested) list of intervals
		]).


## SWI-Prolog Arithmetic Flags

This package sets the SWI-Prolog arithmetic flags as follows:

	set_prolog_flag(prefer_rationals, true),           % enable rational arithmetic
	set_prolog_flag(max_rational_size, 16),            % rational size in bytes before ..
	set_prolog_flag(max_rational_size_action, float),  % conversion to float

	set_prolog_flag(float_overflow,infinity),          % enable IEEE continuation values
	set_prolog_flag(float_zero_div,infinity),
	set_prolog_flag(float_undefined,nan),

This package will not work as intended if these flag values are not respected.


More documentation including many real world examples may be found in [Guide to CLP(BNR)][clpBNR_UG] (under construction). 
