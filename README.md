# CLP(BNR)

`clpBNR` is an implementation of CLP(BNR) structured as a package for SWI-Prolog (V8.2 or later).

CLP(BNR) is an instance of CLP(*R*), i.e., CLP over the domain of real numbers. It differs from some other CLP(*R*)'s in that:
* CLP(BNR) is complete in that any real number can be finitely represented even though the set of reals is infinite. It does this by sacrificing precision: a real number *R* is represented by an interval (*L,U*) where *L=<R=<U* and *L* and *U* are numbers as defined by SWI-Prolog (integers, rationals or floats, including the IEEE infinity values). A precise value (*L=U*) is represented directly by the number.
* CLP(BNR) arithmetic is mathematically sound. Any computed interval will contain the precise value. Due to the well-known pitfalls of IEEE floating point arithmetic, any CLP(*R*) based on conventional IEEE floating point arithmetic is unsound. (Try: `?- 1.21 =:= 1.1*1.1.`) In particular the add and multiply operations are non-associative and non-distributive. Relational interval arithmetic in CLP(BNR) (and some others) ensures that computed intervals contain the mathematically correct real value.
* All constraints, including non-linear constraints are active. In some CLP(*R*) implementations only linear constraints are active; non-linear constraints are deferred until their set of variables is sufficiently resolved that the constraint becomes linear.
* CLP(BNR) supports an "integral" constraint which forces interval bounds to be integers, enabling constraints over finite domain problems within the relational interval arithmetic framework; booleans can be represented as integer intervals with bounds `((0,1))` and  primitives to support boolean logic are included. Including integers and booleans within a single arithmetic framework enables natural solutions to mixed domain problems.
* Implementation: For simplicity and portability reasons, this version of CLP(BNR) is entirely implemented in SWI-Prolog. The main dependancies include attributed variables, support for rationals and IEEE floating point numbers (including rounding modes), and global variables for operational measurements.

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

Note that all of these examples produce multiple solutions that are produced by backtracking in the top-level listener (just like any other top level query). `solve/1` is one of several predicates in CLP(BNR) which "search" for solutions.

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

Further explanation and examples, including a complete reference section, can be found in the [Guide to CLP(BNR)][clpBNR_UG]. Examples include problems in finite domains, and finding roots, global optima, and boundary value solutions to differential equations. Additional background material is available at [BNR Prolog Papers][bnrpp].

[ia1]:         http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.44.6767
[ia2]:         http://fab.cba.mit.edu/classes/S62.12/docs/Hickey_interval.pdf
[clip]:        https://scholar.lib.vt.edu/ejournals/JFLP/jflp-mirror/articles/2001/S01-02/JFLP-A01-07.pdf
[cldl]:        http://interval.sourceforge.net/interval/index.html
[swip]:        http://www.swi-prolog.org
[bnrpp]:       https://ridgeworks.github.io/BNRProlog-Papers
[clpBNR_UG]:   https://ridgeworks.github.io/clpBNR/CLP_BNR_Guide/CLP_BNR_Guide.html
[BNRParchive]: https://github.com/ridgeworks/BNRProlog-Source-Archive

## Getting Started

If SWI-Prolog has not been installed, see [downloads](http://www.swi-prolog.org/Download.html). A current development release or stable release 8.2 or greater is required.

If you do not want to download this entire repo, a package can be installed using the URL `https://github.com/ridgeworks/clpBNR.git`. Once installed, it can be loaded with `use_module/1`. For example:

	﻿?- pack_install(clpBNR,[url('https://github.com/ridgeworks/clpBNR.git')]).
	% Cloning into '/Users/rworkman/.local/share/swi-prolog/pack/clpBNR'...
	Verify package status (anonymously)
		at "https://www.swi-prolog.org/pack/query" Y/n? 
	% Contacting server at https://www.swi-prolog.org/pack/query ... ok
	% "clpBNR.git" was downloaded 2 times
	Package:                clpBNR
	Title:                  CLP over Reals using Interval Arithmetic - includes Rational, Integer and Boolean domains as subsets.
	Installed version:      0.9.7
	Author:                 Rick Workman <ridgeworks@mac.com>
	Home page:              https://github.com/ridgeworks/clpBNR
	Download URL:           https://github.com/ridgeworks/clpBNR.git
	Activate pack "clpBNR" Y/n? 
	true.
	
	﻿?- use_module(library(clpBNR)).
	% *** clpBNR v0.9.7alpha ***.
	true.
   
Or if the respository has been down downloaded, just consult `clpBNR.pl` (in `prolog/` directory) which will automatically include helper files in directory `clpBNR`. Past releases can be found in the repo "Releases" (e.g., <https://github.com/ridgeworks/clpBNR/archive/v0.9.2.zip>).

The `clpBNR` module declaration is:

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


## SWI-Prolog Arithmetic Flags

This package sets the SWI-Prolog arithmetic flags as follows:

	set_prolog_flag(prefer_rationals, true),           % enable rational arithmetic
	set_prolog_flag(max_rational_size, 16),            % rational size in bytes before ..
	set_prolog_flag(max_rational_size_action, float),  % conversion to float

	set_prolog_flag(float_overflow,infinity),          % enable IEEE continuation values
	set_prolog_flag(float_zero_div,infinity),
	set_prolog_flag(float_undefined,nan),

This package will not work as intended if these flag values are not respected.
