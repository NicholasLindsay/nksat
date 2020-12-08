# nksat

`nksat` is a lightweight SAT solver written in C++. `nksat` checks systems of
boolean equations for satisfiability. `nksat` expects a single input file in
the standard DIMACS `.cnf` input format.

Under the hood, `nksat` uses the [DPLL](https://en.wikipedia.org/wiki/DPLL_algorithm) 
algorithm and makes use of the "two watched literals" and "pure literal 
elimation" optimizations.

## Building nksat

`nksat` has the following dependencies:
- A working C++ compiler and build system (e.g. `Make`)
- `CMake`

To build nksat, create a new directory (e.g. `build`) inside the project root
directory, and then inside that directory run the following command 
(assuming `Make` is the default build system):

`cmake .. && make`

This command will generate and run the build files. An `nksat` executable will
be created in the build directory.

## Running nksat

`nksat` can be run using the following command:
`nksat <path/to/.cnf/file>`

`nksat` expects input files to be in the DIMACS .cnf format as described
[here](http://www.satcompetition.org/2009/format-benchmarks2009.html).

`nksat` will output either a satisfying assignemnt or inform if no such
assignment exists.

## Credit

`nksat` was written jointly by:
- Nicholas Lindsay (<nick.lindsay@yale.edu>)
- Ketaki Joshi (<ketaki.joshi@yale.edu>)

Both authors contributed equally.
