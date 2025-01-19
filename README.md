# RECIP
=====

A Reduction-Based Algorithm for the Clique Interdiction Problem

Installation Notes
=====

The package relies the following software.
- IBM CPLEX (https://www.ibm.com/cn-zh/products/ilog-cplex-optimization-studio)

After installing the packages, run `scons program=vcc variant=optimized` to build.

## Compile & Running

On a Linux system, **RECIP** can be compiled and run as follows:

**Compiling**

This is an example of compiling command.

`g++ main.cpp Graph.cpp -O2 -m64 -O -fPIC -fno-strict-aliasing -fexceptions -DNDEBUG -DIL_STD     -I/opt/ibm/ILOG/CPLEX_Studio1271/cplex/include     -I/opt/ibm/ILOG/CPLEX_Studio1271/concert/include     -L/opt/ibm/ILOG/CPLEX_Studio1271/cplex/lib/x86-64_linux/static_pic     -L/opt/ibm/ILOG/CPLEX_Studio1271/concert/lib/x86-64_linux/static_pic     -o recip -lconcert -lilocplex -lcplex -lm -lpthread -w`

**Running**

`./main <input graph> <output file> k`

- `<input graph>:` a file containing the given graph
- `<output file>:`  a file containing the default output of CPLEX, the number of nodes, edges after each reduction, and total execution time, etc
- `k:` interdiction budget as a floating-point number


## Graph Format

RECIP uses **DIMACS format**, which consists of

   `p edge <num_nodes> <num_edges>`

   `e <node_1> <node_2>`

**Example :**

p edge 3 2

e 1 2

e 1 3