# RECIP
=====

A Reduction-Based Algorithm for the Clique Interdiction Problem

Installation Notes
=====

The package relies the following software.
- IBM CPLEX (https://www.ibm.com/cn-zh/products/ilog-cplex-optimization-studio)

After installing the packages, run `scons program=vcc variant=optimized` to build.

## Running

This package contains 5 different algorithms: **Chalupa**, **Redu**, **ReduVCC**, **BnR**, and **EdgeBnR**, which can be run as follows:

**Chalupa**

`./optimized/vcc --preconfiguration=fsocial --k=2 --mis=<independent set size> --run_type="Chalupa" <input graph>`

**Redu**
`./optimized/vcc --preconfiguration=fsocial --k=2 --run_type="Redu" <input graph>`

**ReduVCC**
`./optimized/vcc --preconfiguration=fsocial --k=2 --mis=<independent set size> --run_type="ReduVCC" <input graph>`

**BnR**
`./optimized/vcc --preconfiguration=fsocial --k=2 --run_type="bnr" <input graph>`

**EdgeBnr**
`./optimized/vcc --preconfiguration=fsocial --k=2 --run_type="edge_bnr" <input graph>`

## Input Format

ReduVCC uses **The unweighted METIS format**, which consists of

   `<# vertices> <# edges> 1`

   followed by `<# vertices>` lines of space-separated vertices,  where the `i`-th line consists of 
   all neighbors of `i`. All vertices range from `1` to `<# vertices>`

Loops and directed edges are not supported.

## Data Sets

You will find an example graph in the directory `examples`