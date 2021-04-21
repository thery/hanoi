[![Build Status](https://travis-ci.org/thery/hanoi.svg?branch=master)](https://travis-ci.org/thery/hanoi)

## Hanoi


Hanoi tower in Coq


| File                              |  Content                                 | 
| --------------------------------- | -----------------------------------------| 
| [extra](./extra.v)                | Extra theorems from the standard library |
| [gdist](./gdist.v)                | Distance in a graph                      |
| [ghanoi](./ghanoi.v)              | General Hanoi framework                  |
| [ghanoi3](./ghanoi3.v)            | General Hanoi framework with 3 pegs      |
| [lhanoi3](./lhanoi3.v)            | Linear Hanoi tower with 3 pegs           |
| [rhanoi3](./rhanoi3.v)            | Regular Hanoi tower with 3 pegs          |
| [triangular](./triangular.v)      | Theorems about triangular numbers        |
| [phi](./phi.v)                    | Theorems about the Φ function            |
| [psi](./psi.v)                    | Theorems about the Ψ function            |
| [ghanoi4](./ghanoi4.v)            | General Hanoi framework with 4 pegs      |
| [rhanoi4](./rhanoi4.v)            | Regular Hanoi tower with 4 pegs          |
| [star](./star.v)                  | Some maths for the shanoi                |
| [shanoi](./shanoi.v)              | Hanoi tower in star                      |
| [shanoi4](./shanoi4.v)            | Hanoi tower with 4 pegs in star          |

A note about this development is available 
[here](https://hal.inria.fr/hal-02903548).

An interactive version of the library is available 
[here](https://thery.github.io/hanoi/index.html).


To build the library, download the files and type ```opam install .``` or manually type  
```make``` and 
then ```make install``` (the dependencies are listed in 
[opam](./opam)).
