<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# hanoi

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/thery/hanoi/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/thery/hanoi/actions/workflows/docker-action.yml




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

## Meta

- Author(s):
  - Laurent Théry
- License: [MIT License](LICENSE)
- Compatible Coq versions: 9.0 or later
- Additional dependencies:
  - [MathComp ssreflect 2.4 or later](https://math-comp.github.io)
  - [MathComp algebra 2.4 or later](https://math-comp.github.io)
  - [MathComp finmap 2.2.1 or later](https://github.com/math-comp/finmap)
- Coq namespace: `hanoi`
- Related publication(s): none

## Building and installation instructions

To build and install manually, do:

``` shell
git clone https://github.com/thery/hanoi.git
cd hanoi
make   # or make -j <number-of-cores-on-your-machine> 
make install
```



