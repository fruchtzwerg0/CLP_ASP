# CLP(ASP)

A generic, statically typed CLP(X) implementation with an s(CASP) parameterization.
This implementation uses Agda 2.6.4.3.

## Usage

To use a given CLP program, the Agda project must be compiled to Haskell via MAlonzo.
To build the Traveling Salesman example, this command must be executed to generate the Haskell code:
```
agda --compile --ghc-dont-call-ghc src\CLP-agda\Examples\travelingSalesman.agda
```

Then, add the resulting library directory to stack.
Then build the stack project.

## Examples

An example implementation of a domain group is outlined in [Domain Group](src/CLP-agda/Examples/myDomainGroup.agda).

An example implementation outlining default CLP(X) are given:

- Towers of Hanoi: [Towers of Hanoi](src/CLP-agda/Examples/hanoi_without_asp.agda).

Some example implementation outlining the ASP overloading are given:

- Stream Reasoning: [StreamReasoning](src/CLP-agda/Examples/streamreasoning.agda).
- Towers of Hanoi: [Towers of Hanoi](src/CLP-agda/Examples/hanoi_without_fd.agda).
- Towers of Hanoi with finite domains: [Towers of Hanoi](src/CLP-agda/Examples/hanoi.agda).
- N-Queens: [N-Queens](src/CLP-agda/Examples/nQueens.agda).
- Traveling Salesman: [Traveling Salesman](src/CLP-agda/Examples/travelingSalesman.agda).

