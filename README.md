# CLP(ASP)

A generic CLP(X) implementation with term as a testing domain.
Aim is to implement Answer-Set Programming within the CLP(X) scheme.

## Usage

Compile the CLPtermHs.agda. This generates the folders _build and MAlonzo. In MAlonzo/Code/ClptermHs.hs the compiled agda code is ready to use in Haskell. The parser is implemented in Haskell, but is not generic, right now hardcoded with CLP(term).

## Implement your own domain

To implement your own domain into this generic implementation, the src/CLP-agda/Common folder is the place where extensions can be made. For larger definitions, make a new folder in CLP-agda with the name of the domain.

### What to extend?

First, set up a data type describing your domain. The data type must be a (Set -> Set) -> Set (extensive type), so that the LogicVar type can be applied to it. With that, you don't need to bother yourself with the representation of logical variables in your domain. For every place that can be substituted by a variable, instead of *Type*, use f (*Type* f).

Now in Common/types.agda extend the universe codes with a code for your new type. In the decoding function, return your type. In the Expr data type extend the constructors with the composite operators of your domain. Use the code as the argument. Do the same in the ℒ for your domain constraints.

It is advised to also extend the utilities in Common/utilities.agda. These are functions which are likely to be used in a solver no matter what the domain is. After that, extend the solve function in Common/solver with your solver.

With that, you have implemented your domain in this CLP(X) scheme.