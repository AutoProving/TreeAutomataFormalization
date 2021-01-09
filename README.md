# Formalization of Basic Concepts from Tree Automata Theory in Coq

## Dependencies

This project depends on [Coq](https://coq.inria.fr/) 8.12 or 8.13, [MathComp ssreflect](https://math-comp.github.io/) 1.11 or 1.12, and [MathComp finmap](https://github.com/math-comp/finmap) 1.5.

### Instal dependencies with opam

Version 2 of [opam](https://opam.ocaml.org/doc/Install.html) is needed.

To get the coq-released repo for opam 2, run: 
```
opam repo add coq-released https://coq.inria.fr/opam/released
```

To install the dependencies run:
```
opam install . --deps-only
```
 
## Compilation

```
make
```

## Documentation

```
make coqdoc
```

The generated documentation will be in `docs/coqdoc`.

The documentation is generated with CoqdocJS: https://github.com/palmskog/coqdocjs

## Licence

This project is under the MIT licence. More details can be found in the file LICENSE and at https://mit-license.org/

## Acknowledgements

We acknowledge suport from the Research Council of Norway in the context of the project 
AUTOPROVING - Automated Theorem Proving From the Mindset of Parameterized Complexity Theory (Proj. Number 288761). 
