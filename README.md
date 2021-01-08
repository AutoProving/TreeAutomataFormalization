# Formalization of Tree Automata in Coq

## Dependencies

This project depends on [Coq](https://coq.inria.fr/) 8.12, [MathComp ssreflect](https://math-comp.github.io/) 1.11, and [MathComp finmap](https://github.com/math-comp/finmap) 1.5.

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
