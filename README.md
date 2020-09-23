# SPRITE

An tutorial-style implementation of liquid/refinement types for a subset of Ocaml/Reason.

## Install

**1. Get Z3** 

[Download from here](https://github.com/Z3Prover/z3/releases) and make sure `z3` is on your `$PATH`

**2. Clone the repository**

```
$ git clone git@github.com:ranjitjhala/sprite-lang.git
$ cd sprite-lang
```

**3. Build** 

Using `stack` 

```
$ stack build
```

or 

```
$ cabal v2-build
```

## Run on a single file

```
$ stack exec -- sprite 8 test/L8/pos/listSet.re
```

The `8` indicates the *language-level* -- see below.

## Horn VC

When you run `sprite N path/to/file.re` 
the generated Horn-VC is saved in `path/to/.liquid/file.re.smt2`.

So for example 

```
$ stack exec -- sprite 8 test/L8/pos/listSet.re
```

will generate a VC in 

```
test/L8/pos/.liquid/listSet.re.smt2
``` 

## Languages

- [*] Lang1 : STLC + Annot         (refinements 101)
- [*] Lang2 : ""   + Branches      (path-sensitivity)
- [*] Lang3 : ""   + *-refinements (inference + qual-fixpoint)
- [*] Lang4 : ""   + T-Poly        (type-polymorphism)
- [*] Lang5 : ""   + Data          (datatypes & measures)
- [*] Lang6 : ""   + R-Poly        (refinement-polymorphism)
- [*] Lang7 : ""   + Termination   (metrics + invariants)
- [*] Lang8 : ""   + Reflection    (proofs)