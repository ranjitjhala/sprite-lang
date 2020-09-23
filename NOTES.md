# SPRITE

An tutorial-style implementation of liquid/refinement types for a subset of Ocaml/Reason.

## TODO: Paper

- [*] Lang1 : STLC + Annot         (refinements 101)
- [*] Lang2 : ""   + Branches      (path-sensitivity)
- [*] Lang3 : ""   + *-refinements (inference + qual-fixpoint)
- [*] Lang4 : ""   + T-Poly        (type-polymorphism)
- [*] Lang5 : ""   + Data          (datatypes & measures)
- [*] Lang6 : ""   + R-Poly        (refinement-polymorphism)
- [*] Lang7 : ""   + Termination   (metrics + invariants)
- [-] Lang8 : ""   + Reflection    (proofs)
- [ ] well-formedness
- [ ] L7 Invariant & Validity 
- [ ] intro
- [ ] outro

## TODO: Code 

- [*] Save Horn QUERY
- [ ] ANF

## L7 Invariant & Validity 

```
I, G, f_k |- t
---------------------- [Inv-RAbs]
I, G |- rall r. t

I, G, a |- t
---------------------- [Inv-TAbs]
I, G |- all a. t

I, G, x:s |- x:s -> t
---------------------- [Inv-Fun]
I, G |- x:s -> t

G |- t <: I(t)
---------------------- [Inv-Base]
I, G |- t
```


## Dependencies

```txt
  L1 --> L2 --> L3 --> L4 --> L6
                  `--> L5 --> L7 --> L8
```

## Horn Constraints

- Syntax
- Semantics
- Solution
  - Houdini
  - Fusion
  - [McMillan, Bjorner, Rybalchenko]


### Types and Terms

```txt
p :== x                 -- PREDICATES
    | c
    | (op  p1 ... pn)   -- interpreted   ops
    | (f   p1 ... pn)   -- uninterpreted ops
    | (bop p1 ... pn)   -- boolean       ops

c :== p                 -- FORMULAS
    | c /\ c
    | all x. (p => c)

r ::= [v|p]             -- known refinements

t ::= Int[r]            -- refined int
    | x:t -> t          -- dependent arrow

e ::= x                 -- variables        [synth]
    | c                 -- constants        [synth]
    | \x. e             -- functions        [check]
    | e x               -- anf-application  [synth]
    | let x = e in e    -- let-binding      [check]
    | e : t             -- annotation       [check]
```

### Declarative Checking

Environments

```txt
G ::= 0 | G, x:t        -- environment
```

Judgments

```txt
G |- e <== t            -- checking  judgment
G |- e ==> t            -- synthesis judgment
```

Rules

- *Check-_* deals with `let`, `\x.e`
- *Synth-_* deals with `x`, `c`, `e x`, `e:t`

#### Subtyping Rules

```txt
Valid(G,p)
----------[Sub-Valid]
G |- p

G,v:int{p} |- q[w:=v]
-------------------------[Sub-Base]
G |- int{v:p} <: int{w:q}


G |- s2 <: s1       G,x2:s2 |- t1[x1:=x2] <: t2
------------------------------------------------[Sub-Fun]
G |- x1:s1 -> t1 <: x2:s2 -> t2
```

Alternate "Hybrid" Presentation

```txt
Valid(c)
--------
0 => c

G => (all x. (p => c))
----------------------
G, x:{p} => c

G => sub(s, t)
---------------
G |- s <: t
```

#### Checking Rules

```txt
G, x:t1 |- e <== t2
--------------------------[Chk-Lam]
G |- \x.e <== x:t1 -> t2


G |- e1 ==> t1        G, x:t1 |- e2 <== t2
--------------------------------------------[Chk-Let]
    G |- let x = e1 in e2 <== t2


G |- e ==> s        G |- s <: t
----------------------------------[Chk-Syn]
          G |- e <== t
```

#### Synthesis Rules

```txt
----------------- [Syn-Var]
G |- x ==> G(x)

----------------- [Syn-Con]
G |- x ==> ty(c)


G |- e <== t
----------------- [Syn-Ann]
G |- e:t ==> t


G |- e ==> x:s -> t
G |- y <== s
-----------------------[Syn-App]
G |- e y ==> t[x := y]



G |- e ==> s -> t   G |- (s -> t) * x ==> t
-------------------------------------------
G |- e x ==> t

G |- e ==> forall as. x1:s1 -> ... xn:sn -> t


G |- (forall as.S * y1 ... yn) <== T
G |- (e y1 ... yn) ==> t
```

### Algorithmic Constraints

```haskell
--------------------------------------------------------------------
sub :: (Type, Type) -> Cstr
--------------------------------------------------------------------
sub(B{v:p}, B{w:q})           = (v::p) => q[w:=v]
sub(x1:s1 -> t1, x2:s2 -> t2) = sub (s2, s1) /\ (x2 :: t2) => sub(t1[x1:=x2], t2)

--------------------------------------------------------------------
imp :: (Env, Cstr) -> Cstr
--------------------------------------------------------------------
imp (0, c)     = c
imp (G;x:t, c) = imp(G, all x t c)
```

```haskell
-------------------------------------------------------
check                     :: (Env, Expr, Type) -> C
-------------------------------------------------------
check (g, \x.e, x:s -> t) = (x :: s) => c
  where
    c                     = check(g;x:s, e, t)

check (g, let x e e', t') = c /\ ((x::s) => c')
  where
    (c, s)                = synth(g, e)
    c'                    = check(g;x:s, e', t')

check (g, e, t)           = sub(s, t)
  where
    (c, s)                = synth(g, e)

-----------------------------------------------------
synth :: (Env, Expr) -> (C, Type)
-----------------------------------------------------
synth (g,   x)   = (TT, lookupEnv g x  )

synth (g,   c)   = (TT, ty c           )

synth (g, e y)   = (ce /\ cy, t[x := y])
  where
    (ce, x:s->t) = synth (g, e)
    cy           = check (g, y)

synth (g, e:t)   = (c,     t )
  where
    c            = check g e t
```

## Lang2

### Examples

Booleans

```reason
/*@ val cmp : (x:int, y:int) => bool{b| b <=> (x < y)} */
let cmp = (x, y) => {
    if (x < y) {
        true
    } else {
        false
    }
}
```

Path Sensitivity

```reason
/*@ val abs : x:int => int[v| 0<=v && x <= v] */
let abs = (x) => {
    if x >= 0 {
        x
    } else {
        0 - x
    };
};

/*@ val test : (a:int, b:int) => int[v|0<=v && a + b <= v] */
let test = (a, b) => {
    let t1 = abs(a);
    let t2 = abs(b);
    t1 + t2
}
```

Recursion

```reason
/*@ val sum : n:int => int[v|0 <= v && n <= v] */
let rec sum = (n) => {
    if (n <= 0) {
        0
    } else {
        let n1 = n-1;
        let t1 = sum(n1);
        n + t1
    }
}
```

### Types and Terms

```txt
t ::=
    | Bool{r}           -- refined bool

e ::= ...
    | if v e1 e2        -- branches
    | letrec f = (e:t)  -- recursive binder with annot
```

### Declarative Checking

Environments

```
G ::= ... | G, _:t      -- extend with "fresh"/"distinct" binder
```

Judgments, Rules (as before)

#### Subtyping

Subtyping (as before)

#### Checking

Rec binders must have type-sig

```



              G |- v  <== bool
    G, _:int{v} |- e1 <== t
G, _:int{not v} |- e2 <== t
--------------------------------[Chk-If]
G |- if v e1 e2 <== t

G; f:t1 |- e1 <== t1       G; f:t1 |- e2 <== t2
------------------------------------------------[Chk-Rec]
G |- letrec f = (e1:t1) in e2  <== t2
```

#### Synthesis

**Note** Only when you add branches do you need
the singleton rule for variable lookup: without it 
`abs00.re` doesn't check!


```
--------------------------- [Syn-Var]
G |- x ==> singleton(G, x)
```

where

```
singleton(G, x) = v:b{p /\ v = x}  if  G(x) = b[v|p]
                  G(x)             otherwise
```

### Algorithmic Constraints

#### Check

```haskell
check g (EIf v e1 e2) t = ((x :: v) => c1) /\ ((x :: ~v) => c2)
  where
    c1 = check g e1 t  
    c2 = check g e2 t
    x  = fresh

check g (ERec f e1 t1 e2) t2 = c1 /\ c2
  where
    c1 = check g' e1 t1
    c2 = check g' e2 t2
    g' = g; f:t1
```

#### Synth

as before

## Lang 3

### Examples

```reason
/*@ val assert : bool[b|b] => int */
let assert = (b) => { 0 };

/*@ val abs : x:int => int[?] */
let abs = (x) => {
    if x >= 0 {
        x
    } else {
        0 - x
    };
};

/*@ val main : int -> int */
let main = (y) => {
  let ya  = abs(y); // neg: omit 'abs'
  let ok  = 0 <= ya;
  assert(ok)       // never fails
}
```

```reason
/*@ val assert : bool[b|b] => int */
let assert = (b) => { 0 };

/*@ val abs : x:int => int[?] */
let abs = (x) => {
    if x >= 0 {
        x
    } else {
        0 - x
    };
};

/*@ val incf: int => int */
let incf = (x:nat) : nat => {
    /*@ val wrap : (int -> int[?]) -> int[?] */
    let wrap = (f) => {
       let r = f(x);
       r + 1
    };
    let res = wrap(abs);
    let ok  = 0 < res;
    assert (ok)
};
```

### Types and Terms

```txt
p ::= ...
    | K(x1,...,xn)      -- horn-variable

r ::= ...
    | [?]               -- unknown
```

### Declarative Checking

"fresh" each annotation

#### Subtyping

(as before)

#### Checking

```txt
     t1 := fresh(s1)
G; f:t1 |- e1 <== t1
G; f:t1 |- e2 <== t2
------------------------------------- [Chk-Rec]
G |- letrec f = (e1:s1) in e2  <== t2
```

#### Synthesis

```
G |- e <== t  t := fresh(s)
--------------------------- [Syn-Ann]
G |- e:s => t
```

### Algorithmic Constraints


"fresh" each annotation

```haskell
fresh :: Env -> Type -> Type
fresh g (B[r])     = B[freshR g B r]
  where
    r'             = freshR g r

fresh g (x:s -> t) = x:s' -> t'
  where
    s'             = fresh g s
    t'             = fresh (g; x:s') t

freshR :: Env -> Base -> Reft -> Reft
freshR _ _ [v|p] = [v|p]
freshR g B [?]   = [v|k(v, x1...)]
  where
    v            = freshV
    k            = freshK [B, s1...]
    (x1:s1...)   = g
```

Rest is swept under the horn solving rug?

#### Check

```haskell
check g (ERec f e1 s1 e2) t2 = c1 /\ c2
  where
    c1 = check g' e1 t1
    c2 = check g' e2 t2
    g' = g; f:t1
    t1 = fresh s1
```

#### Synth

```haskell
synth (g, e:s) = (c, t)
  where
    c          = check g e t
    t          = fresh s
```

## Lang 4

### Examples

see `tests/L4/{pos, neg}`

### Types and Terms

```txt
G ::= ...
    | G, a      -- ^ type variables

t :== ...
    | a[r]      -- ^ refined base type
    | all a. t  -- ^ forall types (quantifiers at the top)

e :== ...
    | Λ a. e    -- ^ type abstraction
    | e [t]     -- ^ type application
```

### Declarative Checking

The real hassle here is the *elaboration* step that adds the explicit
type abstraction and application.

#### Subtyping

```txt
G, v:int{p} |- q[w:=v]
-------------------------[Sub-Base]
G |- b[v|p] <: b[w|q]

G |- t1 <: t2 [a2 := a1]
------------------------------[Sub-All]
G |- all a1. t1 <: all a2. t2
```

#### Checking

```txt
G, a |- e <== s
------------------------ [Chk-TLam]
G |- Λ a. e <== all a. s
```

#### Synthesis 

```txt
G |- e ==> all a. s
------------------------- [Syn-TApp]
G |- e[t] ==> s [ a := t]
```

### Algorithmic Constraints

#### Check

```haskell
check g (ETLam a e _) (TAll b t) | a == b = do
  check g e t
```

#### Synth

```haskell
synth g (ETApp e t l) = do
  (ce, te)   <- synth g e
  case te of
    TAll a s -> do tt <- Misc.traceShow "REFRESH" <$> refresh l g t
                   return (ce, tsubst a tt s)
    _        -> failWith "Type Application to non-forall" l
```

## Lang 5

### Examples

containers

- head00

data-refinement

- tuple00
- olist00

measures

- head01
- tail01
- append

### Types and Terms

```txt
d ::= [C1:t1,...]       -- ^ data-definition

G ::= ...
    | G, d              -- ^ data-definitions

a := C(x1...) => e      -- ^ switch-alternative

e :== ...
    | C(x1...)          -- ^ constructor
    | switch(x){ a1...} -- ^ destructor
```

### Declarative Checking

#### Subtyping

```txt
G,v:int{p} |- q[w:=v]     G |- si <: ti
-----------------------------------------[Sub-TCon]
G |- (C s1...)[v|p] <: (C t1...)[w|q]
```

#### Checking

Environment Extension

```txt
G(y) = s
-----------------------------[G-Scr]
G | y + 0 * t ~~> G, y:s/\t

G, z:s | y + zs * t[z/x] ~~> G'
---------------------------------[G-Ext]
G | y + z;zs * (x:s -> t) ~~> G'
```

```txt
G | y |- a_i <== t
----------------------------[Chk-Switch]
G |- switch y {a_1...} <== t


unfold(G, c, y) === s   G | y + z... * s ~~> G'     G' |- e <== t
----------------------------------------------------------------- [Chk-Alt]
G | y |- C z... -> e <== t


G(y) === tc[ts]   G(c) === all as. t
------------------------------------- [Unfold]
unfold(g, c, y) === t [as := ts]
```


#### Synthesis

```
singleton(G, x) = v:b     [p /\ v = x] if G(x) = b[v|p]
                  v:(c ts)[p /\ v = x] if G(x) = c ts
                  G(x)             otherwise
```

### Algorithmic Constraints

#### Check

#### Synth
