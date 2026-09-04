# 1. Tiny interval

This is a literate `rzk` file: exponentiation by the interval (`ar`), its right adjoint
(`rar`), transpose/untranspose, and naturality lemmas.

```rzk
#lang rzk-1

#assume funext : FunExt
```

## Prerequisites

- `hott/04-modalities.rzk.md` — `b-extract`, `b-elim`, `b-naturality`, `b-beta`, `b-map`, `mod ♭`, `_b`.
- `hott/01-paths.rzk.md` — `ap`, `concat`, `rev`.
- `hott/03-equivalences.rzk.md` — `is-equiv`, `Equiv`, `ap-cancel-has-retraction`.

## Right adjoint

First, introduce the exponentiation by interval functor.

```rzk
#def ar (A : U)
  : U
  := 𝕀 → A

#def ar-fmap (A B : U) (f : A → B)
  : ar A → ar B
  := \ p → \ i → f (p i)

#def ar-pure (A : U) (a : A)
  : ar A
  := \ _ → a
```

We postulate its right adjoint functor with counit, transpose, and untranspose.


GWB 24, axiom 3
```rzk
#postulate rar (A : (♭ U))
  : ( ♭ U)

#postulate ar-rar-counit
  : ( ♭ ( ( A :♭ U) → (x : 𝕀 → (b-extract U (rar (mod ♭ A)))) → A))

#def transpose-ar (A B :♭ U) (f : ♭ (B → (b-extract U (rar (mod ♭ A)))))
  : ( ♭ ( ( ar B) → A))
  :=
  let mod ♭ f' := f in
  mod ♭ (\ (g : 𝕀 → B) → (let mod ♭ eta := ar-rar-counit in eta) A (\ i → f' (g i)))

#postulate untranspose-ar (A B :♭ U) (f : ♭ ((ar B) → A))
  : ( ♭ ( B → (b-extract U (rar (mod ♭ A)))))

#postulate transpose-untranspose-ar (A B :♭ U)
  ( f : (♭ ((ar B) → A)))
  : transpose-ar A B (untranspose-ar A B f) = f

#postulate untranspose-transpose-ar (A B :♭ U)
  ( f : (♭ (B → (b-extract U (rar (mod ♭ A))))))
  : untranspose-ar A B (transpose-ar A B f) = f

#def transpose-ar-is-equiv (A B :♭ U)
  : is-equiv
    ( ♭ ( B → (b-extract U (rar (mod ♭ A)))))
    ( ♭ ( ( ar B) → A))
    ( transpose-ar A B)
  :=
  ( ( untranspose-ar A B
    , untranspose-transpose-ar A B)
  , ( untranspose-ar A B
    , transpose-untranspose-ar A B))

#def transpose-ar-equiv (A B :♭ U)
  : Equiv
    ( ♭ ( B → (b-extract U (rar (mod ♭ A)))))
    ( ♭ ( ( ar B) → A))
  :=
  ( transpose-ar A B
  , transpose-ar-is-equiv A B)

```

These operations induce canonical functorial actions.

```rzk
#def rar-pure (A :♭ U) (a :♭ A)
  : b-extract U (rar (mod ♭ A))
  :=
    let mod ♭ tr := untranspose-ar A Unit (mod _b (\ _ → a)) in
    tr unit

#def rar-fmap (A B :♭ U) (f :♭ A → B)
  : ( ♭ ( b-extract U (rar (mod ♭ A)) → b-extract U (rar (mod ♭ B))))
  :=
  untranspose-ar B (b-extract U (rar (mod ♭ A)))
    mod _b ( \ (p : 𝕀 → b-extract U (rar (mod ♭ A))) → f ((let mod ♭ eta := ar-rar-counit in eta) A p))
```

Naturality of transpositions.

```rzk
#def transpose-precomp (A B C :♭ U) (h :♭ C → B)
  ( w : ♭ (B → (b-extract U (rar (mod ♭ A)))))
  : ( let mod ♭ sec := w in transpose-ar A C (mod ♭ (\ (x : C) → sec (h x))))
  =_{ ♭ ((ar C) → A)} ( let mod ♭ t := transpose-ar A B w in mod ♭ (\ (p : 𝕀 → C) → t (\ i → h (p i))))
  := b-elim
       ( B → (b-extract U (rar (mod ♭ A))))
       ( \ (z : ♭ (B → (b-extract U (rar (mod ♭ A))))) →
           ( let mod ♭ sec := z in transpose-ar A C (mod ♭ (\ (x : C) → sec (h x))))
           =_{ ♭ ((ar C) → A)} ( let mod ♭ t := transpose-ar A B z in mod ♭ (\ (p : 𝕀 → C) → t (\ i → h (p i)))))
       ( w)
       ( \ (sec :_b B → (b-extract U (rar (mod ♭ A)))) → \ (e : mod ♭ sec =_{♭ (B → (b-extract U (rar (mod ♭ A))))} w) → refl)

#def transpose-untranspose-comp
  ( A B C :♭ U)
  ( h :♭ C → B)
  ( f :♭ (ar B) → A)
  :
    (let mod ♭ sec := untranspose-ar A B (mod ♭ f) in
    ( transpose-ar A C)
      ( mod ♭ (\ (x : C) → (sec) (h x))))
    = ( let mod ♭ f' := mod ♭ f in mod ♭ (\ (p : 𝕀 → C)
      → ( f') (\ i → h (p i))))
  :=
    concat
      ( ♭ ( ( ar C) → A))
      ( let mod ♭ sec := untranspose-ar A B (mod ♭ f) in
        transpose-ar A C (mod ♭ (\ (x : C) → sec (h x))))
      ( let mod ♭ t := transpose-ar A B (untranspose-ar A B (mod ♭ f)) in
        mod ♭ (\ (p : 𝕀 → C) → t (\ i → h (p i))))
      ( let mod ♭ f' := mod ♭ f in mod ♭ (\ (p : 𝕀 → C) → f' (\ i → h (p i))))
      ( transpose-precomp A B C h (untranspose-ar A B (mod ♭ f)))
      ( ap
        ( ♭ ( ( ar B) → A))
        ( ♭ ( ( ar C) → A))
        ( transpose-ar A B (untranspose-ar A B (mod ♭ f)))
        ( mod ♭ f)
        ( \ (g : ♭ ((ar B) → A)) → let mod ♭ t := g in mod ♭ (\ (p : 𝕀 → C) → t (\ i → h (p i))))
        ( transpose-untranspose-ar A B (mod ♭ f)))

#def untranspose-naturality-left
  ( A B C :♭ U)
  ( h :♭ C → B)
  ( f :♭ (ar B) → A)
  :
    ( let mod ♭ sec := untranspose-ar A B (mod ♭ f) in mod ♭ (\ (x : C) → sec (h x)))
    = ( untranspose-ar A C
        ( mod ♭ (\ (p : 𝕀 → C) → f (\ i → h (p i)))))
  :=
    ap-cancel-has-retraction
      ( ♭ ( C → b-extract U (rar (mod ♭ A))))
      ( ♭ ( ( ar C) → A))
      ( transpose-ar A C)
      ( ( untranspose-ar A C)
      , ( untranspose-transpose-ar A C))
      ( let mod ♭ sec := untranspose-ar A B (mod ♭ f) in mod ♭ (\ (x : C) → sec (h x)))
      ( untranspose-ar A C (mod ♭ (\ (p : 𝕀 → C) → f (\ i → h (p i)))))
      ( concat ( ♭ ( ( ar C) → A))
        ( transpose-ar A C (let mod ♭ sec := untranspose-ar A B (mod ♭ f) in mod ♭ (\ (x : C) → sec (h x))))
        ( mod ♭ (\ (p : 𝕀 → C) → f (\ i → h (p i))))
        ( transpose-ar A C (untranspose-ar A C (mod ♭ (\ (p : 𝕀 → C) → f (\ i → h (p i))))))
        ( concat ( ♭ ( ( ar C) → A))
          ( transpose-ar A C (let mod ♭ sec := untranspose-ar A B (mod ♭ f) in mod ♭ (\ (x : C) → sec (h x))))
          ( let mod ♭ sec := untranspose-ar A B (mod ♭ f) in transpose-ar A C (mod ♭ (\ (x : C) → sec (h x))))
          ( mod ♭ (\ (p : 𝕀 → C) → f (\ i → h (p i))))
          ( b-naturality
            ( B → (b-extract U (rar (mod ♭ A))))
            ( C → (b-extract U (rar (mod ♭ A))))
            ( ( ar C) → A)
            ( transpose-ar A C)
            ( \ (sec : B → (b-extract U (rar (mod ♭ A)))) → \ (x : C) → sec (h x))
            ( untranspose-ar A B (mod ♭ f)))
          ( concat ( ♭ ( ( ar C) → A))
            ( let mod ♭ sec := untranspose-ar A B (mod ♭ f) in transpose-ar A C (mod ♭ (\ (x : C) → sec (h x))))
            ( let mod ♭ f' := mod ♭ f in mod ♭ (\ (p : 𝕀 → C) → f' (\ i → h (p i))))
            ( mod ♭ (\ (p : 𝕀 → C) → f (\ i → h (p i))))
            ( transpose-untranspose-comp A B C h f)
            ( b-beta
              ( ( ar B) → A)
              ( ( ar C) → A)
              ( \ (f' : (ar B) → A) → \ (p : 𝕀 → C) → f' (\ i → h (p i)))
              ( f))))
        ( rev ( ♭ ( ( ar C) → A))
          ( transpose-ar A C (untranspose-ar A C (mod ♭ (\ (p : 𝕀 → C) → f (\ i → h (p i))))))
          ( mod ♭ (\ (p : 𝕀 → C) → f (\ i → h (p i))))
          ( transpose-untranspose-ar A C (mod ♭ (\ (p : 𝕀 → C) → f (\ i → h (p i)))))))

#def untranspose-naturality-left-rev
  ( A B C :♭ U)
  ( h :♭ C → B)
  ( f :♭ (ar B) → A)
  : untranspose-ar A C (mod ♭ (\ (p : 𝕀 → C) → f (\ i → h (p i))))
  = ( let mod ♭ sec := untranspose-ar A B (mod ♭ f) in mod ♭ (\ (x : C) → sec (h x)))
  :=
    rev
      ( ♭ ( C → b-extract U (rar (mod ♭ A))))
      ( let mod ♭ sec := untranspose-ar A B (mod ♭ f) in mod ♭ (\ (x : C) → sec (h x)))
      ( untranspose-ar A C (mod ♭ (\ (p : 𝕀 → C) → f (\ i → h (p i)))))
      ( untranspose-naturality-left A B C h f)

#def untranspose-naturality-left-flat (A B C :♭ U) (hh : ♭ (C → B)) (f :♭ (ar B) → A)
  : ( let mod ♭ sec := untranspose-ar A B (mod ♭ f) in let mod ♭ h := hh in mod ♭ (\ (x : C) → sec (h x)))
  = ( let mod ♭ h := hh in untranspose-ar A C (mod ♭ (\ (p : 𝕀 → C) → f (\ i → h (p i)))))
  := b-elim
       ( C → B)
       ( \ (z : ♭ (C → B)) → (let mod ♭ sec := untranspose-ar A B (mod ♭ f) in let mod ♭ h' := z in mod ♭ (\ (x : C) → sec (h' x))) = (let mod ♭ h' := z in untranspose-ar A C (mod ♭ (\ (p : 𝕀 → C) → f (\ i → h' (p i))))))
       ( hh)
       ( \ (h :_b C → B) → \ (e : mod ♭ h =_{♭ (C → B)} hh) → untranspose-naturality-left A B C h f)

#def untranspose-naturality-right-rev
  ( A B C :♭ U)
  ( f :♭ A → B)
  ( t :♭ (ar C) → A)
  : ( let mod ♭ fmap := rar-fmap A B f in
      let mod ♭ k := untranspose-ar A C (mod ♭ t) in
      mod ♭ (\ (x : C) → fmap (k x)))
    = untranspose-ar B C (mod ♭ (\ (p : 𝕀 → C) → f (t p)))
  :=
    concat ( ♭ ( C → b-extract U (rar (mod ♭ B))))
      ( let mod ♭ fmap := rar-fmap A B f in
        let mod ♭ k := untranspose-ar A C (mod ♭ t) in
        mod ♭ (\ (x : C) → fmap (k x)))
      ( let mod ♭ k := untranspose-ar A C (mod ♭ t) in
        untranspose-ar B C (mod ♭ (\ (p : 𝕀 → C) → f ((let mod ♭ eta := ar-rar-counit in eta) A (\ i → k (p i))))))
      ( untranspose-ar B C (mod ♭ (\ (p : 𝕀 → C) → f (t p))))
      ( untranspose-naturality-left-flat B (b-extract U (rar (mod ♭ A))) C
          ( untranspose-ar A C (mod ♭ t))
          ( \ (q : 𝕀 → b-extract U (rar (mod ♭ A))) → f ((let mod ♭ eta := ar-rar-counit in eta) A q)))
      ( concat ( ♭ ( C → b-extract U (rar (mod ♭ B))))
        ( let mod ♭ k := untranspose-ar A C (mod ♭ t) in
          untranspose-ar B C (mod ♭ (\ (p : 𝕀 → C) → f ((let mod ♭ eta := ar-rar-counit in eta) A (\ i → k (p i))))))
        ( untranspose-ar B C
            ( let mod ♭ k := untranspose-ar A C (mod ♭ t) in
              mod ♭ (\ (p : 𝕀 → C) → f ((let mod ♭ eta := ar-rar-counit in eta) A (\ i → k (p i))))))
        ( untranspose-ar B C (mod ♭ (\ (p : 𝕀 → C) → f (t p))))
        ( rev ( ♭ ( C → b-extract U (rar (mod ♭ B))))
          ( untranspose-ar B C
              ( let mod ♭ k := untranspose-ar A C (mod ♭ t) in
                mod ♭ (\ (p : 𝕀 → C) → f ((let mod ♭ eta := ar-rar-counit in eta) A (\ i → k (p i))))))
          ( let mod ♭ k := untranspose-ar A C (mod ♭ t) in
            untranspose-ar B C (mod ♭ (\ (p : 𝕀 → C) → f ((let mod ♭ eta := ar-rar-counit in eta) A (\ i → k (p i))))))
          ( b-naturality
              ( C → b-extract U (rar (mod ♭ A)))
              ( ( ar C) → B)
              ( C → b-extract U (rar (mod ♭ B)))
              ( untranspose-ar B C)
              ( \ (k : C → b-extract U (rar (mod ♭ A))) → \ (p : 𝕀 → C) → f ((let mod ♭ eta := ar-rar-counit in eta) A (\ i → k (p i))))
              ( untranspose-ar A C (mod ♭ t))))
        ( ap ( ♭ ( ( ar C) → B)) ( ♭ ( C → b-extract U (rar (mod ♭ B))))
          ( let mod ♭ k := untranspose-ar A C (mod ♭ t) in
            mod ♭ (\ (p : 𝕀 → C) → f ((let mod ♭ eta := ar-rar-counit in eta) A (\ i → k (p i)))))
          ( mod ♭ (\ (p : 𝕀 → C) → f (t p)))
          ( untranspose-ar B C)
          ( concat ( ♭ ( ( ar C) → B))
            ( let mod ♭ k := untranspose-ar A C (mod ♭ t) in
              mod ♭ (\ (p : 𝕀 → C) → f ((let mod ♭ eta := ar-rar-counit in eta) A (\ i → k (p i)))))
            ( b-map ( ( ar C) → A) ( ( ar C) → B)
                ( \ (m : (ar C) → A) → \ (p : ar C) → f (m p))
                ( transpose-ar A C (untranspose-ar A C (mod ♭ t))))
            ( mod ♭ (\ (p : 𝕀 → C) → f (t p)))
            ( rev ( ♭ ( ( ar C) → B))
              ( b-map ( ( ar C) → A) ( ( ar C) → B)
                  ( \ (m : (ar C) → A) → \ (p : ar C) → f (m p))
                  ( transpose-ar A C (untranspose-ar A C (mod ♭ t))))
              ( let mod ♭ k := untranspose-ar A C (mod ♭ t) in
                mod ♭ (\ (p : 𝕀 → C) → f ((let mod ♭ eta := ar-rar-counit in eta) A (\ i → k (p i)))))
              ( b-naturality
                  ( C → b-extract U (rar (mod ♭ A)))
                  ( ( ar C) → A)
                  ( ( ar C) → B)
                  ( b-map ( ( ar C) → A) ( ( ar C) → B) ( \ (m : (ar C) → A) → \ (p : ar C) → f (m p)))
                  ( \ (k : C → b-extract U (rar (mod ♭ A))) → \ (g : ar C) → (let mod ♭ eta := ar-rar-counit in eta) A (\ i → k (g i)))
                  ( untranspose-ar A C (mod ♭ t))))
            ( ap ( ♭ ( ( ar C) → A)) ( ♭ ( ( ar C) → B))
              ( transpose-ar A C (untranspose-ar A C (mod ♭ t)))
              ( mod ♭ t)
              ( b-map ( ( ar C) → A) ( ( ar C) → B) ( \ (m : (ar C) → A) → \ (p : ar C) → f (m p)))
              ( transpose-untranspose-ar A C (mod ♭ t))))))

#def untranspose-naturality-right
  ( A B C :♭ U)
  ( f :♭ A → B)
  ( t :♭ (ar C) → A)
  : untranspose-ar B C (mod ♭ (\ (p : 𝕀 → C) → f (t p)))
    = ( let mod ♭ fmap := rar-fmap A B f in
        let mod ♭ k := untranspose-ar A C (mod ♭ t) in
        mod ♭ (\ (x : C) → fmap (k x)))
  := rev
       ( ♭ ( C → b-extract U (rar (mod ♭ B))))
       ( let mod ♭ fmap := rar-fmap A B f in
         let mod ♭ k := untranspose-ar A C (mod ♭ t) in
         mod ♭ (\ (x : C) → fmap (k x)))
       ( untranspose-ar B C (mod ♭ (\ (p : 𝕀 → C) → f (t p))))
       ( untranspose-naturality-right-rev A B C f t)
```

## Counit

```rzk
#def ar-counit
  ( A :♭ U)
  : ar (b-extract U (rar (mod ♭ A))) → A
  := (let mod ♭ e := ar-rar-counit in e) A
```

## Cubes separate

GWB24, axiom 8
```rzk
#postulate cubes-separate (A B :♭ U) (f :♭ A → B)
  : iff (is-equiv A B f) ((n :♭ nat) → is-equiv (♭ (I^n n → A)) (♭ (I^n n → B)) (b-map (I^n n → A) (I^n n → B) (\ p t → f (p t))))
```

## Root preserves equivalences

```rzk
#def rar-preserves-is-equiv uses (funext)
  ( A B :♭ U)
  ( f :♭ A → B)
  ( ef :♭ is-equiv A B f)
  : is-equiv
      ( b-extract U (rar (mod ♭ A)))
      ( b-extract U (rar (mod ♭ B)))
      ( b-extract
          ( b-extract U (rar (mod ♭ A)) → b-extract U (rar (mod ♭ B)))
          ( rar-fmap A B f))
  :=
    b-b-elim
      ( b-extract U (rar (mod ♭ A)) → b-extract U (rar (mod ♭ B)))
      ( \ w → is-equiv (b-extract U (rar (mod ♭ A))) (b-extract U (rar (mod ♭ B)))
                ( b-extract (b-extract U (rar (mod ♭ A)) → b-extract U (rar (mod ♭ B))) w))
      ( rar-fmap A B f)
      ( \ (g :_b b-extract U (rar (mod ♭ A)) → b-extract U (rar (mod ♭ B)))
          ( e : ♭ (mod ♭ g =_{♭ (b-extract U (rar (mod ♭ A)) → b-extract U (rar (mod ♭ B)))} rar-fmap A B f)) →
          second
            ( cubes-separate
                ( b-extract U (rar (mod ♭ A)))
                ( b-extract U (rar (mod ♭ B)))
                ( g))
            ( \ n →
                is-equiv-b-map-via-splits
                  ( I^n n → b-extract U (rar (mod ♭ A)))
                  ( I^n n → b-extract U (rar (mod ♭ B)))
                  ( \ p t → g (p t))
                  ( ♭ (ar (I^n n) → A))
                  ( ♭ (ar (I^n n) → B))
                  ( transpose-ar-equiv A (I^n n))
                  ( transpose-ar-equiv B (I^n n))
                  ( b-equiv (ar (I^n n) → A) (ar (I^n n) → B)
                      ( \ m p → f (m p) , is-equiv-postcomp-is-equiv funext A B (ar (I^n n)) f ef))
                  ( \ a →
                      b-path-commute-fwd ( ar (I^n n) → B)
                        ( \ p → f (ar-counit A (\ i → a (p i))))
                        ( \ h → ar-counit B (\ i → g (a (h i))))
                        ( let mod ♭ e0 := e in
                          mod ♭
                            ( let key
                                : transpose-ar B (b-extract U (rar (mod ♭ A))) (mod ♭ g)
                                  =_{♭ (ar (b-extract U (rar (mod ♭ A))) → B)}
                                  ( mod ♭ (\ (p : ar (b-extract U (rar (mod ♭ A)))) → f (ar-counit A p)))
                                := concat ( ♭ (ar (b-extract U (rar (mod ♭ A))) → B))
                                     ( transpose-ar B (b-extract U (rar (mod ♭ A))) (mod ♭ g))
                                     ( transpose-ar B (b-extract U (rar (mod ♭ A))) (rar-fmap A B f))
                                     ( mod ♭ (\ p → f (ar-counit A p)))
                                     ( ap ( ♭ (b-extract U (rar (mod ♭ A)) → b-extract U (rar (mod ♭ B))))
                                          ( ♭ (ar (b-extract U (rar (mod ♭ A))) → B))
                                          ( mod ♭ g) (rar-fmap A B f)
                                          ( transpose-ar B (b-extract U (rar (mod ♭ A))))
                                          ( e0))
                                     ( transpose-untranspose-ar B (b-extract U (rar (mod ♭ A)))
                                         ( mod ♭ (\ p → f (ar-counit A p))))
                              in
                              let natptwise
                                : ( m : ar (b-extract U (rar (mod ♭ A))))
                                  → ar-counit B (\ i → g (m i)) = f (ar-counit A m)
                                := htpy-eq (ar (b-extract U (rar (mod ♭ A)))) (\ _ → B)
                                     ( \ h → ar-counit B (\ i → g (h i)))
                                     ( \ p → f (ar-counit A p))
                                     ( b-extract-eq (ar (b-extract U (rar (mod ♭ A))) → B)
                                         ( transpose-ar B (b-extract U (rar (mod ♭ A))) (mod ♭ g))
                                         ( mod ♭ (\ p → f (ar-counit A p)))
                                         ( key))
                              in
                              eq-htpy funext (ar (I^n n)) (\ _ → B)
                                ( \ p → f (ar-counit A (\ i → a (p i))))
                                ( \ h → ar-counit B (\ i → g (a (h i))))
                                ( \ p → rev B
                                    ( ar-counit B (\ i → g (a (p i))))
                                    ( f (ar-counit A (\ i → a (p i))))
                                    ( natptwise (\ i → a (p i)))))))))
```

## Root preserves embeddings

```rzk
#def is-emb-b-map-gf uses (funext)
  ( A B :♭ U)
  ( f :♭ A → B)
  ( emb-f :♭ is-emb A B f)
  ( n :♭ nat)
  ( g :_b b-extract U (rar (mod ♭ A)) → b-extract U (rar (mod ♭ B)))
  ( e : ♭ (mod ♭ g =_{♭ (b-extract U (rar (mod ♭ A)) → b-extract U (rar (mod ♭ B)))} rar-fmap A B f))
  : is-emb
      ( ♭ (I^n n → b-extract U (rar (mod ♭ A))))
      ( ♭ (I^n n → b-extract U (rar (mod ♭ B))))
      ( b-map (I^n n → b-extract U (rar (mod ♭ A))) (I^n n → b-extract U (rar (mod ♭ B)))
          ( \ p t → g (p t)))
  :=
          is-emb-right-factor-equiv
            ( ♭ (I^n n → b-extract U (rar (mod ♭ A))))
            ( ♭ (I^n n → b-extract U (rar (mod ♭ B))))
            ( ♭ (ar (I^n n) → B))
            ( b-map (I^n n → b-extract U (rar (mod ♭ A))) (I^n n → b-extract U (rar (mod ♭ B)))
                ( \ p t → g (p t)))
            ( first (transpose-ar-equiv B (I^n n)))
            ( second (transpose-ar-equiv B (I^n n)))
            ( transport
                ( ♭ (I^n n → b-extract U (rar (mod ♭ A))) → ♭ (ar (I^n n) → B))
                ( \ m → is-emb (♭ (I^n n → b-extract U (rar (mod ♭ A)))) (♭ (ar (I^n n) → B)) m)
                ( comp (♭ (I^n n → b-extract U (rar (mod ♭ A)))) (♭ (ar (I^n n) → A)) (♭ (ar (I^n n) → B))
                    ( b-map (ar (I^n n) → A) (ar (I^n n) → B) (\ m p → f (m p)))
                    ( first (transpose-ar-equiv A (I^n n))))
                ( comp (♭ (I^n n → b-extract U (rar (mod ♭ A)))) (♭ (I^n n → b-extract U (rar (mod ♭ B)))) (♭ (ar (I^n n) → B))
                    ( first (transpose-ar-equiv B (I^n n)))
                    ( b-map (I^n n → b-extract U (rar (mod ♭ A))) (I^n n → b-extract U (rar (mod ♭ B)))
                        ( \ p t → g (p t))))
                ( eq-htpy funext
                    ( ♭ (I^n n → b-extract U (rar (mod ♭ A))))
                    ( \ _ → ♭ (ar (I^n n) → B))
                    ( comp (♭ (I^n n → b-extract U (rar (mod ♭ A)))) (♭ (ar (I^n n) → A)) (♭ (ar (I^n n) → B))
                        ( b-map (ar (I^n n) → A) (ar (I^n n) → B) (\ m p → f (m p)))
                        ( first (transpose-ar-equiv A (I^n n))))
                    ( comp (♭ (I^n n → b-extract U (rar (mod ♭ A)))) (♭ (I^n n → b-extract U (rar (mod ♭ B)))) (♭ (ar (I^n n) → B))
                        ( first (transpose-ar-equiv B (I^n n)))
                        ( b-map (I^n n → b-extract U (rar (mod ♭ A))) (I^n n → b-extract U (rar (mod ♭ B)))
                            ( \ p t → g (p t))))
                    ( \ x →
                      b-elim (I^n n → b-extract U (rar (mod ♭ A)))
                        ( \ z →
                            b-map (ar (I^n n) → A) (ar (I^n n) → B) (\ m p → f (m p))
                              ( first (transpose-ar-equiv A (I^n n)) z)
                          = first (transpose-ar-equiv B (I^n n))
                              ( b-map (I^n n → b-extract U (rar (mod ♭ A))) (I^n n → b-extract U (rar (mod ♭ B)))
                                  ( \ p t → g (p t)) z))
                        ( x)
                        ( \ (a :_b I^n n → b-extract U (rar (mod ♭ A))) → \ _ →
                          b-path-commute-fwd ( ar (I^n n) → B)
                            ( \ p → f (ar-counit A (\ i → a (p i))))
                            ( \ h → ar-counit B (\ i → g (a (h i))))
                            ( let mod ♭ e0 := e in
                              mod ♭
                                ( let key
                                    : transpose-ar B (b-extract U (rar (mod ♭ A))) (mod ♭ g)
                                      =_{♭ (ar (b-extract U (rar (mod ♭ A))) → B)}
                                      ( mod ♭ (\ (p : ar (b-extract U (rar (mod ♭ A)))) → f (ar-counit A p)))
                                    := concat ( ♭ (ar (b-extract U (rar (mod ♭ A))) → B))
                                         ( transpose-ar B (b-extract U (rar (mod ♭ A))) (mod ♭ g))
                                         ( transpose-ar B (b-extract U (rar (mod ♭ A))) (rar-fmap A B f))
                                         ( mod ♭ (\ p → f (ar-counit A p)))
                                         ( ap ( ♭ (b-extract U (rar (mod ♭ A)) → b-extract U (rar (mod ♭ B))))
                                              ( ♭ (ar (b-extract U (rar (mod ♭ A))) → B))
                                              ( mod ♭ g) (rar-fmap A B f)
                                              ( transpose-ar B (b-extract U (rar (mod ♭ A))))
                                              ( e0))
                                         ( transpose-untranspose-ar B (b-extract U (rar (mod ♭ A)))
                                             ( mod ♭ (\ p → f (ar-counit A p))))
                                  in
                                  let natptwise
                                    : ( m : ar (b-extract U (rar (mod ♭ A))))
                                      → ar-counit B (\ i → g (m i)) = f (ar-counit A m)
                                    := htpy-eq (ar (b-extract U (rar (mod ♭ A)))) (\ _ → B)
                                         ( \ h → ar-counit B (\ i → g (h i)))
                                         ( \ p → f (ar-counit A p))
                                         ( b-extract-eq (ar (b-extract U (rar (mod ♭ A))) → B)
                                             ( transpose-ar B (b-extract U (rar (mod ♭ A))) (mod ♭ g))
                                             ( mod ♭ (\ p → f (ar-counit A p)))
                                             ( key))
                                  in
                                  eq-htpy funext (ar (I^n n)) (\ _ → B)
                                    ( \ p → f (ar-counit A (\ i → a (p i))))
                                    ( \ h → ar-counit B (\ i → g (a (h i))))
                                    ( \ p → rev B
                                        ( ar-counit B (\ i → g (a (p i))))
                                        ( f (ar-counit A (\ i → a (p i))))
                                        ( natptwise (\ i → a (p i)))))))))
                ( is-emb-comp
                    ( ♭ (I^n n → b-extract U (rar (mod ♭ A))))
                    ( ♭ (ar (I^n n) → A))
                    ( ♭ (ar (I^n n) → B))
                    ( first (transpose-ar-equiv A (I^n n)))
                    ( b-map (ar (I^n n) → A) (ar (I^n n) → B) (\ m p → f (m p)))
                    ( is-emb-is-equiv (♭ (I^n n → b-extract U (rar (mod ♭ A)))) (♭ (ar (I^n n) → A))
                        ( first (transpose-ar-equiv A (I^n n))) (second (transpose-ar-equiv A (I^n n))))
                    ( is-emb-b-map (ar (I^n n) → A) (ar (I^n n) → B) (\ m p → f (m p))
                        ( is-emb-postcomp funext (ar (I^n n)) A B f emb-f))))

#def is-equiv-emb-diagonal-rar uses (funext)
  ( A B :♭ U)
  ( f :♭ A → B)
  ( emb-f :♭ is-emb A B f)
  : is-equiv
      ( b-extract U (rar (mod ♭ A)))
      ( emb-pullback
          ( b-extract U (rar (mod ♭ A)))
          ( b-extract U (rar (mod ♭ B)))
          ( b-extract (b-extract U (rar (mod ♭ A)) → b-extract U (rar (mod ♭ B))) (rar-fmap A B f)))
      ( emb-diagonal
          ( b-extract U (rar (mod ♭ A)))
          ( b-extract U (rar (mod ♭ B)))
          ( b-extract (b-extract U (rar (mod ♭ A)) → b-extract U (rar (mod ♭ B))) (rar-fmap A B f)))
  :=
    b-b-elim
      ( b-extract U (rar (mod ♭ A)) → b-extract U (rar (mod ♭ B)))
      ( \ w → is-equiv
                ( b-extract U (rar (mod ♭ A)))
                ( emb-pullback (b-extract U (rar (mod ♭ A))) (b-extract U (rar (mod ♭ B)))
                    ( b-extract (b-extract U (rar (mod ♭ A)) → b-extract U (rar (mod ♭ B))) w))
                ( emb-diagonal (b-extract U (rar (mod ♭ A))) (b-extract U (rar (mod ♭ B)))
                    ( b-extract (b-extract U (rar (mod ♭ A)) → b-extract U (rar (mod ♭ B))) w)))
      ( rar-fmap A B f)
      ( \ (g :_b b-extract U (rar (mod ♭ A)) → b-extract U (rar (mod ♭ B)))
          ( e : ♭ (mod ♭ g =_{♭ (b-extract U (rar (mod ♭ A)) → b-extract U (rar (mod ♭ B)))} rar-fmap A B f)) →
          second
            ( cubes-separate
                ( b-extract U (rar (mod ♭ A)))
                ( emb-pullback (b-extract U (rar (mod ♭ A))) (b-extract U (rar (mod ♭ B))) g)
                ( emb-diagonal (b-extract U (rar (mod ♭ A))) (b-extract U (rar (mod ♭ B))) g))
            ( \ n →
                is-equiv-right-factor
                  ( ♭ (I^n n → b-extract U (rar (mod ♭ A))))
                  ( ♭ (I^n n → emb-pullback (b-extract U (rar (mod ♭ A))) (b-extract U (rar (mod ♭ B))) g))
                  ( emb-pullback (♭ (I^n n → b-extract U (rar (mod ♭ A)))) (♭ (I^n n → b-extract U (rar (mod ♭ B))))
                      ( b-map (I^n n → b-extract U (rar (mod ♭ A))) (I^n n → b-extract U (rar (mod ♭ B))) (\ c t → g (c t))))
                  ( b-map (I^n n → b-extract U (rar (mod ♭ A))) (I^n n → emb-pullback (b-extract U (rar (mod ♭ A))) (b-extract U (rar (mod ♭ B))) g)
                      ( \ p t → emb-diagonal (b-extract U (rar (mod ♭ A))) (b-extract U (rar (mod ♭ B))) g (p t)))
                  ( first
                      ( equiv-comp
                          ( ♭ (I^n n → emb-pullback (b-extract U (rar (mod ♭ A))) (b-extract U (rar (mod ♭ B))) g))
                          ( ♭ (emb-pullback (I^n n → b-extract U (rar (mod ♭ A))) (I^n n → b-extract U (rar (mod ♭ B))) (\ c t → g (c t))))
                          ( emb-pullback (♭ (I^n n → b-extract U (rar (mod ♭ A)))) (♭ (I^n n → b-extract U (rar (mod ♭ B))))
                              ( b-map (I^n n → b-extract U (rar (mod ♭ A))) (I^n n → b-extract U (rar (mod ♭ B))) (\ c t → g (c t))))
                          ( b-equiv (I^n n → emb-pullback (b-extract U (rar (mod ♭ A))) (b-extract U (rar (mod ♭ B))) g)
                              ( emb-pullback (I^n n → b-extract U (rar (mod ♭ A))) (I^n n → b-extract U (rar (mod ♭ B))) (\ c t → g (c t)))
                              ( equiv-pullback-postcomp funext (I^n n) (b-extract U (rar (mod ♭ A))) (b-extract U (rar (mod ♭ B))) g))
                          ( equiv-flat-emb-pullback (I^n n → b-extract U (rar (mod ♭ A))) (I^n n → b-extract U (rar (mod ♭ B))) (\ c t → g (c t)))))
                  ( second
                      ( equiv-comp
                          ( ♭ (I^n n → emb-pullback (b-extract U (rar (mod ♭ A))) (b-extract U (rar (mod ♭ B))) g))
                          ( ♭ (emb-pullback (I^n n → b-extract U (rar (mod ♭ A))) (I^n n → b-extract U (rar (mod ♭ B))) (\ c t → g (c t))))
                          ( emb-pullback (♭ (I^n n → b-extract U (rar (mod ♭ A)))) (♭ (I^n n → b-extract U (rar (mod ♭ B))))
                              ( b-map (I^n n → b-extract U (rar (mod ♭ A))) (I^n n → b-extract U (rar (mod ♭ B))) (\ c t → g (c t))))
                          ( b-equiv (I^n n → emb-pullback (b-extract U (rar (mod ♭ A))) (b-extract U (rar (mod ♭ B))) g)
                              ( emb-pullback (I^n n → b-extract U (rar (mod ♭ A))) (I^n n → b-extract U (rar (mod ♭ B))) (\ c t → g (c t)))
                              ( equiv-pullback-postcomp funext (I^n n) (b-extract U (rar (mod ♭ A))) (b-extract U (rar (mod ♭ B))) g))
                          ( equiv-flat-emb-pullback (I^n n → b-extract U (rar (mod ♭ A))) (I^n n → b-extract U (rar (mod ♭ B))) (\ c t → g (c t)))))
                  ( is-equiv-homotopy
                      ( ♭ (I^n n → b-extract U (rar (mod ♭ A))))
                      ( emb-pullback (♭ (I^n n → b-extract U (rar (mod ♭ A)))) (♭ (I^n n → b-extract U (rar (mod ♭ B))))
                          ( b-map (I^n n → b-extract U (rar (mod ♭ A))) (I^n n → b-extract U (rar (mod ♭ B))) (\ c t → g (c t))))
                      ( comp
                          ( ♭ (I^n n → b-extract U (rar (mod ♭ A))))
                          ( ♭ (I^n n → emb-pullback (b-extract U (rar (mod ♭ A))) (b-extract U (rar (mod ♭ B))) g))
                          ( emb-pullback (♭ (I^n n → b-extract U (rar (mod ♭ A)))) (♭ (I^n n → b-extract U (rar (mod ♭ B))))
                              ( b-map (I^n n → b-extract U (rar (mod ♭ A))) (I^n n → b-extract U (rar (mod ♭ B))) (\ c t → g (c t))))
                          ( first
                              ( equiv-comp
                                  ( ♭ (I^n n → emb-pullback (b-extract U (rar (mod ♭ A))) (b-extract U (rar (mod ♭ B))) g))
                                  ( ♭ (emb-pullback (I^n n → b-extract U (rar (mod ♭ A))) (I^n n → b-extract U (rar (mod ♭ B))) (\ c t → g (c t))))
                                  ( emb-pullback (♭ (I^n n → b-extract U (rar (mod ♭ A)))) (♭ (I^n n → b-extract U (rar (mod ♭ B))))
                                      ( b-map (I^n n → b-extract U (rar (mod ♭ A))) (I^n n → b-extract U (rar (mod ♭ B))) (\ c t → g (c t))))
                                  ( b-equiv (I^n n → emb-pullback (b-extract U (rar (mod ♭ A))) (b-extract U (rar (mod ♭ B))) g)
                                      ( emb-pullback (I^n n → b-extract U (rar (mod ♭ A))) (I^n n → b-extract U (rar (mod ♭ B))) (\ c t → g (c t)))
                                      ( equiv-pullback-postcomp funext (I^n n) (b-extract U (rar (mod ♭ A))) (b-extract U (rar (mod ♭ B))) g))
                                  ( equiv-flat-emb-pullback (I^n n → b-extract U (rar (mod ♭ A))) (I^n n → b-extract U (rar (mod ♭ B))) (\ c t → g (c t)))))
                          ( b-map (I^n n → b-extract U (rar (mod ♭ A))) (I^n n → emb-pullback (b-extract U (rar (mod ♭ A))) (b-extract U (rar (mod ♭ B))) g)
                              ( \ p t → emb-diagonal (b-extract U (rar (mod ♭ A))) (b-extract U (rar (mod ♭ B))) g (p t))))
                      ( emb-diagonal (♭ (I^n n → b-extract U (rar (mod ♭ A)))) (♭ (I^n n → b-extract U (rar (mod ♭ B))))
                          ( b-map (I^n n → b-extract U (rar (mod ♭ A))) (I^n n → b-extract U (rar (mod ♭ B))) (\ c t → g (c t))))
                      ( \ a →
                        b-elim ( I^n n → b-extract U (rar (mod ♭ A)))
                          ( \ z →
                              comp
                                ( ♭ (I^n n → b-extract U (rar (mod ♭ A))))
                                ( ♭ (I^n n → emb-pullback (b-extract U (rar (mod ♭ A))) (b-extract U (rar (mod ♭ B))) g))
                                ( emb-pullback (♭ (I^n n → b-extract U (rar (mod ♭ A)))) (♭ (I^n n → b-extract U (rar (mod ♭ B))))
                                    ( b-map (I^n n → b-extract U (rar (mod ♭ A))) (I^n n → b-extract U (rar (mod ♭ B))) (\ c t → g (c t))))
                                ( first
                                    ( equiv-comp
                                        ( ♭ (I^n n → emb-pullback (b-extract U (rar (mod ♭ A))) (b-extract U (rar (mod ♭ B))) g))
                                        ( ♭ (emb-pullback (I^n n → b-extract U (rar (mod ♭ A))) (I^n n → b-extract U (rar (mod ♭ B))) (\ c t → g (c t))))
                                        ( emb-pullback (♭ (I^n n → b-extract U (rar (mod ♭ A)))) (♭ (I^n n → b-extract U (rar (mod ♭ B))))
                                            ( b-map (I^n n → b-extract U (rar (mod ♭ A))) (I^n n → b-extract U (rar (mod ♭ B))) (\ c t → g (c t))))
                                        ( b-equiv (I^n n → emb-pullback (b-extract U (rar (mod ♭ A))) (b-extract U (rar (mod ♭ B))) g)
                                            ( emb-pullback (I^n n → b-extract U (rar (mod ♭ A))) (I^n n → b-extract U (rar (mod ♭ B))) (\ c t → g (c t)))
                                            ( equiv-pullback-postcomp funext (I^n n) (b-extract U (rar (mod ♭ A))) (b-extract U (rar (mod ♭ B))) g))
                                        ( equiv-flat-emb-pullback (I^n n → b-extract U (rar (mod ♭ A))) (I^n n → b-extract U (rar (mod ♭ B))) (\ c t → g (c t)))))
                                ( b-map (I^n n → b-extract U (rar (mod ♭ A))) (I^n n → emb-pullback (b-extract U (rar (mod ♭ A))) (b-extract U (rar (mod ♭ B))) g)
                                    ( \ p t → emb-diagonal (b-extract U (rar (mod ♭ A))) (b-extract U (rar (mod ♭ B))) g (p t)))
                                ( z)
                            =_{ emb-pullback (♭ (I^n n → b-extract U (rar (mod ♭ A)))) (♭ (I^n n → b-extract U (rar (mod ♭ B)))) (b-map (I^n n → b-extract U (rar (mod ♭ A))) (I^n n → b-extract U (rar (mod ♭ B))) (\ c t → g (c t))) }
                              emb-diagonal (♭ (I^n n → b-extract U (rar (mod ♭ A)))) (♭ (I^n n → b-extract U (rar (mod ♭ B))))
                                ( b-map (I^n n → b-extract U (rar (mod ♭ A))) (I^n n → b-extract U (rar (mod ♭ B))) (\ c t → g (c t)))
                                ( z))
                          ( a)
                          ( \ (c :_b I^n n → b-extract U (rar (mod ♭ A))) → \ _ →
                            ap
                              ( mod ♭ (\ (t : I^n n) → g (c t)) = mod ♭ (\ (t : I^n n) → g (c t)))
                              ( emb-pullback (♭ (I^n n → b-extract U (rar (mod ♭ A)))) (♭ (I^n n → b-extract U (rar (mod ♭ B))))
                                  ( b-map (I^n n → b-extract U (rar (mod ♭ A))) (I^n n → b-extract U (rar (mod ♭ B))) (\ c₁ t → g (c₁ t))))
                              ( b-path-commute-fwd (I^n n → b-extract U (rar (mod ♭ B)))
                                  ( \ (t : I^n n) → g (c t)) (\ (t : I^n n) → g (c t))
                                  ( mod ♭ (first (second (funext (I^n n) (\ _ → b-extract U (rar (mod ♭ B))) (\ (t : I^n n) → g (c t)) (\ (t : I^n n) → g (c t)))) (\ w → refl))))
                              ( refl)
                              ( \ p → (mod ♭ c , (mod ♭ c , p)))
                              ( concat
                                  ( mod ♭ (\ (t : I^n n) → g (c t)) = mod ♭ (\ (t : I^n n) → g (c t)))
                                  ( b-path-commute-fwd (I^n n → b-extract U (rar (mod ♭ B)))
                                      ( \ (t : I^n n) → g (c t)) (\ (t : I^n n) → g (c t))
                                      ( mod ♭ (first (second (funext (I^n n) (\ _ → b-extract U (rar (mod ♭ B))) (\ (t : I^n n) → g (c t)) (\ (t : I^n n) → g (c t)))) (\ w → refl))))
                                  ( b-path-commute-fwd (I^n n → b-extract U (rar (mod ♭ B)))
                                      ( \ (t : I^n n) → g (c t)) (\ (t : I^n n) → g (c t)) (mod ♭ refl))
                                  ( refl)
                                  ( ap
                                      ( ♭ ((\ (t : I^n n) → g (c t)) = (\ (t : I^n n) → g (c t))))
                                      ( mod ♭ (\ (t : I^n n) → g (c t)) = mod ♭ (\ (t : I^n n) → g (c t)))
                                      ( mod ♭ (first (second (funext (I^n n) (\ _ → b-extract U (rar (mod ♭ B))) (\ (t : I^n n) → g (c t)) (\ (t : I^n n) → g (c t)))) (\ w → refl)))
                                      ( mod ♭ refl)
                                      ( b-path-commute-fwd (I^n n → b-extract U (rar (mod ♭ B))) (\ (t : I^n n) → g (c t)) (\ (t : I^n n) → g (c t)))
                                      ( b-path-commute-fwd ((\ (t : I^n n) → g (c t)) = (\ (t : I^n n) → g (c t)))
                                          ( first (second (funext (I^n n) (\ _ → b-extract U (rar (mod ♭ B))) (\ (t : I^n n) → g (c t)) (\ (t : I^n n) → g (c t)))) (\ w → refl))
                                          ( refl)
                                          ( mod ♭ (section-htpy-eq-refl funext (I^n n) (\ _ → b-extract U (rar (mod ♭ B))) (\ (t : I^n n) → g (c t))))))
                                  ( b-path-commute-fwd-refl (I^n n → b-extract U (rar (mod ♭ B))) (\ (t : I^n n) → g (c t))))))
                      ( is-equiv-emb-diagonal-is-emb
                          ( ♭ (I^n n → b-extract U (rar (mod ♭ A))))
                          ( ♭ (I^n n → b-extract U (rar (mod ♭ B))))
                          ( b-map (I^n n → b-extract U (rar (mod ♭ A))) (I^n n → b-extract U (rar (mod ♭ B))) (\ c t → g (c t)))
                          ( is-emb-b-map-gf A B f emb-f n g e)))))

#def rar-preserves-is-emb uses (funext)
  ( A B :♭ U)
  ( f :♭ A → B)
  ( emb-f :♭ is-emb A B f)
  : is-emb
      ( b-extract U (rar (mod ♭ A)))
      ( b-extract U (rar (mod ♭ B)))
      ( b-extract
          ( b-extract U (rar (mod ♭ A)) → b-extract U (rar (mod ♭ B)))
          ( rar-fmap A B f))
  :=
    is-emb-is-equiv-emb-diagonal
      ( b-extract U (rar (mod ♭ A)))
      ( b-extract U (rar (mod ♭ B)))
      ( b-extract (b-extract U (rar (mod ♭ A)) → b-extract U (rar (mod ♭ B))) (rar-fmap A B f))
      ( is-equiv-emb-diagonal-rar A B f emb-f)
```
