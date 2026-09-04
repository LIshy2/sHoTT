# 5. Directed univalence

This is a literate `rzk` file:

```rzk
#lang rzk-1

#assume funext : FunExt
#assume weakfunext : WeakFunExt
#assume extext : ExtExt
```

## Prerequisites

- `hott/**` — `ap`, `rev`, `concat`, `transport`, `Equiv`, `is-equiv`, `eq-pair`, `total-map`, etc.
- `simplicial-hott/**` — extension types, right-orthogonality, discreteness.
- `hott/04-modalities.rzk.md` — modalities, `Prop-b`, `univ-family-Prop-b`.
- `triangulated/01`–`02` — tiny interval, internal universe.
- `triangulated/04-amazing-covariant.rzk.md` — `is-covariant-arrow-II`, `is-covariant-arrow-II-Prop`, `amazing-covariant-uniqueness-line-II`, `is-a-cov`, `is-a-cov-sigma-closed`, `is-a-cov-fib`, `is-a-cov-ext`, `is-a-cov-i===0`, `is-prop-is-a-cov`.

## S and its morphisms

`S` is the type of amazingly-covariant types; a map `𝕀 → S` is a morphism.

```rzk

#def S uses (funext weakfunext)
  : U
  := Σ (A : U) , (is-a-cov funext weakfunext) A

#def S-b uses (funext weakfunext)
  : ( ♭ U)
  := mod ♭ S

#def s-is-covariant-arrow-II uses (funext weakfunext)
  ( f : 𝕀 → S)
  : is-covariant-arrow-II (\ (t : 𝕀 | TOP) → first (f t))
  :=
    b-extract
      ( ( f : 𝕀 → S) → is-covariant-arrow-II (\ (t : 𝕀 | TOP) → first (f t)))
      ( amazing-transpose funext weakfunext
        ( is-covariant-arrow-II-Prop funext weakfunext)
        ( S)
        ( ( \ s → first s))
        ( ( \ s → second s)))
    f

-- Lemma 6.12
#def mor2fun uses (funext weakfunext) (f : 𝕀 → S)
  : Σ ( A : S) , (Σ (B : S) , (first A) → (first B))
  :=
  ( f 0₂ , (f 1₂ , covariant-transport-line-II
      ( \ (t : 𝕀 | TOP) → first (f t))
      ( s-is-covariant-arrow-II f)
      ( \ k → form k)))
```

## dirglue

```rzk

#def dirglue-is-acov uses (funext weakfunext extext) (A B : S) (f : (first A) → (first B)) (i : 𝕀)
  : ( is-a-cov funext weakfunext) (
    Σ ( b : (first B))
  , ( ( t : 1 | i ≡ 0₂) → fib (first A) (first B) f b)
  )
  :=
    is-a-cov-sigma-closed funext weakfunext
      ( first B)
      ( \ b → (t : 1 | i ≡ 0₂) → fib (first A) (first B) f b)
      ( second B)
      ( \ b →
          let mod ᵒᵖ flip_i := flipᵒᵖ i in
            is-a-cov-ext funext weakfunext extext
              ( mod ᵒᵖ (flip_i ≡ 1₂))
              ( mod ᵒᵖ (is-a-cov-i===0 funext weakfunext extext flip_i))
              ( fib (first A) (first B) f b)
              ( is-a-cov-fib funext weakfunext
                  ( first A) (first B)
                  ( second A) (second B)
                  ( f) (b)))


-- Gwb, Definition 6.14
#def dirglue uses (funext weakfunext extext) (A B : S) (f : (first A) → (first B))
  : 𝕀 → S
  :=
    \ i →
      ( Σ ( b : (first B))
      , ( ( t : 1 | i ≡ 0₂) → fib (first A) (first B) f b)
    , dirglue-is-acov A B f i)
```

First part of equivalence mor2fun (dirglue f) is f.

```rzk
#def dirglue-equiv-0 uses (funext weakfunext extext) (A B : S) (f : (first A) → (first B))
  : Equiv (first (dirglue A B f 0₂)) (first A)
  := equiv-comp
       ( first (dirglue A B f 0₂))
       ( total-type (first B) (fib (first A) (first B) f))
       ( first A)
       ( total-equiv-family-of-equiv
           ( first B)
           ( \ b → (t : 1 | 0₂ ≡ 0₂) → fib (first A) (first B) f b)
           ( fib (first A) (first B) f)
           ( \ b → equiv-extent-0 (fib (first A) (first B) f b)))
       ( ( \ (_ , (a , _)) → a)
       , is-equiv-domain-sum-of-fibers (first A) (first B) f)

#def dirglue_0=A uses (funext weakfunext extext) (A B : S) (f : (first A) → (first B))
  : dirglue A B f 0₂ = A
  :=
    eq-pair-equiv
      ( is-a-cov funext weakfunext)
      ( dirglue A B f 0₂)
      ( A)
      ( dirglue-equiv-0 A B f)
      ( first
        ( is-prop-is-a-cov funext weakfunext (first A)
          ( transport U (is-a-cov funext weakfunext)
              ( first (dirglue A B f 0₂)) (first A)
              ( first (ua (first (dirglue A B f 0₂)) (first A)) (dirglue-equiv-0 A B f))
              ( second (dirglue A B f 0₂)))
          ( second A)))

#def dirglue-equiv-1 uses (funext weakfunext extext) (A B : S) (f : (first A) → (first B))
  : Equiv (first (dirglue A B f 1₂)) (first B)
  := equiv-total-type-is-contr-fiber
       ( first B)
       ( \ b → (t : 1 | 1₂ ≡ 0₂) → fib (first A) (first B) f b)
       ( \ b → is-contr-extent-1 extext (fib (first A) (first B) f b))

#def dirglue_1=B uses (funext weakfunext extext) (A B : S) (f : (first A) → (first B))
  : dirglue A B f 1₂ = B
  :=
    eq-pair-equiv
      ( is-a-cov funext weakfunext)
      ( dirglue A B f 1₂)
      ( B)
      ( dirglue-equiv-1 A B f)
      ( first
        ( is-prop-is-a-cov funext weakfunext (first B)
          ( transport U (is-a-cov funext weakfunext)
              ( first (dirglue A B f 1₂)) (first B)
              ( first (ua (first (dirglue A B f 1₂)) (first B)) (dirglue-equiv-1 A B f))
              ( second (dirglue A B f 1₂)))
          ( second B)))

#def coe-dirglue-is-f-pointwise uses (funext weakfunext extext)
  ( A B : S) (f : (first A) → (first B))
  ( a : first A)
  : transport S (\ s → first s) (dirglue A B f 1₂) B (dirglue_1=B A B f)
      ( covariant-transport-line-II (\ (t : 𝕀 | TOP) → first (dirglue A B f t)) (s-is-covariant-arrow-II (dirglue A B f)) (\ k → form k)
          ( transport-rev S (\ s → first s) (dirglue A B f 0₂) A (dirglue_0=A A B f) a))
    = f a
  :=
    let coe-dirglue : first (dirglue A B f 0₂) → first (dirglue A B f 1₂)
      := covariant-transport-line-II (\ (t : 𝕀 | TOP) → first (dirglue A B f t)) (s-is-covariant-arrow-II (dirglue A B f)) (\ k → form k) in
    let a-in-dirglue-0 : first (dirglue A B f 0₂)
      := transport-rev S (\ s → first s) (dirglue A B f 0₂) A (dirglue_0=A A B f) a in
    let base-is-f-a : first a-in-dirglue-0 = f a
      := concat (first B)
           ( first a-in-dirglue-0)
           ( f (first (dirglue-equiv-0 A B f) a-in-dirglue-0))
           ( f a)
           -- first a-in-dirglue-0 = f (dirglue-equiv-0 a-in-dirglue-0)
           ( rev (first B) (f (first (dirglue-equiv-0 A B f) a-in-dirglue-0)) (first a-in-dirglue-0)
               ( second ((second a-in-dirglue-0) *₁)))
           -- f (dirglue-equiv-0 a-in-dirglue-0) = f a
           ( ap (first A) (first B) (first (dirglue-equiv-0 A B f) a-in-dirglue-0) a f
               ( concat (first A)
                   ( first (dirglue-equiv-0 A B f) a-in-dirglue-0)
                   ( transport S (\ s → first s) (dirglue A B f 0₂) A (dirglue_0=A A B f) a-in-dirglue-0)
                   ( a)
                   -- dirglue-equiv-0 a-in-dirglue-0 = transport (dirglue_0=A) a-in-dirglue-0
                   ( rev (first A)
                       ( transport S (\ s → first s) (dirglue A B f 0₂) A (dirglue_0=A A B f) a-in-dirglue-0)
                       ( first (dirglue-equiv-0 A B f) a-in-dirglue-0)
                       ( transport-first-eq-pair-equiv
                           ( is-a-cov funext weakfunext)
                           ( dirglue A B f 0₂)
                           ( A)
                           ( dirglue-equiv-0 A B f)
                           ( first
                             ( is-prop-is-a-cov funext weakfunext (first A)
                               ( transport U (is-a-cov funext weakfunext)
                                   ( first (dirglue A B f 0₂)) (first A)
                                   ( first (ua (first (dirglue A B f 0₂)) (first A)) (dirglue-equiv-0 A B f))
                                   ( second (dirglue A B f 0₂)))
                               ( second A)))
                           ( a-in-dirglue-0)))
                   -- transport (dirglue_0=A) a-in-dirglue-0 = a
                   ( transport-transport-rev S (\ s → first s)
                       ( dirglue A B f 0₂) A (dirglue_0=A A B f) a))) in
    concat (first B)
      ( transport S (\ s → first s) (dirglue A B f 1₂) B (dirglue_1=B A B f) (coe-dirglue a-in-dirglue-0))
      ( first a-in-dirglue-0)
      ( f a)
      -- transport (dirglue_1=B) (coe-dirglue a-in-dirglue-0) = first a-in-dirglue-0
      ( concat (first B)
          ( transport S (\ s → first s) (dirglue A B f 1₂) B (dirglue_1=B A B f) (coe-dirglue a-in-dirglue-0))
          ( first (coe-dirglue a-in-dirglue-0))
          ( first a-in-dirglue-0)
          -- transport (dirglue_1=B) (coe-dirglue a-in-dirglue-0) = first (coe-dirglue a-in-dirglue-0)
          ( transport-first-eq-pair-equiv
              ( is-a-cov funext weakfunext)
              ( dirglue A B f 1₂)
              ( B)
              ( dirglue-equiv-1 A B f)
              ( first
                ( is-prop-is-a-cov funext weakfunext (first B)
                  ( transport U (is-a-cov funext weakfunext)
                      ( first (dirglue A B f 1₂)) (first B)
                      ( first (ua (first (dirglue A B f 1₂)) (first B)) (dirglue-equiv-1 A B f))
                      ( second (dirglue A B f 1₂)))
                  ( second B)))
              ( coe-dirglue a-in-dirglue-0))
          -- first (coe-dirglue a-in-dirglue-0) = first a-in-dirglue-0
          ( ap (first (dirglue A B f 1₂)) (first B) (coe-dirglue a-in-dirglue-0) (first a-in-dirglue-0 , second a-in-dirglue-0)
              ( \ z → first z)
              ( amazing-covariant-uniqueness-line-II (\ (t : 𝕀 | TOP) → first (dirglue A B f t)) (s-is-covariant-arrow-II (dirglue A B f))
                  ( a-in-dirglue-0) (first a-in-dirglue-0 , second a-in-dirglue-0) (\ (t : 𝕀) → (first a-in-dirglue-0 , second a-in-dirglue-0)))))
      ( base-is-f-a)


-- GWB, Lemma 6.15
#def coe-dirglue-is-f uses (funext weakfunext extext)
  ( A B : S) (f : (first A) → (first B))
  : product-transport S S (\ X Y → (first X) → (first Y))
      ( dirglue A B f 0₂) A
      ( dirglue A B f 1₂) B
      ( dirglue_0=A A B f) (dirglue_1=B A B f)
      ( covariant-transport-line-II (\ (t : 𝕀 | TOP) → first (dirglue A B f t)) (s-is-covariant-arrow-II (dirglue A B f)) (\ k → form k))
    = f
  :=
    let coe-dirglue : first (dirglue A B f 0₂) → first (dirglue A B f 1₂)
      := covariant-transport-line-II (\ (t : 𝕀 | TOP) → first (dirglue A B f t)) (s-is-covariant-arrow-II (dirglue A B f)) (\ k → form k) in
    let coe-dirglue-transported : (first A) → (first B)
      := \ (a : first A) →
         transport S (\ s → first s) (dirglue A B f 1₂) B (dirglue_1=B A B f)
           ( coe-dirglue (transport-rev S (\ s → first s) (dirglue A B f 0₂) A (dirglue_0=A A B f) a)) in
    concat ((first A) → (first B))
      ( product-transport S S (\ X Y → (first X) → (first Y))
          ( dirglue A B f 0₂) A (dirglue A B f 1₂) B
          ( dirglue_0=A A B f) (dirglue_1=B A B f) coe-dirglue)
      ( coe-dirglue-transported)
      ( f)
      -- product-transport (dirglue_0=A) (dirglue_1=B) coe-dirglue = coe-dirglue-transported
      ( product-transport-fun S (\ s → first s)
          ( dirglue A B f 0₂) A (dirglue A B f 1₂) B
          ( dirglue_0=A A B f) (dirglue_1=B A B f) coe-dirglue)
      -- coe-dirglue-transported = f
      ( eq-htpy funext (first A) (\ _ → first B)
          coe-dirglue-transported f (coe-dirglue-is-f-pointwise A B f))


#def mor2fun-dirglue=f uses (funext weakfunext extext) (A B : S) (f : (first A) → (first B))
  : mor2fun (dirglue A B f) = (A , (B , f))
  :=
    eq-triple S S (\ X Y → (first X) → (first Y))
      ( mor2fun (dirglue A B f))
      ( A , (B , f))
      ( dirglue_0=A A B f , (dirglue_1=B A B f , (coe-dirglue-is-f A B f)))

-- Lemma 6.8
#def is-equiv-amazing-covariant-from-endpoints uses (funext weakfunext extext) (f g : 𝕀 → S) (a : (i : 𝕀) → first (f i) → first (g i))
  : ( is-equiv (first (f 0₂)) (first (g 0₂)) (a 0₂)) → (is-equiv (first (f 1₂)) (first (g 1₂)) (a 1₂))
    → ( ( i : 𝕀) → (is-equiv (first (f i)) (first (g i)) (a i)))
  :=
    let mod ♭ X := mod ♭ (Σ (F : 𝕀 → S) , Σ (G : 𝕀 → S) , Σ (alpha : (theta : 𝕀) → first (F theta) → first (G theta)) , Σ (equiv-0 : is-equiv (first (F 0₂)) (first (G 0₂)) (alpha 0₂)) , (is-equiv (first (F 1₂)) (first (G 1₂)) (alpha 1₂))) in
    let mod ♭ Y := mod ♭ (Σ (F : 𝕀 → S) , Σ (G : 𝕀 → S) , Σ (alpha : (theta : 𝕀) → first (F theta) → first (G theta)) , (theta : 𝕀) → is-equiv (first (F theta)) (first (G theta)) (alpha theta)) in
    let mod ♭ Y-to-X : Y → X := mod ♭ (\ (F , (G , (alpha , pequiv))) → (F , (G , (alpha , (pequiv 0₂ , pequiv 1₂))))) in
    let Y-to-X-is-equiv : is-equiv Y X Y-to-X :=
      second (cubes-separate Y X Y-to-X) (\ n →
        let mod ♭ Gamma := mod ♭ ((I^n n)) in
        let mod ♭ Gamma' := mod ♭ (product (I^n n) (shape (_ : 𝕀 | TOP))) in
        let mod ♭ Hom-in-S := mod ♭ (\ (F : Gamma' → S) → \ (G : Gamma' → S) → (((v , i) : Gamma') → first (F (v , i)) → first (G (v , i)))) in
        let mod ♭ E-X := mod ♭ (\ (F : Gamma' → S) → \ (G : Gamma' → S) → \ (alpha : Hom-in-S F G) →
          ( ( v : I^n n) → product
              ( is-equiv (first (F (v , form 0₂))) (first (G (v , form 0₂))) (alpha (v , form 0₂)))
              ( is-equiv (first (F (v , form 1₂))) (first (G (v , form 1₂))) (alpha (v , form 1₂))))) in
        let mod ♭ E-Y := mod ♭ (\ (F : Gamma' → S) → \ (G : Gamma' → S) → \ (alpha : Hom-in-S F G) →
          ( ( ( v , i) : product (I^n n) (shape (_ : 𝕀 | TOP))) → is-equiv (first (F (v , i))) (first (G (v , i))) (alpha (v , i)))) in
        let mod ♭ X-cube :=
          mod ♭ (Σ (F : Gamma' → S) , Σ (G : Gamma' → S) , Σ (alpha : Hom-in-S F G) , E-X F G alpha) in
        let mod ♭ Y-cube :=
          mod ♭ (Σ (F : Gamma' → S) , Σ (G : Gamma' → S) , Σ (alpha : Hom-in-S F G) , E-Y F G alpha) in
        let mod ♭ X-split :=
          mod ♭ (Σ (F : ♭ (Gamma' → S))
          , ( let mod ♭ F0 := F in
              Σ ( G : ♭ (Gamma' → S))
              , ( let mod ♭ G0 := G in
                  Σ ( alpha : ♭ (Hom-in-S F0 G0))
                  , ( let mod ♭ a0 := alpha in ♭ (E-X F0 G0 a0))))) in
        let mod ♭ Y-split :=
          mod ♭ (Σ (F : ♭ (Gamma' → S))
          , ( let mod ♭ F0 := F in
              Σ ( G : ♭ (Gamma' → S))
              , ( let mod ♭ G0 := G in
                  Σ ( alpha : ♭ (Hom-in-S F0 G0))
                  , ( let mod ♭ a0 := alpha in ♭ (E-Y F0 G0 a0))))) in
        let mod ♭ E-Y-is-prop
 : ( F : Gamma' → S) → (G : Gamma' → S) → (alpha : Hom-in-S F G) → is-prop (E-Y F G alpha)
          :=
            mod ♭ (\ F G alpha →
              is-prop-fiberwise-prop funext Gamma'
                ( \ (v , i) → is-equiv (first (F (v , i))) (first (G (v , i))) (alpha (v , i)))
                ( \ (v , i) → is-prop-is-equiv funext (first (F (v , i))) (first (G (v , i))) (alpha (v , i)))) in
        let mod ♭ E-X-is-prop
 : ( F : Gamma' → S) → (G : Gamma' → S) → (alpha : Hom-in-S F G) → is-prop (E-X F G alpha)
          :=
            mod ♭ (\ F G alpha →
              is-prop-fiberwise-prop funext (I^n n)
                ( \ v → product
                    ( is-equiv (first (F (v , form 0₂))) (first (G (v , form 0₂))) (alpha (v , form 0₂)))
                    ( is-equiv (first (F (v , form 1₂))) (first (G (v , form 1₂))) (alpha (v , form 1₂))))
                ( \ v → is-prop-total-type-is-fiberwise-prop-is-prop-base
                    ( is-equiv (first (F (v , form 0₂))) (first (G (v , form 0₂))) (alpha (v , form 0₂)))
                    ( is-prop-is-equiv funext (first (F (v , form 0₂))) (first (G (v , form 0₂))) (alpha (v , form 0₂)))
                    ( \ _ → is-equiv (first (F (v , form 1₂))) (first (G (v , form 1₂))) (alpha (v , form 1₂)))
                    ( \ _ → is-prop-is-equiv funext (first (F (v , form 1₂))) (first (G (v , form 1₂))) (alpha (v , form 1₂))))) in
        let to-X-split : Equiv (♭ (I^n n → X)) X-split :=
          let mod ♭ X-uncurried :=
            mod ♭ (Σ (fa : (v : I^n n) → 𝕀 → S)
            , Σ ( fb : (v : I^n n) → 𝕀 → S)
            , Σ ( fc : (v : I^n n) → ((i : 𝕀) → first (fa v i) → first (fb v i)))
            , ( ( v : I^n n) → product
                  ( is-equiv (first (fa v 0₂)) (first (fb v 0₂)) (fc v 0₂))
                  ( is-equiv (first (fa v 1₂)) (first (fb v 1₂)) (fc v 1₂)))) in
          let mod ♭ curry-X :=
            mod ♭ (equiv-has-inverse
              ( X-uncurried) (X-cube)
              ( \ (fa , (fb , (fc , last))) →
                ( \ (v , t) → fa v (unform t)
                , ( \ (v , t) → fb v (unform t)
                  , ( \ (v , t) → fc v (unform t)
                    , last))))
              ( \ (F , (G , (alpha , e))) →
                ( \ v j → F (v , form j)
                , ( \ v j → G (v , form j)
                  , ( \ v j → alpha (v , form j)
                    , e))))
              ( \ _ → refl) (\ _ → refl)) in
          equiv-comp (♭ (I^n n → X)) (♭ X-cube) X-split
            ( b-equiv (I^n n → X) X-cube
                ( equiv-comp (I^n n → X) X-uncurried X-cube
                    ( equiv-choice3 (I^n n) (\ _ → 𝕀 → S) (\ _ _ → 𝕀 → S)
                        ( \ _ F G → (i : 𝕀) → first (F i) → first (G i))
                        ( \ _ F G alpha → product
                            ( is-equiv (first (F 0₂)) (first (G 0₂)) (alpha 0₂))
                            ( is-equiv (first (F 1₂)) (first (G 1₂)) (alpha 1₂))))
                    ( curry-X)))
            ( b-sigma3-commute-equiv (Gamma' → S) (\ _ → Gamma' → S) Hom-in-S E-X) in
        let to-Y-split : Equiv (♭ (I^n n → Y)) Y-split :=
          let mod ♭ Y-uncurried :=
            mod ♭ (Σ (fa : (v : I^n n) → 𝕀 → S)
            , Σ ( fb : (v : I^n n) → 𝕀 → S)
            , Σ ( fc : (v : I^n n) → ((i : 𝕀) → first (fa v i) → first (fb v i)))
            , ( ( v : I^n n) → (i : 𝕀) → is-equiv (first (fa v i)) (first (fb v i)) (fc v i))) in
          let mod ♭ curry-Y :=
            mod ♭ (equiv-has-inverse
              ( Y-uncurried) (Y-cube)
              ( \ (fa , (fb , (fc , nlast))) →
                ( \ (v , t) → fa v (unform t)
                , ( \ (v , t) → fb v (unform t)
                  , ( \ (v , t) → fc v (unform t)
                    , \ (v , i) → nlast v (unform i)))))
              ( \ (F , (G , (alpha , e))) →
                ( \ v j → F (v , form j)
                , ( \ v j → G (v , form j)
                  , ( \ v j → alpha (v , form j)
                    , \ v j → e (v , form j)))))
              ( \ _ → refl) (\ _ → refl)) in
          equiv-comp (♭ (I^n n → Y)) (♭ Y-cube) Y-split
            ( b-equiv (I^n n → Y) Y-cube
                ( equiv-comp (I^n n → Y) Y-uncurried Y-cube
                    ( equiv-choice3 (I^n n) (\ _ → 𝕀 → S) (\ _ _ → 𝕀 → S)
                        ( \ _ F G → (i : 𝕀) → first (F i) → first (G i))
                        ( \ _ F G alpha → (theta : 𝕀) → is-equiv (first (F theta)) (first (G theta)) (alpha theta)))
                    ( curry-Y)))
            ( b-sigma3-commute-equiv (Gamma' → S) (\ _ → Gamma' → S) Hom-in-S E-Y) in
        let Y-to-X-split : Equiv Y-split X-split :=
          total-b-equiv-family3
            ( Gamma' → S)
            ( \ _ → Gamma' → S)
            ( Hom-in-S)
            ( \ (F0 :♭ Gamma' → S) → \ (G0 :♭ Gamma' → S) → \ (a0 :♭ Hom-in-S F0 G0) → ♭ (E-Y F0 G0 a0))
            ( \ (F0 :♭ Gamma' → S) → \ (G0 :♭ Gamma' → S) → \ (a0 :♭ Hom-in-S F0 G0) → ♭ (E-X F0 G0 a0))
            ( \ (F0 :♭ Gamma' → S) → \ (G0 :♭ Gamma' → S) → \ (a0 :♭ Hom-in-S F0 G0) →
                equiv-iff-is-prop-is-prop
                  ( ♭ ( E-Y F0 G0 a0))
                  ( ♭ ( E-X F0 G0 a0))
                  ( is-prop-flat (E-Y F0 G0 a0) (mod ♭ (E-Y-is-prop F0 G0 a0)))
                  ( is-prop-flat (E-X F0 G0 a0) (mod ♭ (E-X-is-prop F0 G0 a0)))
                  ( ( b-map (E-Y F0 G0 a0) (E-X F0 G0 a0)
                        ( \ e v → (e (v , form 0₂) , e (v , form 1₂))))
                  , ( \ e →
                        let mod ♭ e0 := e in
                        let mod ♭ F̃ :=
                          mod ♭ (Σ (t : Gamma') , first (F0 t)) in
                        let mod ♭ G̃ :=
                          mod ♭ (Σ (t : Gamma') , first (G0 t)) in
                        let mod ♭ ã : F̃ → G̃ :=
                          mod ♭ (total-map
                            ( Gamma')
                            ( \ t → first (F0 t))
                            ( \ t → first (G0 t))
                            ( \ t → a0 t)) in
                        let mod ♭ fiberwise-is-equiv :=
                          mod ♭ ((t : Gamma')
                          → is-equiv (first (F0 t)) (first (G0 t)) (a0 t)) in
                        let mod ♭ fiberwise-is-equiv-is-prop
 : is-prop fiberwise-is-equiv
                          :=
                            mod ♭ (is-prop-fiberwise-prop funext
                              ( Gamma')
                              ( \ t → is-equiv (first (F0 t))
                                  ( first (G0 t)) (a0 t))
                              ( \ t → is-prop-is-equiv funext
                                  ( first (F0 t))
                                  ( first (G0 t))
                                  ( a0 t))) in
                        let mod ♭ total-is-equiv-is-prop
 : is-prop (is-equiv F̃ G̃ ã)
                          :=
                            mod ♭ (is-prop-is-equiv funext F̃ G̃ ã) in
                        let mod ♭ to-E-Y : is-equiv F̃ G̃ ã → E-Y F0 G0 a0 :=
                          mod ♭ (first (inv-equiv
                            ( E-Y F0 G0 a0)
                            ( is-equiv F̃ G̃ ã)
                            ( equiv-comp
                                ( E-Y F0 G0 a0)
                                ( fiberwise-is-equiv)
                                ( is-equiv F̃ G̃ ã)
                                ( equiv-identity (E-Y F0 G0 a0))
                                ( equiv-iff-is-prop-is-prop
                                    ( fiberwise-is-equiv)
                                    ( is-equiv F̃ G̃ ã)
                                    ( fiberwise-is-equiv-is-prop)
                                    ( total-is-equiv-is-prop)
                                    ( is-equiv-total-iff-is-equiv-fiberwise
                                        ( Gamma')
                                        ( \ t → first (F0 t))
                                        ( \ t → first (G0 t))
                                        ( \ t → a0 t)))))) in
                        b-map (is-equiv F̃ G̃ ã) (E-Y F0 G0 a0) to-E-Y
                          ( mod ♭ (second (cubes-separate F̃ G̃ ã)
                              ( \ (m :♭ nat) →
                                let fixed-F
 : ( v : ♭ (I^n m → I^n n)) → U
                                  :=
                                    \ v →
                                      let mod ♭ v' := v in
                                      Σ ( theta : ♭ (I^n m → shape (_ : 𝕀 | TOP)))
                                      , ( let mod ♭ theta' := theta in
                                          let mod ♭ vc :=
                                            mod ♭ (v' (zero-vec-I^n m)) in
                                          let mod ♭ i :=
                                            mod ♭ (unform (theta' (zero-vec-I^n m))) in
                                          ♭ ( first (F0 (vc , form i)))) in
                                let fixed-G
 : ( v : ♭ (I^n m → I^n n)) → U
                                  :=
                                    \ v →
                                      let mod ♭ v' := v in
                                      Σ ( theta : ♭ (I^n m → shape (_ : 𝕀 | TOP)))
                                      , ( let mod ♭ theta' := theta in
                                          let mod ♭ vc :=
                                            mod ♭ (v' (zero-vec-I^n m)) in
                                          let mod ♭ i :=
                                            mod ♭ (unform (theta' (zero-vec-I^n m))) in
                                          ♭ ( first (G0 (vc , form i)))) in
                                let to-F-split
 : Equiv
                                      ( ♭ ( I^n m → Σ (t : product (I^n n) (shape (_ : 𝕀 | TOP))) , first (F0 t)))
                                      ( Σ ( v : ♭ (I^n m → I^n n)) , fixed-F v)
                                  :=
                                    let mod ♭ F-uncurried :=
                                      mod ♭ (orthogonality-pullback-fiber n m (\ t → first (F0 t))) in
                                    let mod ♭ curry-F :=
                                      mod ♭ (equiv-orthogonality-pullback-split n m (\ t → first (F0 t))) in
                                    equiv-comp
                                      ( ♭ ( I^n m → Σ (t : product (I^n n) (shape (_ : 𝕀 | TOP))) , first (F0 t)))
                                      ( ♭ ( orthogonality-pullback-split n m (\ t → first (F0 t))))
                                      ( Σ ( v : ♭ (I^n m → I^n n)) , fixed-F v)
                                      ( b-equiv
                                          ( I^n m → Σ (t : product (I^n n) (shape (_ : 𝕀 | TOP))) , first (F0 t))
                                          ( orthogonality-pullback-split n m (\ t → first (F0 t)))
                                          ( equiv-comp
                                              ( I^n m → Σ (t : product (I^n n) (shape (_ : 𝕀 | TOP))) , first (F0 t))
                                              ( F-uncurried)
                                              ( orthogonality-pullback-split n m (\ t → first (F0 t)))
                                              ( orthogonality-pullback n m (\ t → first (F0 t)))
                                              ( curry-F)))
                                      ( orthogonality-pullback-flat-commute n m (\ t → first (F0 t))) in
                                let to-G-split
 : Equiv
                                      ( ♭ ( I^n m → Σ (t : product (I^n n) (shape (_ : 𝕀 | TOP))) , first (G0 t)))
                                      ( Σ ( v : ♭ (I^n m → I^n n)) , fixed-G v)
                                  :=
                                    let mod ♭ G-uncurried :=
                                      mod ♭ (orthogonality-pullback-fiber n m (\ t → first (G0 t))) in
                                    let mod ♭ curry-G :=
                                      mod ♭ (equiv-orthogonality-pullback-split n m (\ t → first (G0 t))) in
                                    equiv-comp
                                      ( ♭ ( I^n m → Σ (t : product (I^n n) (shape (_ : 𝕀 | TOP))) , first (G0 t)))
                                      ( ♭ ( orthogonality-pullback-split n m (\ t → first (G0 t))))
                                      ( Σ ( v : ♭ (I^n m → I^n n)) , fixed-G v)
                                      ( b-equiv
                                          ( I^n m → Σ (t : product (I^n n) (shape (_ : 𝕀 | TOP))) , first (G0 t))
                                          ( orthogonality-pullback-split n m (\ t → first (G0 t)))
                                          ( equiv-comp
                                              ( I^n m → Σ (t : product (I^n n) (shape (_ : 𝕀 | TOP))) , first (G0 t))
                                              ( G-uncurried)
                                              ( orthogonality-pullback-split n m (\ t → first (G0 t)))
                                              ( orthogonality-pullback n m (\ t → first (G0 t)))
                                              ( curry-G)))
                                      ( orthogonality-pullback-flat-commute n m (\ t → first (G0 t))) in
                                let fixed-equiv
 : Equiv
                                      ( Σ ( v : ♭ (I^n m → I^n n)) , fixed-F v)
                                      ( Σ ( v : ♭ (I^n m → I^n n)) , fixed-G v)
                                  :=
                                    total-b-equiv-family2
                                      ( I^n m → I^n n)
                                      ( \ _ → I^n m → shape (_ : 𝕀 | TOP))
                                      ( \ (v' :♭ (I^n m → I^n n))
                                        → \ (theta' :♭ (I^n m → shape (_ : 𝕀 | TOP)))
                                          → let mod ♭ vc :=
                                              mod ♭ (v' (zero-vec-I^n m)) in
                                            let mod ♭ i :=
                                              mod ♭ (unform (theta' (zero-vec-I^n m))) in
                                            ♭ ( first (F0 (vc , form i))))
                                      ( \ (v' :♭ (I^n m → I^n n))
                                        → \ (theta' :♭ (I^n m → shape (_ : 𝕀 | TOP)))
                                          → let mod ♭ vc :=
                                              mod ♭ (v' (zero-vec-I^n m)) in
                                            let mod ♭ i :=
                                              mod ♭ (unform (theta' (zero-vec-I^n m))) in
                                            ♭ ( first (G0 (vc , form i))))
                                      ( \ (v' :♭ (I^n m → I^n n))
                                        → \ (theta' :♭ (I^n m → shape (_ : 𝕀 | TOP)))
                                          → let mod ♭ vc :=
                                              mod ♭ (v' (zero-vec-I^n m)) in
                                            let mod ♭ i :=
                                              mod ♭ (unform (theta' (zero-vec-I^n m))) in
                                            b-equiv
                                              ( first (F0 (vc , form i)))
                                              ( first (G0 (vc , form i)))
                                              ( a0 (vc , form i)
                                              , is-equiv-discrete-interval-elim i
                                                  ( \ j → first (F0 (vc , form j)))
                                                  ( \ j → first (G0 (vc , form j)))
                                                  ( \ j → a0 (vc , form j))
                                                  ( first (e0 vc))
                                                  ( second (e0 vc)))) in
                                is-equiv-b-map-via-splits
                                  ( I^n m → F̃) (I^n m → G̃)
                                  ( \ p t → ã (p t))
                                  ( Σ ( v : ♭ (I^n m → I^n n)) , fixed-F v)
                                  ( Σ ( v : ♭ (I^n m → I^n n)) , fixed-G v)
                                  ( to-F-split) (to-G-split) (fixed-equiv)
                                  ( \ _ → refl))))))) in
        is-equiv-b-map-via-splits
          ( I^n n → Y) (I^n n → X)
          ( \ p t → Y-to-X (p t))
          ( Y-split) (X-split)
          ( to-Y-split) (to-X-split) (Y-to-X-split)
          ( \ _ → refl)
      ) in
    \ e0 e1 →
      transport X
        ( \ (F , (G , (alpha , w))) → (i : 𝕀) → is-equiv (first (F i)) (first (G i)) (alpha i))
        ( Y-to-X (first (second Y-to-X-is-equiv) (f , (g , (a , (e0 , e1))))))
        ( f , (g , (a , (e0 , e1))))
        ( second (second Y-to-X-is-equiv) (f , (g , (a , (e0 , e1)))))
        ( second (second (second (first (second Y-to-X-is-equiv) (f , (g , (a , (e0 , e1))))))))

#def is-equiv-amazing-covariant-from-vertices uses (funext weakfunext extext)
  ( f g : ( ( t , s) : Δ²-II) → S)
  ( a : ( ( t , s) : Δ²-II) → first (f (t , s)) → first (g (t , s)))
  : is-equiv (first (f (0₂ , 0₂))) (first (g (0₂ , 0₂))) (a (0₂ , 0₂))
    → is-equiv (first (f (1₂ , 0₂))) (first (g (1₂ , 0₂))) (a (1₂ , 0₂))
    → is-equiv (first (f (1₂ , 1₂))) (first (g (1₂ , 1₂))) (a (1₂ , 1₂))
    → ( ( t , s) : Δ²-II) → is-equiv (first (f (t , s))) (first (g (t , s))) (a (t , s))
  :=
    \ e00 e10 e11 →
      \ (t , s) →
        is-equiv-amazing-covariant-from-endpoints
          ( \ r → f (sup s r , s))
          ( \ r → g (sup s r , s))
          ( \ r → a (sup s r , s))
          ( is-equiv-amazing-covariant-from-endpoints
              ( \ r → f (r , r)) (\ r → g (r , r)) (\ r → a (r , r)) e00 e11 s)
          ( is-equiv-amazing-covariant-from-endpoints
              ( \ s' → f (1₂ , s')) (\ s' → g (1₂ , s')) (\ s' → a (1₂ , s')) e10 e11 s)
          ( t)

#def dirglue-mor2fun=f uses (funext weakfunext extext)
  ( F : 𝕀 → S)
  : F = dirglue (F 0₂) (F 1₂) (second (second (mor2fun F)))
  :=
    let G : 𝕀 → S
      := dirglue (F 0₂) (F 1₂) (second (second (mor2fun F))) in
    let a : (j : 𝕀) → first (F j) → first (G j)
      := \ i x →
         ( covariant-transport-line-II
            ( \ (t : 𝕀 | TOP) → first (F (sup i t)))
            ( s-is-covariant-arrow-II (\ j → F (sup i j)))
            ( \ k → form k)
            x
         , \ (t : 1 | i ≡ 0₂) → (x , refl)) in
    let equiv-0 : is-equiv (first (F 0₂)) (first (G 0₂)) (a 0₂)
      := is-equiv-right-factor
           ( first (F 0₂)) (first (G 0₂)) (first (F 0₂))
           ( a 0₂)
           ( \ p → first ((second p) *₁))
           ( second (dirglue-equiv-0 (F 0₂) (F 1₂) (second (second (mor2fun F)))))
           ( is-equiv-identity (first (F 0₂))) in
    let equiv-1 : is-equiv (first (F 1₂)) (first (G 1₂)) (a 1₂)
      := is-equiv-right-factor
           ( first (F 1₂)) (first (G 1₂)) (first (F 1₂))
           ( a 1₂)
           ( \ p → first p)
           ( second (dirglue-equiv-1 (F 0₂) (F 1₂) (second (second (mor2fun F)))))
           ( is-equiv-homotopy (first (F 1₂)) (first (F 1₂))
               ( \ x → covariant-transport-line-II
                    ( \ (t : 𝕀 | TOP) → first (F 1₂))
                    ( s-is-covariant-arrow-II (\ j → F 1₂))
                    ( \ k → form k)
                    x)
               ( \ a → a)
               ( \ x → amazing-covariant-uniqueness-line-II
                    ( \ (t : 𝕀 | TOP) → first (F 1₂))
                    ( s-is-covariant-arrow-II (\ j → F 1₂))
                    x
                    x
                    ( \ _ → x))
               ( is-equiv-identity (first (F 1₂)))) in
    naiveextext-extext extext
      𝕀 ( \ _ → ⊤) (\ _ → BOT)
      ( \ _ → S) (\ _ → recBOT)
      ( F) (G)
      ( \ i →
        eq-pair-equiv
          ( is-a-cov funext weakfunext)
          ( F i) (G i)
          ( a i , is-equiv-amazing-covariant-from-endpoints F G a equiv-0 equiv-1 i)
          ( first
            ( is-prop-is-a-cov funext weakfunext (first (G i))
              ( transport U (is-a-cov funext weakfunext)
                  ( first (F i)) (first (G i))
                  ( first (ua (first (F i)) (first (G i)))
                    ( a i , is-equiv-amazing-covariant-from-endpoints F G a equiv-0 equiv-1 i))
                  ( second (F i)))
              ( second (G i)))))

```

Directed univalence

```rzk

-- GWB, Theorem 6.13
#def dua uses (funext weakfunext extext)
  : Equiv (Σ (A : S) , (Σ (B : S) , (first A → first B))) ((i : 𝕀) → S)
  := (\ t → dirglue (first t) (first (second t)) (second (second t))
   , ( ( mor2fun , \ t → mor2fun-dirglue=f (first t) (first (second t)) (second (second t)))
   , ( mor2fun , \ F → rev (𝕀 → S) F (dirglue (F 0₂) (F 1₂) (second (second (mor2fun F)))) (dirglue-mor2fun=f F))))
```

## Arrows in S

```rzk

#def hom-II-in-S uses (funext weakfunext)
  ( x y : S)
  ( h : hom-II S x y)
  : first x → first y
  := second (second (mor2fun h))

#def is-equiv-hom-II-in-S uses (funext weakfunext extext)
  ( x y : S)
  : is-equiv (hom-II S x y) (first x → first y) (hom-II-in-S x y)
  :=
    is-equiv-fiberwise-is-equiv-total
      ( product S S)
      ( \ (a , b) → hom-II S a b)
      ( \ (a , b) → first a → first b)
      ( \ (a , b) → hom-II-in-S a b)
      ( second
          ( equiv-triple-comp
              ( fibered-arr-II' S)
              ( arr-II S)
              ( Σ ( A : S) , (Σ (B : S) , (first A → first B)))
              ( Σ ( ab : product S S) , (first (first ab) → first (second ab)))
              ( inv-equiv (arr-II S) (fibered-arr-II' S)
                  ( fibered-arr-free-arr-II' S , is-equiv-fibered-arr-free-arr-II' S))
              ( inv-equiv (Σ (A : S) , (Σ (B : S) , (first A → first B))) (arr-II S) dua)
              ( associative-Σ S (\ _ → S) (\ A B → first A → first B))))
      ( x , y)

#def equiv-hom-II-in-S uses (funext weakfunext extext)
  ( x y : S)
  : Equiv (hom-II S x y) (first x → first y)
  := (hom-II-in-S x y , is-equiv-hom-II-in-S x y)

```

## S is Segal

First we compare two-simplices in `S` with three objects and two underlying
maps.

### The two-dimensional dirglue2 and mor2fun2

```rzk

#def dirglue2-is-acov uses (funext weakfunext extext)
  ( A B C : S)
  ( f : first A → first B)
  ( g : first B → first C)
  ( t s : 𝕀)
  : ( is-a-cov funext weakfunext) (
      Σ ( c : first C)
      , ( ( u : 1 | s ≡ 0₂)
        → Σ ( bf : fib (first B) (first C) g c)
          , ( ( w : 1 | t ≡ 0₂) → fib (first A) (first B) f (first bf))))
  :=
    is-a-cov-sigma-closed funext weakfunext
      ( first C)
      ( \ c →
          ( u : 1 | s ≡ 0₂)
        → Σ ( bf : fib (first B) (first C) g c)
          , ( ( w : 1 | t ≡ 0₂) → fib (first A) (first B) f (first bf)))
      ( second C)
      ( \ c →
          let mod ᵒᵖ flip_s := flipᵒᵖ s in
            is-a-cov-ext funext weakfunext extext
              ( mod ᵒᵖ (flip_s ≡ 1₂))
              ( mod ᵒᵖ (is-a-cov-i===0 funext weakfunext extext flip_s))
              ( Σ ( bf : fib (first B) (first C) g c)
                , ( ( w : 1 | t ≡ 0₂) → fib (first A) (first B) f (first bf)))
              ( is-a-cov-sigma-closed funext weakfunext
                  ( fib (first B) (first C) g c)
                  ( \ bf → (w : 1 | t ≡ 0₂) → fib (first A) (first B) f (first bf))
                  ( is-a-cov-fib funext weakfunext
                      ( first B) (first C)
                      ( second B) (second C)
                      ( g) (c))
                  ( \ bf →
                      let mod ᵒᵖ flip_t := flipᵒᵖ t in
                        is-a-cov-ext funext weakfunext extext
                          ( mod ᵒᵖ (flip_t ≡ 1₂))
                          ( mod ᵒᵖ (is-a-cov-i===0 funext weakfunext extext flip_t))
                          ( fib (first A) (first B) f (first bf))
                          ( is-a-cov-fib funext weakfunext
                              ( first A) (first B)
                              ( second A) (second B)
                              ( f) (first bf)))))

#def dirglue2 uses (funext weakfunext extext)
  ( A B C : S)
  ( f : first A → first B)
  ( g : first B → first C)
  : ( ( t , s) : Δ²-II) → S
  :=
    \ (t , s) →
      ( Σ ( c : first C)
        , ( ( u : 1 | s ≡ 0₂)
          → Σ ( bf : fib (first B) (first C) g c)
            , ( ( w : 1 | t ≡ 0₂) → fib (first A) (first B) f (first bf)))
      , dirglue2-is-acov A B C f g t s)

#def dirglue2-equiv-11 uses (funext weakfunext extext)
  ( A B C : S)
  ( f : first A → first B)
  ( g : first B → first C)
  : Equiv (first (dirglue2 A B C f g (1₂ , 1₂))) (first C)
  :=
    equiv-total-type-is-contr-fiber
      ( first C)
      ( \ c → (u : 1 | 1₂ ≡ 0₂)
        → Σ ( bf : fib (first B) (first C) g c)
          , ( ( w : 1 | 1₂ ≡ 0₂) → fib (first A) (first B) f (first bf)))
      ( \ c → is-contr-extent-1 extext
          ( Σ ( bf : fib (first B) (first C) g c)
            , ( ( w : 1 | 1₂ ≡ 0₂) → fib (first A) (first B) f (first bf))))

#def dirglue2-equiv-10 uses (funext weakfunext extext)
  ( A B C : S)
  ( f : first A → first B)
  ( g : first B → first C)
  : Equiv (first (dirglue2 A B C f g (1₂ , 0₂))) (first B)
  :=
    equiv-comp
      ( first (dirglue2 A B C f g (1₂ , 0₂)))
      ( total-type (first C) (fib (first B) (first C) g))
      ( first B)
      ( total-equiv-family-of-equiv
          ( first C)
          ( \ c → (u : 1 | 0₂ ≡ 0₂)
            → Σ ( bf : fib (first B) (first C) g c)
              , ( ( w : 1 | 1₂ ≡ 0₂) → fib (first A) (first B) f (first bf)))
          ( fib (first B) (first C) g)
          ( \ c →
              equiv-comp
                ( ( u : 1 | 0₂ ≡ 0₂)
                  → Σ ( bf : fib (first B) (first C) g c)
                    , ( ( w : 1 | 1₂ ≡ 0₂) → fib (first A) (first B) f (first bf)))
                ( Σ ( bf : fib (first B) (first C) g c)
                  , ( ( w : 1 | 1₂ ≡ 0₂) → fib (first A) (first B) f (first bf)))
                ( fib (first B) (first C) g c)
                ( equiv-extent-0
                    ( Σ ( bf : fib (first B) (first C) g c)
                      , ( ( w : 1 | 1₂ ≡ 0₂) → fib (first A) (first B) f (first bf))))
                ( equiv-total-type-is-contr-fiber
                    ( fib (first B) (first C) g c)
                    ( \ bf → (w : 1 | 1₂ ≡ 0₂) → fib (first A) (first B) f (first bf))
                    ( \ bf → is-contr-extent-1 extext (fib (first A) (first B) f (first bf))))))
      ( ( \ (_ , (b , _)) → b)
      , is-equiv-domain-sum-of-fibers (first B) (first C) g)

#def dirglue2-equiv-00 uses (funext weakfunext extext)
  ( A B C : S)
  ( f : first A → first B)
  ( g : first B → first C)
  : Equiv (first (dirglue2 A B C f g (0₂ , 0₂))) (first A)
  :=
    equiv-comp
      ( first (dirglue2 A B C f g (0₂ , 0₂)))
      ( Σ ( c : first C)
        , Σ ( bf : fib (first B) (first C) g c)
          , fib (first A) (first B) f (first bf))
      ( first A)
      ( total-equiv-family-of-equiv
          ( first C)
          ( \ c → (u : 1 | 0₂ ≡ 0₂)
            → Σ ( bf : fib (first B) (first C) g c)
              , ( ( w : 1 | 0₂ ≡ 0₂) → fib (first A) (first B) f (first bf)))
          ( \ c → Σ ( bf : fib (first B) (first C) g c)
              , fib (first A) (first B) f (first bf))
          ( \ c →
              equiv-comp
                ( ( u : 1 | 0₂ ≡ 0₂)
                  → Σ ( bf : fib (first B) (first C) g c)
                    , ( ( w : 1 | 0₂ ≡ 0₂) → fib (first A) (first B) f (first bf)))
                ( Σ ( bf : fib (first B) (first C) g c)
                  , ( ( w : 1 | 0₂ ≡ 0₂) → fib (first A) (first B) f (first bf)))
                ( Σ ( bf : fib (first B) (first C) g c)
                  , fib (first A) (first B) f (first bf))
                ( equiv-extent-0
                    ( Σ ( bf : fib (first B) (first C) g c)
                      , ( ( w : 1 | 0₂ ≡ 0₂) → fib (first A) (first B) f (first bf))))
                ( total-equiv-family-of-equiv
                    ( fib (first B) (first C) g c)
                    ( \ bf → (w : 1 | 0₂ ≡ 0₂) → fib (first A) (first B) f (first bf))
                    ( \ bf → fib (first A) (first B) f (first bf))
                    ( \ bf → equiv-extent-0 (fib (first A) (first B) f (first bf))))))
      ( equiv-has-inverse
          ( Σ ( c : first C)
            , Σ ( bf : fib (first B) (first C) g c)
              , fib (first A) (first B) f (first bf))
          ( first A)
          ( \ (c , (bf , ff)) → first ff)
          ( \ a → (g (f a) , ((f a , refl) , (a , refl))))
          ( \ (c , ((b , p) , (a , q))) →
              ind-path (first B) (f a)
                ( \ b' q' →
                    ( p' : g b' = c)
                    → ( (g (f a) , ((f a , refl) , (a , refl)))
                        =_{ Σ ( c'' : first C)
                          , Σ ( bf'' : fib (first B) (first C) g c'')
                            , fib (first A) (first B) f (first bf'') }
                        ( c , ((b' , p') , (a , q')))))
                ( \ p' →
                    ind-path (first C) (g (f a))
                      ( \ c' p'' →
                          ( (g (f a) , ((f a , refl) , (a , refl)))
                            =_{ Σ ( c'' : first C)
                              , Σ ( bf'' : fib (first B) (first C) g c'')
                                , fib (first A) (first B) f (first bf'') }
                            ( c' , ((f a , p'') , (a , refl)))))
                      ( refl)
                      ( c) (p'))
                ( b) (q) (p))
          ( \ a → refl))

#def dirglue2-00=A-EqΣ uses (funext weakfunext extext)
  ( A B C : S)
  ( f : first A → first B)
  ( g : first B → first C)
  : Eq-Σ U (is-a-cov funext weakfunext) (dirglue2 A B C f g (0₂ , 0₂)) A
  := ( first (ua (first (dirglue2 A B C f g (0₂ , 0₂))) (first A)) (dirglue2-equiv-00 A B C f g)
     , first
         ( is-prop-is-a-cov funext weakfunext (first A)
           ( transport U (is-a-cov funext weakfunext)
               ( first (dirglue2 A B C f g (0₂ , 0₂))) (first A)
               ( first (ua (first (dirglue2 A B C f g (0₂ , 0₂))) (first A)) (dirglue2-equiv-00 A B C f g))
               ( second (dirglue2 A B C f g (0₂ , 0₂))))
           ( second A)))

#def dirglue2_00=A uses (funext weakfunext extext)
  ( A B C : S)
  ( f : first A → first B)
  ( g : first B → first C)
  : dirglue2 A B C f g (0₂ , 0₂) = A
  := eq-pair U (is-a-cov funext weakfunext) (dirglue2 A B C f g (0₂ , 0₂)) A (dirglue2-00=A-EqΣ A B C f g)

#def dirglue2-10=B-EqΣ uses (funext weakfunext extext)
  ( A B C : S)
  ( f : first A → first B)
  ( g : first B → first C)
  : Eq-Σ U (is-a-cov funext weakfunext) (dirglue2 A B C f g (1₂ , 0₂)) B
  := ( first (ua (first (dirglue2 A B C f g (1₂ , 0₂))) (first B)) (dirglue2-equiv-10 A B C f g)
     , first
         ( is-prop-is-a-cov funext weakfunext (first B)
           ( transport U (is-a-cov funext weakfunext)
               ( first (dirglue2 A B C f g (1₂ , 0₂))) (first B)
               ( first (ua (first (dirglue2 A B C f g (1₂ , 0₂))) (first B)) (dirglue2-equiv-10 A B C f g))
               ( second (dirglue2 A B C f g (1₂ , 0₂))))
           ( second B)))

#def dirglue2_10=B uses (funext weakfunext extext)
  ( A B C : S)
  ( f : first A → first B)
  ( g : first B → first C)
  : dirglue2 A B C f g (1₂ , 0₂) = B
  := eq-pair U (is-a-cov funext weakfunext) (dirglue2 A B C f g (1₂ , 0₂)) B (dirglue2-10=B-EqΣ A B C f g)

#def dirglue2-11=C-EqΣ uses (funext weakfunext extext)
  ( A B C : S)
  ( f : first A → first B)
  ( g : first B → first C)
  : Eq-Σ U (is-a-cov funext weakfunext) (dirglue2 A B C f g (1₂ , 1₂)) C
  := ( first (ua (first (dirglue2 A B C f g (1₂ , 1₂))) (first C)) (dirglue2-equiv-11 A B C f g)
     , first
         ( is-prop-is-a-cov funext weakfunext (first C)
           ( transport U (is-a-cov funext weakfunext)
               ( first (dirglue2 A B C f g (1₂ , 1₂))) (first C)
               ( first (ua (first (dirglue2 A B C f g (1₂ , 1₂))) (first C)) (dirglue2-equiv-11 A B C f g))
               ( second (dirglue2 A B C f g (1₂ , 1₂))))
           ( second C)))

#def dirglue2_11=C uses (funext weakfunext extext)
  ( A B C : S)
  ( f : first A → first B)
  ( g : first B → first C)
  : dirglue2 A B C f g (1₂ , 1₂) = C
  := eq-pair U (is-a-cov funext weakfunext) (dirglue2 A B C f g (1₂ , 1₂)) C (dirglue2-11=C-EqΣ A B C f g)

#def mor2fun2 uses (funext weakfunext)
  ( F : ( ( t , s) : Δ²-II) → S)
  : Σ ( A : S)
    , (Σ ( B : S)
      , (Σ ( C : S)
        , (Σ ( f : first A → first B)
          , (first B → first C))))
  :=
    ( first (mor2fun (\ t → F (t , 0₂)))
    , ( first (second (mor2fun (\ t → F (t , 0₂))))
      , ( first (second (mor2fun (\ s → F (1₂ , s))))
        , ( second (second (mor2fun (\ t → F (t , 0₂))))
          , second (second (mor2fun (\ s → F (1₂ , s))))))))

#def eq-composable uses (funext weakfunext)
  ( a b c : S)
  ( d : first a → first b)
  ( e : first b → first c)
  ( a' : S) ( pa : a = a')
  : ( b' : S) → ( pb : b = b')
  → ( c' : S) → ( pc : c = c')
  → ( d' : first a' → first b')
  → ( pd : product-transport S S (\ X Y → first X → first Y) a a' b b' pa pb d = d')
  → ( e' : first b' → first c')
  → ( pe : product-transport S S (\ X Y → first X → first Y) b b' c c' pb pc e = e')
  → ( ( a , (b , (c , (d , e))))
    =_{ Σ ( A : S)
       , (Σ ( B : S)
         , (Σ ( C : S)
           , (Σ ( f : first A → first B)
             , (first B → first C)))) }
      (a' , (b' , (c' , (d' , e')))))
  :=
    let composable : U :=
      Σ ( A : S)
      , (Σ ( B : S)
        , (Σ ( C : S)
          , (Σ ( f : first A → first B)
            , (first B → first C)))) in
    ind-path S a
      ( \ a'' pa'' →
          ( b' : S) → ( pb : b = b')
        → ( c' : S) → ( pc : c = c')
        → ( d' : first a'' → first b')
        → ( pd : product-transport S S (\ X Y → first X → first Y) a a'' b b' pa'' pb d = d')
        → ( e' : first b' → first c')
        → ( pe : product-transport S S (\ X Y → first X → first Y) b b' c c' pb pc e = e')
        → ( ( a , (b , (c , (d , e)))) =_{ composable } (a'' , (b' , (c' , (d' , e'))))))
      ( \ b' pb →
          ind-path S b
            ( \ b'' pb'' →
                ( c' : S) → ( pc : c = c')
              → ( d' : first a → first b'')
              → ( pd : product-transport S S (\ X Y → first X → first Y) a a b b'' refl pb'' d = d')
              → ( e' : first b'' → first c')
              → ( pe : product-transport S S (\ X Y → first X → first Y) b b'' c c' pb'' pc e = e')
              → ( ( a , (b , (c , (d , e)))) =_{ composable } (a , (b'' , (c' , (d' , e'))))))
            ( \ c' pc →
                ind-path S c
                  ( \ c'' pc'' →
                      ( d' : first a → first b)
                    → ( pd : product-transport S S (\ X Y → first X → first Y) a a b b refl refl d = d')
                    → ( e' : first b → first c'')
                    → ( pe : product-transport S S (\ X Y → first X → first Y) b b c c'' refl pc'' e = e')
                    → ( ( a , (b , (c , (d , e)))) =_{ composable } (a , (b , (c'' , (d' , e'))))))
                  ( \ d' pd e' pe →
                      concat composable
                        ( a , (b , (c , (d , e))))
                        ( a , (b , (c , (d' , e))))
                        ( a , (b , (c , (d' , e'))))
                        ( ap (first a → first b) composable d d'
                            ( \ dd → (a , (b , (c , (dd , e))))) pd)
                        ( ap (first b → first c) composable e e'
                            ( \ ee → (a , (b , (c , (d' , ee))))) pe))
                  ( c') ( pc))
            ( b') ( pb))
      ( a') ( pa)

#def coe-dirglue2-bottom-is-f-pointwise uses (funext weakfunext extext)
  ( A B C : S)
  ( f : first A → first B)
  ( g : first B → first C)
  ( a : first A)
  : transport S (\ s → first s) (dirglue2 A B C f g (1₂ , 0₂)) B (dirglue2_10=B A B C f g)
      ( covariant-transport-line-II (\ (t : 𝕀 | TOP) → first (dirglue2 A B C f g (t , 0₂)))
          ( s-is-covariant-arrow-II (\ t → dirglue2 A B C f g (t , 0₂))) (\ k → form k)
          ( transport-rev S (\ s → first s) (dirglue2 A B C f g (0₂ , 0₂)) A (dirglue2_00=A A B C f g) a))
    = f a
  :=
    let coe-BE : first (dirglue2 A B C f g (0₂ , 0₂)) → first (dirglue2 A B C f g (1₂ , 0₂))
      := covariant-transport-line-II (\ (t : 𝕀 | TOP) → first (dirglue2 A B C f g (t , 0₂)))
           ( s-is-covariant-arrow-II (\ t → dirglue2 A B C f g (t , 0₂))) (\ k → form k) in
    let a-in-0 : first (dirglue2 A B C f g (0₂ , 0₂))
      := transport-rev S (\ s → first s) (dirglue2 A B C f g (0₂ , 0₂)) A (dirglue2_00=A A B C f g) a in
    let bf : fib (first B) (first C) g (first a-in-0)
      := first ((second a-in-0) *₁) in
    let ff : fib (first A) (first B) f (first bf)
      := (second ((second a-in-0) *₁)) *₁ in
    concat (first B)
      ( transport S (\ s → first s) (dirglue2 A B C f g (1₂ , 0₂)) B (dirglue2_10=B A B C f g) (coe-BE a-in-0))
      ( first (dirglue2-equiv-10 A B C f g) (coe-BE a-in-0))
      ( f a)
      ( concat (first B)
          ( transport S (\ s → first s) (dirglue2 A B C f g (1₂ , 0₂)) B (dirglue2_10=B A B C f g) (coe-BE a-in-0))
          ( transport U (\ Z → Z) (first (dirglue2 A B C f g (1₂ , 0₂))) (first B)
              ( first (dirglue2-10=B-EqΣ A B C f g)) (coe-BE a-in-0))
          ( first (dirglue2-equiv-10 A B C f g) (coe-BE a-in-0))
          ( transport-first-eq-pair (is-a-cov funext weakfunext) (dirglue2 A B C f g (1₂ , 0₂)) B
              ( dirglue2-10=B-EqΣ A B C f g) (coe-BE a-in-0))
          ( transport-ua (first (dirglue2 A B C f g (1₂ , 0₂))) (first B) (dirglue2-equiv-10 A B C f g) (coe-BE a-in-0)))
      ( concat (first B)
          ( first (dirglue2-equiv-10 A B C f g) (coe-BE a-in-0))
          ( first (dirglue2-equiv-10 A B C f g) (first a-in-0 , second a-in-0))
          ( f a)
          ( ap (first (dirglue2 A B C f g (1₂ , 0₂))) (first B)
              ( coe-BE a-in-0) (first a-in-0 , second a-in-0)
              ( \ z → first (dirglue2-equiv-10 A B C f g) z)
              ( amazing-covariant-uniqueness-line-II (\ (t : 𝕀 | TOP) → first (dirglue2 A B C f g (t , 0₂)))
                  ( s-is-covariant-arrow-II (\ t → dirglue2 A B C f g (t , 0₂)))
                  ( a-in-0) (first a-in-0 , second a-in-0) (\ (t : 𝕀) → (first a-in-0 , second a-in-0))))
          ( concat (first B)
              ( first (dirglue2-equiv-10 A B C f g) (first a-in-0 , second a-in-0))
              ( f (first ff))
              ( f a)
              ( rev (first B) (f (first ff)) (first bf) (second ff))
              ( ap (first A) (first B) (first ff) a f
                  ( concat (first A)
                      ( first (dirglue2-equiv-00 A B C f g) a-in-0)
                      ( transport S (\ s → first s) (dirglue2 A B C f g (0₂ , 0₂)) A (dirglue2_00=A A B C f g) a-in-0)
                      ( a)
                      ( rev (first A)
                          ( transport S (\ s → first s) (dirglue2 A B C f g (0₂ , 0₂)) A (dirglue2_00=A A B C f g) a-in-0)
                          ( first (dirglue2-equiv-00 A B C f g) a-in-0)
                          ( concat (first A)
                              ( transport S (\ s → first s) (dirglue2 A B C f g (0₂ , 0₂)) A (dirglue2_00=A A B C f g) a-in-0)
                              ( transport U (\ Z → Z) (first (dirglue2 A B C f g (0₂ , 0₂))) (first A)
                                  ( first (dirglue2-00=A-EqΣ A B C f g)) a-in-0)
                              ( first (dirglue2-equiv-00 A B C f g) a-in-0)
                              ( transport-first-eq-pair (is-a-cov funext weakfunext) (dirglue2 A B C f g (0₂ , 0₂)) A
                                  ( dirglue2-00=A-EqΣ A B C f g) a-in-0)
                              ( transport-ua (first (dirglue2 A B C f g (0₂ , 0₂))) (first A) (dirglue2-equiv-00 A B C f g) a-in-0)))
                      ( transport-transport-rev S (\ s → first s) (dirglue2 A B C f g (0₂ , 0₂)) A (dirglue2_00=A A B C f g) a)))))

#def coe-dirglue2-bottom-is-f uses (funext weakfunext extext)
  ( A B C : S)
  ( f : first A → first B)
  ( g : first B → first C)
  : product-transport S S (\ X Y → first X → first Y)
      ( dirglue2 A B C f g (0₂ , 0₂)) A
      ( dirglue2 A B C f g (1₂ , 0₂)) B
      ( dirglue2_00=A A B C f g) (dirglue2_10=B A B C f g)
      ( covariant-transport-line-II (\ (t : 𝕀 | TOP) → first (dirglue2 A B C f g (t , 0₂)))
          ( s-is-covariant-arrow-II (\ t → dirglue2 A B C f g (t , 0₂))) (\ k → form k))
    = f
  :=
    concat (first A → first B)
      ( product-transport S S (\ X Y → first X → first Y)
          ( dirglue2 A B C f g (0₂ , 0₂)) A (dirglue2 A B C f g (1₂ , 0₂)) B
          ( dirglue2_00=A A B C f g) (dirglue2_10=B A B C f g)
          ( covariant-transport-line-II (\ (t : 𝕀 | TOP) → first (dirglue2 A B C f g (t , 0₂)))
              ( s-is-covariant-arrow-II (\ t → dirglue2 A B C f g (t , 0₂))) (\ k → form k)))
      ( \ (a : first A) →
          transport S (\ s → first s) (dirglue2 A B C f g (1₂ , 0₂)) B (dirglue2_10=B A B C f g)
            ( covariant-transport-line-II (\ (t : 𝕀 | TOP) → first (dirglue2 A B C f g (t , 0₂)))
                ( s-is-covariant-arrow-II (\ t → dirglue2 A B C f g (t , 0₂))) (\ k → form k)
                ( transport-rev S (\ s → first s) (dirglue2 A B C f g (0₂ , 0₂)) A (dirglue2_00=A A B C f g) a)))
      ( f)
      ( product-transport-fun S (\ s → first s)
          ( dirglue2 A B C f g (0₂ , 0₂)) A (dirglue2 A B C f g (1₂ , 0₂)) B
          ( dirglue2_00=A A B C f g) (dirglue2_10=B A B C f g)
          ( covariant-transport-line-II (\ (t : 𝕀 | TOP) → first (dirglue2 A B C f g (t , 0₂)))
              ( s-is-covariant-arrow-II (\ t → dirglue2 A B C f g (t , 0₂))) (\ k → form k)))
      ( eq-htpy funext (first A) (\ _ → first B)
          ( \ (a : first A) →
              transport S (\ s → first s) (dirglue2 A B C f g (1₂ , 0₂)) B (dirglue2_10=B A B C f g)
                ( covariant-transport-line-II (\ (t : 𝕀 | TOP) → first (dirglue2 A B C f g (t , 0₂)))
                    ( s-is-covariant-arrow-II (\ t → dirglue2 A B C f g (t , 0₂))) (\ k → form k)
                    ( transport-rev S (\ s → first s) (dirglue2 A B C f g (0₂ , 0₂)) A (dirglue2_00=A A B C f g) a)))
          ( f)
          ( coe-dirglue2-bottom-is-f-pointwise A B C f g))

#def coe-dirglue2-right-is-g-pointwise uses (funext weakfunext extext)
  ( A B C : S)
  ( f : first A → first B)
  ( g : first B → first C)
  ( b : first B)
  : transport S (\ s → first s) (dirglue2 A B C f g (1₂ , 1₂)) C (dirglue2_11=C A B C f g)
      ( covariant-transport-line-II (\ (s : 𝕀 | TOP) → first (dirglue2 A B C f g (1₂ , s)))
          ( s-is-covariant-arrow-II (\ s → dirglue2 A B C f g (1₂ , s))) (\ k → form k)
          ( transport-rev S (\ s → first s) (dirglue2 A B C f g (1₂ , 0₂)) B (dirglue2_10=B A B C f g) b))
    = g b
  :=
    let coe-RE : first (dirglue2 A B C f g (1₂ , 0₂)) → first (dirglue2 A B C f g (1₂ , 1₂))
      := covariant-transport-line-II (\ (s : 𝕀 | TOP) → first (dirglue2 A B C f g (1₂ , s)))
           ( s-is-covariant-arrow-II (\ s → dirglue2 A B C f g (1₂ , s))) (\ k → form k) in
    let b-in-0 : first (dirglue2 A B C f g (1₂ , 0₂))
      := transport-rev S (\ s → first s) (dirglue2 A B C f g (1₂ , 0₂)) B (dirglue2_10=B A B C f g) b in
    let bf : fib (first B) (first C) g (first b-in-0)
      := first ((second b-in-0) *₁) in
    concat (first C)
      ( transport S (\ s → first s) (dirglue2 A B C f g (1₂ , 1₂)) C (dirglue2_11=C A B C f g) (coe-RE b-in-0))
      ( first (dirglue2-equiv-11 A B C f g) (coe-RE b-in-0))
      ( g b)
      ( concat (first C)
          ( transport S (\ s → first s) (dirglue2 A B C f g (1₂ , 1₂)) C (dirglue2_11=C A B C f g) (coe-RE b-in-0))
          ( transport U (\ Z → Z) (first (dirglue2 A B C f g (1₂ , 1₂))) (first C)
              ( first (dirglue2-11=C-EqΣ A B C f g)) (coe-RE b-in-0))
          ( first (dirglue2-equiv-11 A B C f g) (coe-RE b-in-0))
          ( transport-first-eq-pair (is-a-cov funext weakfunext) (dirglue2 A B C f g (1₂ , 1₂)) C
              ( dirglue2-11=C-EqΣ A B C f g) (coe-RE b-in-0))
          ( transport-ua (first (dirglue2 A B C f g (1₂ , 1₂))) (first C) (dirglue2-equiv-11 A B C f g) (coe-RE b-in-0)))
      ( concat (first C)
          ( first (dirglue2-equiv-11 A B C f g) (coe-RE b-in-0))
          ( first (dirglue2-equiv-11 A B C f g) (first b-in-0 , second b-in-0))
          ( g b)
          ( ap (first (dirglue2 A B C f g (1₂ , 1₂))) (first C)
              ( coe-RE b-in-0) (first b-in-0 , second b-in-0)
              ( \ z → first (dirglue2-equiv-11 A B C f g) z)
              ( amazing-covariant-uniqueness-line-II (\ (s : 𝕀 | TOP) → first (dirglue2 A B C f g (1₂ , s)))
                  ( s-is-covariant-arrow-II (\ s → dirglue2 A B C f g (1₂ , s)))
                  ( b-in-0) (first b-in-0 , second b-in-0) (\ (s : 𝕀) → (first b-in-0 , second b-in-0))))
          ( concat (first C)
              ( first (dirglue2-equiv-11 A B C f g) (first b-in-0 , second b-in-0))
              ( g (first bf))
              ( g b)
              ( rev (first C) (g (first bf)) (first b-in-0) (second bf))
              ( ap (first B) (first C) (first bf) b g
                  ( concat (first B)
                      ( first (dirglue2-equiv-10 A B C f g) b-in-0)
                      ( transport S (\ s → first s) (dirglue2 A B C f g (1₂ , 0₂)) B (dirglue2_10=B A B C f g) b-in-0)
                      ( b)
                      ( rev (first B)
                          ( transport S (\ s → first s) (dirglue2 A B C f g (1₂ , 0₂)) B (dirglue2_10=B A B C f g) b-in-0)
                          ( first (dirglue2-equiv-10 A B C f g) b-in-0)
                          ( concat (first B)
                              ( transport S (\ s → first s) (dirglue2 A B C f g (1₂ , 0₂)) B (dirglue2_10=B A B C f g) b-in-0)
                              ( transport U (\ Z → Z) (first (dirglue2 A B C f g (1₂ , 0₂))) (first B)
                                  ( first (dirglue2-10=B-EqΣ A B C f g)) b-in-0)
                              ( first (dirglue2-equiv-10 A B C f g) b-in-0)
                              ( transport-first-eq-pair (is-a-cov funext weakfunext) (dirglue2 A B C f g (1₂ , 0₂)) B
                                  ( dirglue2-10=B-EqΣ A B C f g) b-in-0)
                              ( transport-ua (first (dirglue2 A B C f g (1₂ , 0₂))) (first B) (dirglue2-equiv-10 A B C f g) b-in-0)))
                      ( transport-transport-rev S (\ s → first s) (dirglue2 A B C f g (1₂ , 0₂)) B (dirglue2_10=B A B C f g) b)))))

#def coe-dirglue2-right-is-g uses (funext weakfunext extext)
  ( A B C : S)
  ( f : first A → first B)
  ( g : first B → first C)
  : product-transport S S (\ X Y → first X → first Y)
      ( dirglue2 A B C f g (1₂ , 0₂)) B
      ( dirglue2 A B C f g (1₂ , 1₂)) C
      ( dirglue2_10=B A B C f g) (dirglue2_11=C A B C f g)
      ( covariant-transport-line-II (\ (s : 𝕀 | TOP) → first (dirglue2 A B C f g (1₂ , s)))
          ( s-is-covariant-arrow-II (\ s → dirglue2 A B C f g (1₂ , s))) (\ k → form k))
    = g
  :=
    concat (first B → first C)
      ( product-transport S S (\ X Y → first X → first Y)
          ( dirglue2 A B C f g (1₂ , 0₂)) B (dirglue2 A B C f g (1₂ , 1₂)) C
          ( dirglue2_10=B A B C f g) (dirglue2_11=C A B C f g)
          ( covariant-transport-line-II (\ (s : 𝕀 | TOP) → first (dirglue2 A B C f g (1₂ , s)))
              ( s-is-covariant-arrow-II (\ s → dirglue2 A B C f g (1₂ , s))) (\ k → form k)))
      ( \ (b : first B) →
          transport S (\ s → first s) (dirglue2 A B C f g (1₂ , 1₂)) C (dirglue2_11=C A B C f g)
            ( covariant-transport-line-II (\ (s : 𝕀 | TOP) → first (dirglue2 A B C f g (1₂ , s)))
                ( s-is-covariant-arrow-II (\ s → dirglue2 A B C f g (1₂ , s))) (\ k → form k)
                ( transport-rev S (\ s → first s) (dirglue2 A B C f g (1₂ , 0₂)) B (dirglue2_10=B A B C f g) b)))
      ( g)
      ( product-transport-fun S (\ s → first s)
          ( dirglue2 A B C f g (1₂ , 0₂)) B (dirglue2 A B C f g (1₂ , 1₂)) C
          ( dirglue2_10=B A B C f g) (dirglue2_11=C A B C f g)
          ( covariant-transport-line-II (\ (s : 𝕀 | TOP) → first (dirglue2 A B C f g (1₂ , s)))
              ( s-is-covariant-arrow-II (\ s → dirglue2 A B C f g (1₂ , s))) (\ k → form k)))
      ( eq-htpy funext (first B) (\ _ → first C)
          ( \ (b : first B) →
              transport S (\ s → first s) (dirglue2 A B C f g (1₂ , 1₂)) C (dirglue2_11=C A B C f g)
                ( covariant-transport-line-II (\ (s : 𝕀 | TOP) → first (dirglue2 A B C f g (1₂ , s)))
                    ( s-is-covariant-arrow-II (\ s → dirglue2 A B C f g (1₂ , s))) (\ k → form k)
                    ( transport-rev S (\ s → first s) (dirglue2 A B C f g (1₂ , 0₂)) B (dirglue2_10=B A B C f g) b)))
          ( g)
          ( coe-dirglue2-right-is-g-pointwise A B C f g))

#def coe-dirglue2-diagonal-is-comp-pointwise uses (funext weakfunext extext)
  ( A B C : S)
  ( f : first A → first B)
  ( g : first B → first C)
  ( a : first A)
  : transport S (\ s → first s) (dirglue2 A B C f g (1₂ , 1₂)) C (dirglue2_11=C A B C f g)
      ( covariant-transport-line-II (\ (t : 𝕀 | TOP) → first (dirglue2 A B C f g (t , t)))
          ( s-is-covariant-arrow-II (\ t → dirglue2 A B C f g (t , t))) (\ k → form k)
          ( transport-rev S (\ s → first s) (dirglue2 A B C f g (0₂ , 0₂)) A (dirglue2_00=A A B C f g) a))
    = g (f a)
  :=
    let coe-DE : first (dirglue2 A B C f g (0₂ , 0₂)) → first (dirglue2 A B C f g (1₂ , 1₂))
      := covariant-transport-line-II (\ (t : 𝕀 | TOP) → first (dirglue2 A B C f g (t , t)))
           ( s-is-covariant-arrow-II (\ t → dirglue2 A B C f g (t , t))) (\ k → form k) in
    let a-in-0 : first (dirglue2 A B C f g (0₂ , 0₂))
      := transport-rev S (\ s → first s) (dirglue2 A B C f g (0₂ , 0₂)) A (dirglue2_00=A A B C f g) a in
    let bf : fib (first B) (first C) g (first a-in-0)
      := first ((second a-in-0) *₁) in
    let ff : fib (first A) (first B) f (first bf)
      := (second ((second a-in-0) *₁)) *₁ in
    concat (first C)
      ( transport S (\ s → first s) (dirglue2 A B C f g (1₂ , 1₂)) C (dirglue2_11=C A B C f g) (coe-DE a-in-0))
      ( first (dirglue2-equiv-11 A B C f g) (coe-DE a-in-0))
      ( g (f a))
      ( concat (first C)
          ( transport S (\ s → first s) (dirglue2 A B C f g (1₂ , 1₂)) C (dirglue2_11=C A B C f g) (coe-DE a-in-0))
          ( transport U (\ Z → Z) (first (dirglue2 A B C f g (1₂ , 1₂))) (first C)
              ( first (dirglue2-11=C-EqΣ A B C f g)) (coe-DE a-in-0))
          ( first (dirglue2-equiv-11 A B C f g) (coe-DE a-in-0))
          ( transport-first-eq-pair (is-a-cov funext weakfunext) (dirglue2 A B C f g (1₂ , 1₂)) C
              ( dirglue2-11=C-EqΣ A B C f g) (coe-DE a-in-0))
          ( transport-ua (first (dirglue2 A B C f g (1₂ , 1₂))) (first C) (dirglue2-equiv-11 A B C f g) (coe-DE a-in-0)))
      ( concat (first C)
          ( first (dirglue2-equiv-11 A B C f g) (coe-DE a-in-0))
          ( first (dirglue2-equiv-11 A B C f g) (first a-in-0 , second a-in-0))
          ( g (f a))
          ( ap (first (dirglue2 A B C f g (1₂ , 1₂))) (first C)
              ( coe-DE a-in-0) (first a-in-0 , second a-in-0)
              ( \ z → first (dirglue2-equiv-11 A B C f g) z)
	              ( amazing-covariant-uniqueness-line-II (\ (t : 𝕀 | TOP) → first (dirglue2 A B C f g (t , t)))
	                  ( s-is-covariant-arrow-II (\ t → dirglue2 A B C f g (t , t)))
	                  ( a-in-0) (first a-in-0 , second a-in-0)
	                  ( \ t → (first a-in-0 , second a-in-0))))
          ( concat (first C)
              ( first a-in-0)
              ( g (first bf))
              ( g (f a))
              ( rev (first C) (g (first bf)) (first a-in-0) (second bf))
              ( ap (first B) (first C) (first bf) (f a) g
                  ( concat (first B)
                      ( first bf)
                      ( f (first ff))
                      ( f a)
                      ( rev (first B) (f (first ff)) (first bf) (second ff))
                      ( ap (first A) (first B) (first ff) a f
                          ( concat (first A)
                              ( first (dirglue2-equiv-00 A B C f g) a-in-0)
                              ( transport S (\ s → first s) (dirglue2 A B C f g (0₂ , 0₂)) A (dirglue2_00=A A B C f g) a-in-0)
                              ( a)
                              ( rev (first A)
                                  ( transport S (\ s → first s) (dirglue2 A B C f g (0₂ , 0₂)) A (dirglue2_00=A A B C f g) a-in-0)
                                  ( first (dirglue2-equiv-00 A B C f g) a-in-0)
                                  ( concat (first A)
                                      ( transport S (\ s → first s) (dirglue2 A B C f g (0₂ , 0₂)) A (dirglue2_00=A A B C f g) a-in-0)
                                      ( transport U (\ Z → Z) (first (dirglue2 A B C f g (0₂ , 0₂))) (first A)
                                          ( first (dirglue2-00=A-EqΣ A B C f g)) a-in-0)
                                      ( first (dirglue2-equiv-00 A B C f g) a-in-0)
                                      ( transport-first-eq-pair (is-a-cov funext weakfunext) (dirglue2 A B C f g (0₂ , 0₂)) A
                                          ( dirglue2-00=A-EqΣ A B C f g) a-in-0)
                                      ( transport-ua (first (dirglue2 A B C f g (0₂ , 0₂))) (first A) (dirglue2-equiv-00 A B C f g) a-in-0)))
                              ( transport-transport-rev S (\ s → first s) (dirglue2 A B C f g (0₂ , 0₂)) A (dirglue2_00=A A B C f g) a)))))))

#def coe-dirglue2-diagonal-is-comp uses (funext weakfunext extext)
  ( A B C : S)
  ( f : first A → first B)
  ( g : first B → first C)
  : product-transport S S (\ X Y → first X → first Y)
      ( dirglue2 A B C f g (0₂ , 0₂)) A
      ( dirglue2 A B C f g (1₂ , 1₂)) C
      ( dirglue2_00=A A B C f g) (dirglue2_11=C A B C f g)
      ( covariant-transport-line-II (\ (t : 𝕀 | TOP) → first (dirglue2 A B C f g (t , t)))
          ( s-is-covariant-arrow-II (\ t → dirglue2 A B C f g (t , t))) (\ k → form k))
    = comp (first A) (first B) (first C) g f
  :=
    concat (first A → first C)
      ( product-transport S S (\ X Y → first X → first Y)
          ( dirglue2 A B C f g (0₂ , 0₂)) A (dirglue2 A B C f g (1₂ , 1₂)) C
          ( dirglue2_00=A A B C f g) (dirglue2_11=C A B C f g)
          ( covariant-transport-line-II (\ (t : 𝕀 | TOP) → first (dirglue2 A B C f g (t , t)))
              ( s-is-covariant-arrow-II (\ t → dirglue2 A B C f g (t , t))) (\ k → form k)))
      ( \ (a : first A) →
          transport S (\ s → first s) (dirglue2 A B C f g (1₂ , 1₂)) C (dirglue2_11=C A B C f g)
            ( covariant-transport-line-II (\ (t : 𝕀 | TOP) → first (dirglue2 A B C f g (t , t)))
                ( s-is-covariant-arrow-II (\ t → dirglue2 A B C f g (t , t))) (\ k → form k)
                ( transport-rev S (\ s → first s) (dirglue2 A B C f g (0₂ , 0₂)) A (dirglue2_00=A A B C f g) a)))
      ( comp (first A) (first B) (first C) g f)
      ( product-transport-fun S (\ s → first s)
          ( dirglue2 A B C f g (0₂ , 0₂)) A (dirglue2 A B C f g (1₂ , 1₂)) C
          ( dirglue2_00=A A B C f g) (dirglue2_11=C A B C f g)
          ( covariant-transport-line-II (\ (t : 𝕀 | TOP) → first (dirglue2 A B C f g (t , t)))
              ( s-is-covariant-arrow-II (\ t → dirglue2 A B C f g (t , t))) (\ k → form k)))
      ( eq-htpy funext (first A) (\ _ → first C)
          ( \ (a : first A) →
              transport S (\ s → first s) (dirglue2 A B C f g (1₂ , 1₂)) C (dirglue2_11=C A B C f g)
                ( covariant-transport-line-II (\ (t : 𝕀 | TOP) → first (dirglue2 A B C f g (t , t)))
                    ( s-is-covariant-arrow-II (\ t → dirglue2 A B C f g (t , t))) (\ k → form k)
                    ( transport-rev S (\ s → first s) (dirglue2 A B C f g (0₂ , 0₂)) A (dirglue2_00=A A B C f g) a)))
          ( comp (first A) (first B) (first C) g f)
          ( coe-dirglue2-diagonal-is-comp-pointwise A B C f g))

#def hom-II-in-S-diagonal-transport uses (funext weakfunext)
  ( F G : ((t , s) : Δ²-II) → S)
  ( p : F = G)
  : let e : Eq-Σ-over-product
        ( S)
        ( S)
        ( \ X Y → first X → first Y)
        ( mor2fun (\ t → F (t , t)))
        ( mor2fun (\ t → G (t , t)))
      :=
        triple-eq
          ( S)
          ( S)
          ( \ X Y → first X → first Y)
          ( mor2fun (\ t → F (t , t)))
          ( mor2fun (\ t → G (t , t)))
          ( ap
            ( ((t , s) : Δ²-II) → S)
            ( Σ ( X : S) , (Σ (Y : S) , first X → first Y))
            F G
            ( \ H → mor2fun (\ t → H (t , t)))
            p)
    in
    product-transport S S (\ X Y → first X → first Y)
      ( first (mor2fun (\ t → F (t , t))))
      ( first (mor2fun (\ t → G (t , t))))
      ( first (second (mor2fun (\ t → F (t , t)))))
      ( first (second (mor2fun (\ t → G (t , t)))))
      ( first e)
      ( first (second e))
      ( second (second (mor2fun (\ t → F (t , t)))))
    =
      second (second (mor2fun (\ t → G (t , t))))
  :=
    let e : Eq-Σ-over-product
        ( S)
        ( S)
        ( \ X Y → first X → first Y)
        ( mor2fun (\ t → F (t , t)))
        ( mor2fun (\ t → G (t , t)))
      :=
        triple-eq
          ( S)
          ( S)
          ( \ X Y → first X → first Y)
          ( mor2fun (\ t → F (t , t)))
          ( mor2fun (\ t → G (t , t)))
          ( ap
            ( ((t , s) : Δ²-II) → S)
            ( Σ ( X : S) , (Σ (Y : S) , first X → first Y))
            F G
            ( \ H → mor2fun (\ t → H (t , t)))
            p)
    in
    second (second e)

#def hom-II-in-S-diagonal-dirglue2 uses (funext weakfunext extext)
  ( a b c : S)
  ( f : first a → first b)
  ( g : first b → first c)
  : hom-II-in-S
      ( dirglue2 a b c f g (0₂ , 0₂))
      ( dirglue2 a b c f g (1₂ , 1₂))
      ( \ t → dirglue2 a b c f g (t , t))
    =
    comp
      ( first (dirglue2 a b c f g (0₂ , 0₂)))
      ( first (dirglue2 a b c f g (1₂ , 0₂)))
      ( first (dirglue2 a b c f g (1₂ , 1₂)))
      ( hom-II-in-S
        ( dirglue2 a b c f g (1₂ , 0₂))
        ( dirglue2 a b c f g (1₂ , 1₂))
        ( \ t → dirglue2 a b c f g (1₂ , t)))
      ( hom-II-in-S
        ( dirglue2 a b c f g (0₂ , 0₂))
        ( dirglue2 a b c f g (1₂ , 0₂))
        ( \ t → dirglue2 a b c f g (t , 0₂)))
  :=
    let d : ((t , s) : Δ²-II) → S
      := dirglue2 a b c f g in
    let d00 : S := d (0₂ , 0₂) in
    let d10 : S := d (1₂ , 0₂) in
    let d11 : S := d (1₂ , 1₂) in
    let d-bottom : first d00 → first d10
      := hom-II-in-S d00 d10 (\ t → d (t , 0₂)) in
    let d-right : first d10 → first d11
      := hom-II-in-S d10 d11 (\ t → d (1₂ , t)) in
    product-transport-cancel
      ( S)
      ( S)
      ( \ X Y → first X → first Y)
      ( d00) (a)
      ( d11) (c)
      ( dirglue2_00=A a b c f g)
      ( dirglue2_11=C a b c f g)
      ( hom-II-in-S d00 d11 (\ t → d (t , t)))
      ( comp (first d00) (first d10) (first d11) d-right d-bottom)
      ( concat
        ( first a → first c)
        ( product-transport S S (\ X Y → first X → first Y)
          d00 a d11 c
          ( dirglue2_00=A a b c f g)
          ( dirglue2_11=C a b c f g)
          ( hom-II-in-S d00 d11 (\ t → d (t , t))))
        ( comp (first a) (first b) (first c) g f)
        ( product-transport S S (\ X Y → first X → first Y)
          d00 a d11 c
          ( dirglue2_00=A a b c f g)
          ( dirglue2_11=C a b c f g)
          ( comp (first d00) (first d10) (first d11) d-right d-bottom))
        ( coe-dirglue2-diagonal-is-comp a b c f g)
        ( rev
          ( first a → first c)
          ( product-transport S S (\ X Y → first X → first Y)
            d00 a d11 c
            ( dirglue2_00=A a b c f g)
            ( dirglue2_11=C a b c f g)
            ( comp (first d00) (first d10) (first d11) d-right d-bottom))
          ( comp (first a) (first b) (first c) g f)
          ( concat
            ( first a → first c)
            ( product-transport S S (\ X Y → first X → first Y)
              d00 a d11 c
              ( dirglue2_00=A a b c f g)
              ( dirglue2_11=C a b c f g)
              ( comp (first d00) (first d10) (first d11) d-right d-bottom))
            ( comp
              ( first a)
              ( first b)
              ( first c)
              ( product-transport S S (\ X Y → first X → first Y)
                d10 b d11 c
                ( dirglue2_10=B a b c f g)
                ( dirglue2_11=C a b c f g)
                d-right)
              ( product-transport S S (\ X Y → first X → first Y)
                d00 a d10 b
                ( dirglue2_00=A a b c f g)
                ( dirglue2_10=B a b c f g)
                d-bottom))
            ( comp (first a) (first b) (first c) g f)
            ( product-transport-comp
              ( S)
              ( \ X → first X)
              ( d00) (a)
              ( d10) (b)
              ( d11) (c)
              ( dirglue2_00=A a b c f g)
              ( dirglue2_10=B a b c f g)
              ( dirglue2_11=C a b c f g)
              ( d-bottom)
              ( d-right))
            ( concat
              ( first a → first c)
              ( comp
                ( first a)
                ( first b)
                ( first c)
                ( product-transport S S (\ X Y → first X → first Y)
                  d10 b d11 c
                  ( dirglue2_10=B a b c f g)
                  ( dirglue2_11=C a b c f g)
                  d-right)
                ( product-transport S S (\ X Y → first X → first Y)
                  d00 a d10 b
                  ( dirglue2_00=A a b c f g)
                  ( dirglue2_10=B a b c f g)
                  d-bottom))
              ( comp
                ( first a)
                ( first b)
                ( first c)
                ( g)
                ( product-transport S S (\ X Y → first X → first Y)
                  d00 a d10 b
                  ( dirglue2_00=A a b c f g)
                  ( dirglue2_10=B a b c f g)
                  d-bottom))
              ( comp (first a) (first b) (first c) g f)
              ( ap
                ( first b → first c)
                ( first a → first c)
                ( product-transport S S (\ X Y → first X → first Y)
                  d10 b d11 c
                  ( dirglue2_10=B a b c f g)
                  ( dirglue2_11=C a b c f g)
                  d-right)
                ( g)
                ( \ h →
                  comp
                    ( first a)
                    ( first b)
                    ( first c)
                    h
                    ( product-transport S S (\ X Y → first X → first Y)
                      d00 a d10 b
                      ( dirglue2_00=A a b c f g)
                      ( dirglue2_10=B a b c f g)
                      d-bottom))
                ( coe-dirglue2-right-is-g a b c f g))
              ( ap
                ( first a → first b)
                ( first a → first c)
                ( product-transport S S (\ X Y → first X → first Y)
                  d00 a d10 b
                  ( dirglue2_00=A a b c f g)
                  ( dirglue2_10=B a b c f g)
                  d-bottom)
                ( f)
                ( \ h → comp (first a) (first b) (first c) g h)
                ( coe-dirglue2-bottom-is-f a b c f g))))))

#def mor2fun2-dirglue2=f uses (funext weakfunext extext)
  ( A B C : S)
  ( f : first A → first B)
  ( g : first B → first C)
  : mor2fun2 (dirglue2 A B C f g) = (A , (B , (C , (f , g))))
  :=
    eq-composable
      ( dirglue2 A B C f g (0₂ , 0₂))
      ( dirglue2 A B C f g (1₂ , 0₂))
      ( dirglue2 A B C f g (1₂ , 1₂))
      ( covariant-transport-line-II (\ (t : 𝕀 | TOP) → first (dirglue2 A B C f g (t , 0₂)))
          ( s-is-covariant-arrow-II (\ t → dirglue2 A B C f g (t , 0₂))) (\ k → form k))
      ( covariant-transport-line-II (\ (s : 𝕀 | TOP) → first (dirglue2 A B C f g (1₂ , s)))
          ( s-is-covariant-arrow-II (\ s → dirglue2 A B C f g (1₂ , s))) (\ k → form k))
      ( A) (dirglue2_00=A A B C f g)
      ( B) (dirglue2_10=B A B C f g)
      ( C) (dirglue2_11=C A B C f g)
      ( f) (coe-dirglue2-bottom-is-f A B C f g)
      ( g) (coe-dirglue2-right-is-g A B C f g)

#def dirglue2-mor2fun2=F uses (funext weakfunext extext)
  ( F : ( ( t , s) : Δ²-II) → S)
  : F = dirglue2 (F (0₂ , 0₂)) (F (1₂ , 0₂)) (F (1₂ , 1₂))
          ( second (second (mor2fun (\ t → F (t , 0₂)))))
          ( second (second (mor2fun (\ s → F (1₂ , s)))))
  :=
    let f' : first (F (0₂ , 0₂)) → first (F (1₂ , 0₂))
      := second (second (mor2fun (\ t → F (t , 0₂)))) in
    let g' : first (F (1₂ , 0₂)) → first (F (1₂ , 1₂))
      := second (second (mor2fun (\ s → F (1₂ , s)))) in
    let G : ( ( t , s) : Δ²-II) → S
      := dirglue2 (F (0₂ , 0₂)) (F (1₂ , 0₂)) (F (1₂ , 1₂)) f' g' in
    let a : ( ( t , s) : Δ²-II) → first (F (t , s)) → first (G (t , s))
      := \ (t , s) → \ x →
          ( covariant-transport-line-II (\ (r' : 𝕀 | TOP) → first (F (1₂ , sup s r')))
              ( s-is-covariant-arrow-II (\ r' → F (1₂ , sup s r'))) (\ k → form k)
              ( covariant-transport-line-II (\ (r : 𝕀 | TOP) → first (F (sup t r , s)))
                  ( s-is-covariant-arrow-II (\ r → F (sup t r , s))) (\ k → form k) x)
          , \ (u : 1 | s ≡ 0₂) →
              ( ( covariant-transport-line-II (\ (r : 𝕀 | TOP) → first (F (sup t r , 0₂)))
                    ( s-is-covariant-arrow-II (\ r → F (sup t r , 0₂))) (\ k → form k) x
                , refl )
              , \ (w : 1 | t ≡ 0₂) → (x , refl))) in
    let equiv-00 : is-equiv (first (F (0₂ , 0₂))) (first (G (0₂ , 0₂))) (a (0₂ , 0₂))
      := is-equiv-right-factor
           ( first (F (0₂ , 0₂))) (first (G (0₂ , 0₂))) (first (F (0₂ , 0₂)))
           ( a (0₂ , 0₂))
           ( \ p → first ((second ((second p) *₁)) *₁))
           ( second (dirglue2-equiv-00 (F (0₂ , 0₂)) (F (1₂ , 0₂)) (F (1₂ , 1₂)) f' g'))
           ( is-equiv-identity (first (F (0₂ , 0₂)))) in
    let equiv-10 : is-equiv (first (F (1₂ , 0₂))) (first (G (1₂ , 0₂))) (a (1₂ , 0₂))
      := is-equiv-right-factor
           ( first (F (1₂ , 0₂))) (first (G (1₂ , 0₂))) (first (F (1₂ , 0₂)))
           ( a (1₂ , 0₂))
           ( \ p → first (dirglue2-equiv-10 (F (0₂ , 0₂)) (F (1₂ , 0₂)) (F (1₂ , 1₂)) f' g') p)
           ( second (dirglue2-equiv-10 (F (0₂ , 0₂)) (F (1₂ , 0₂)) (F (1₂ , 1₂)) f' g'))
           ( is-equiv-homotopy (first (F (1₂ , 0₂))) (first (F (1₂ , 0₂)))
               ( \ x → first (dirglue2-equiv-10 (F (0₂ , 0₂)) (F (1₂ , 0₂)) (F (1₂ , 1₂)) f' g') (a (1₂ , 0₂) x))
               ( \ y → y)
               ( \ x → amazing-covariant-uniqueness-line-II (\ (r : 𝕀 | TOP) → first (F (sup 1₂ r , 0₂)))
                   ( s-is-covariant-arrow-II (\ r → F (sup 1₂ r , 0₂))) x x (\ (r : 𝕀) → x))
               ( is-equiv-identity (first (F (1₂ , 0₂))))) in
    let equiv-11 : is-equiv (first (F (1₂ , 1₂))) (first (G (1₂ , 1₂))) (a (1₂ , 1₂))
      := is-equiv-right-factor
           ( first (F (1₂ , 1₂))) (first (G (1₂ , 1₂))) (first (F (1₂ , 1₂)))
           ( a (1₂ , 1₂))
           ( \ p → first (dirglue2-equiv-11 (F (0₂ , 0₂)) (F (1₂ , 0₂)) (F (1₂ , 1₂)) f' g') p)
           ( second (dirglue2-equiv-11 (F (0₂ , 0₂)) (F (1₂ , 0₂)) (F (1₂ , 1₂)) f' g'))
           ( is-equiv-homotopy (first (F (1₂ , 1₂))) (first (F (1₂ , 1₂)))
               ( \ x → first (dirglue2-equiv-11 (F (0₂ , 0₂)) (F (1₂ , 0₂)) (F (1₂ , 1₂)) f' g') (a (1₂ , 1₂) x))
               ( \ y → y)
               ( \ x →
                   concat (first (F (1₂ , 1₂)))
                     ( covariant-transport-line-II (\ (r' : 𝕀 | TOP) → first (F (1₂ , sup 1₂ r')))
                         ( s-is-covariant-arrow-II (\ r' → F (1₂ , sup 1₂ r'))) (\ k → form k)
                         ( covariant-transport-line-II (\ (r : 𝕀 | TOP) → first (F (sup 1₂ r , 1₂)))
                             ( s-is-covariant-arrow-II (\ r → F (sup 1₂ r , 1₂))) (\ k → form k) x))
                     ( covariant-transport-line-II (\ (r : 𝕀 | TOP) → first (F (sup 1₂ r , 1₂)))
                         ( s-is-covariant-arrow-II (\ r → F (sup 1₂ r , 1₂))) (\ k → form k) x)
                     ( x)
                     ( amazing-covariant-uniqueness-line-II (\ (r' : 𝕀 | TOP) → first (F (1₂ , sup 1₂ r')))
                         ( s-is-covariant-arrow-II (\ r' → F (1₂ , sup 1₂ r')))
                         ( covariant-transport-line-II (\ (r : 𝕀 | TOP) → first (F (sup 1₂ r , 1₂)))
                             ( s-is-covariant-arrow-II (\ r → F (sup 1₂ r , 1₂))) (\ k → form k) x)
                         ( covariant-transport-line-II (\ (r : 𝕀 | TOP) → first (F (sup 1₂ r , 1₂)))
                             ( s-is-covariant-arrow-II (\ r → F (sup 1₂ r , 1₂))) (\ k → form k) x)
                         ( \ (r' : 𝕀) → covariant-transport-line-II (\ (r : 𝕀 | TOP) → first (F (sup 1₂ r , 1₂)))
                             ( s-is-covariant-arrow-II (\ r → F (sup 1₂ r , 1₂))) (\ k → form k) x))
                     ( amazing-covariant-uniqueness-line-II (\ (r : 𝕀 | TOP) → first (F (sup 1₂ r , 1₂)))
                         ( s-is-covariant-arrow-II (\ r → F (sup 1₂ r , 1₂))) x x (\ (r : 𝕀) → x)))
               ( is-equiv-identity (first (F (1₂ , 1₂))))) in
    naiveextext-extext extext
      ( 𝕀 × 𝕀) (Δ²-II) (\ _ → BOT)
      ( \ _ → S) (\ _ → recBOT)
      ( F) (G)
      ( \ (t , s) →
          eq-pair U (is-a-cov funext weakfunext) (F (t , s)) (G (t , s))
            ( first (ua (first (F (t , s))) (first (G (t , s))))
                ( a (t , s) , is-equiv-amazing-covariant-from-vertices F G a equiv-00 equiv-10 equiv-11 (t , s))
            , first
                ( is-prop-is-a-cov funext weakfunext (first (G (t , s)))
                  ( transport U (is-a-cov funext weakfunext) (first (F (t , s))) (first (G (t , s)))
                      ( first (ua (first (F (t , s))) (first (G (t , s))))
                          ( a (t , s) , is-equiv-amazing-covariant-from-vertices F G a equiv-00 equiv-10 equiv-11 (t , s)))
                      ( second (F (t , s))))
	                  ( second (G (t , s))))))


#def hom-II-in-S-diagonal uses (funext weakfunext extext)
  ( F : ((t , s) : Δ²-II) → S)
  : hom-II-in-S (F (0₂ , 0₂)) (F (1₂ , 1₂)) (\ t → F (t , t))
    =
    comp
      ( first (F (0₂ , 0₂)))
      ( first (F (1₂ , 0₂)))
      ( first (F (1₂ , 1₂)))
      ( hom-II-in-S (F (1₂ , 0₂)) (F (1₂ , 1₂)) (\ t → F (1₂ , t)))
      ( hom-II-in-S (F (0₂ , 0₂)) (F (1₂ , 0₂)) (\ t → F (t , 0₂)))
  :=
    let f : first (F (0₂ , 0₂)) → first (F (1₂ , 0₂))
      := hom-II-in-S (F (0₂ , 0₂)) (F (1₂ , 0₂)) (\ t → F (t , 0₂)) in
    let g : first (F (1₂ , 0₂)) → first (F (1₂ , 1₂))
      := hom-II-in-S (F (1₂ , 0₂)) (F (1₂ , 1₂)) (\ t → F (1₂ , t)) in
    let d : ((t , s) : Δ²-II) → S
      := dirglue2 (F (0₂ , 0₂)) (F (1₂ , 0₂)) (F (1₂ , 1₂)) f g in
    transport
      ( ((t , s) : Δ²-II) → S)
      ( \ H →
        hom-II-in-S (H (0₂ , 0₂)) (H (1₂ , 1₂)) (\ t → H (t , t))
        =
        comp
          ( first (H (0₂ , 0₂)))
          ( first (H (1₂ , 0₂)))
          ( first (H (1₂ , 1₂)))
          ( hom-II-in-S (H (1₂ , 0₂)) (H (1₂ , 1₂)) (\ t → H (1₂ , t)))
          ( hom-II-in-S (H (0₂ , 0₂)) (H (1₂ , 0₂)) (\ t → H (t , 0₂))))
      ( d)
      ( F)
      ( rev
        ( ((t , s) : Δ²-II) → S)
        ( F)
        ( d)
        ( dirglue2-mor2fun2=F F))
      ( hom-II-in-S-diagonal-dirglue2
        ( F (0₂ , 0₂))
        ( F (1₂ , 0₂))
        ( F (1₂ , 1₂))
        ( f)
        ( g))


-- Lemma 6.16
#def equiv-dirglue2-mor2fun2 uses (funext weakfunext extext)
  : Equiv
      ( Σ ( A : S)
      , (Σ ( B : S)
        , (Σ ( C : S)
          , (Σ ( f : first A → first B)
            , (first B → first C)))))
      (( ( t , s) : Δ²-II) → S)
  :=
    ( \ (A , (B , (C , (f , g)))) → dirglue2 A B C f g
    , ( ( mor2fun2 , \ (A , (B , (C , (f , g)))) → mor2fun2-dirglue2=f A B C f g)
      , ( mor2fun2 , \ F →
            rev (( ( t , s) : Δ²-II) → S) F
              ( dirglue2 (F (0₂ , 0₂)) (F (1₂ , 0₂)) (F (1₂ , 1₂))
                  ( second (second (mor2fun (\ t → F (t , 0₂)))))
                  ( second (second (mor2fun (\ s → F (1₂ , s))))))
              ( dirglue2-mor2fun2=F F))))

#def dirglue2-bottom-is-dirglue uses (funext weakfunext extext)
  ( A B C : S)
  ( f : first A → first B)
  ( g : first B → first C)
  ( t : 𝕀)
  : dirglue2 A B C f g (t , 0₂)
  = dirglue (dirglue2 A B C f g (0₂ , 0₂)) (dirglue2 A B C f g (1₂ , 0₂))
      ( second (second (mor2fun ( \ u → dirglue2 A B C f g (u , 0₂)))))
      t
  :=
    let F : 𝕀 → S := \ u → dirglue2 A B C f g (u , 0₂) in
    ap (𝕀 → S) S F (dirglue (F 0₂) (F 1₂) (second (second (mor2fun F)))) (\ h → h t) (dirglue-mor2fun=f F)

#def dirglue2-right-is-dirglue uses (funext weakfunext extext)
  ( A B C : S)
  ( f : first A → first B)
  ( g : first B → first C)
  ( s : 𝕀)
  : dirglue2 A B C f g (1₂ , s)
  = dirglue (dirglue2 A B C f g (1₂ , 0₂)) (dirglue2 A B C f g (1₂ , 1₂))
      ( second (second (mor2fun ( \ u → dirglue2 A B C f g (1₂ , u)))))
      s
  :=
    let F : 𝕀 → S := \ u → dirglue2 A B C f g (1₂ , u) in
    ap (𝕀 → S) S F (dirglue (F 0₂) (F 1₂) (second (second (mor2fun F)))) (\ h → h s) (dirglue-mor2fun=f F)

#def dirglue2-from-horn-II uses (funext weakfunext extext)
  ( k : ( ( t₁ , t₂) : 𝕀 × 𝕀 | Δ²-II (t₁ , t₂) ∧ Λ-II (t₁ , t₂)) → S)
  : ( ( t , s) : Δ²-II) → S
  :=
    dirglue2
      ( k (0₂ , 0₂)) (k (1₂ , 0₂)) (k (1₂ , 1₂))
      ( hom-II-in-S (k (0₂ , 0₂)) (k (1₂ , 0₂)) (\ t → k (t , 0₂)))
      ( hom-II-in-S (k (1₂ , 0₂)) (k (1₂ , 1₂)) (\ t → k (1₂ , t)))

```

### The cubical horn inclusion

```rzk

#def equiv-S-simplex-to-composable-maps-II uses (funext weakfunext extext)
  : Equiv
      ( ( ( t , s) : Δ²-II) → S)
      ( Σ ( A : S)
      , (Σ ( B : S)
        , (Σ ( C : S)
          , (Σ ( f : first A → first B)
            , (first B → first C)))))
  :=
    ( mor2fun2
    , second
        ( inv-equiv
          ( Σ ( A : S)
          , (Σ ( B : S)
            , (Σ ( C : S)
              , (Σ ( f : first A → first B)
                , (first B → first C)))))
          ( ( ( t , s) : Δ²-II) → S)
          ( equiv-dirglue2-mor2fun2)))

#def equiv-S-horn-to-composable-maps-II uses (funext weakfunext extext)
  : Equiv
      ( ( ( t₁ , t₂) : 𝕀 × 𝕀 | Δ²-II (t₁ , t₂) ∧ Λ-II (t₁ , t₂)) → S)
      ( Σ ( A : S)
      , (Σ ( B : S)
        , (Σ ( C : S)
          , (Σ ( f : first A → first B)
            , (first B → first C)))))
  :=
    let horn : U
      := ( ( t₁ , t₂) : 𝕀 × 𝕀 | Δ²-II (t₁ , t₂) ∧ Λ-II (t₁ , t₂)) → S in
    let composable-hom : U
      := Σ ( A : S)
        , (Σ ( B : S)
          , (Σ ( C : S)
            , (Σ ( f : hom-II S A B)
              , (hom-II S B C)))) in
    let composable-map : U
      := Σ ( A : S)
        , (Σ ( B : S)
          , (Σ ( C : S)
            , (Σ ( f : first A → first B)
              , (first B → first C)))) in
    let horn-to-composable-hom : horn → composable-hom
      := \ k →
        ( k (0₂ , 0₂)
        , ( k (1₂ , 0₂)
          , ( k (1₂ , 1₂)
            , ( \ t → k (t , 0₂)
              , \ t → k (1₂ , t))))) in
    let composable-hom-to-horn : composable-hom → horn
      := \ (A , (B , (C , (f , g)))) → horn-II S A B C f g in
    let equiv-horn-to-composable-hom : Equiv horn composable-hom
      := ( horn-to-composable-hom
        , ( ( composable-hom-to-horn , \ _ → refl)
          , ( composable-hom-to-horn , \ _ → refl))) in
    let equiv-composable-hom-to-map : Equiv composable-hom composable-map
      := total-equiv-family-of-equiv3
        ( S)
        ( \ _ → S)
        ( \ _ _ → S)
        ( \ A B C → Σ (f : hom-II S A B) , hom-II S B C)
        ( \ A B C → Σ (f : first A → first B) , first B → first C)
        ( \ A B C →
            equiv-comp
              ( Σ (f : hom-II S A B) , hom-II S B C)
              ( Σ (f : first A → first B) , hom-II S B C)
              ( Σ (f : first A → first B) , first B → first C)
              ( equiv-total-pullback-is-equiv
                  ( hom-II S A B)
                  ( first A → first B)
                  ( hom-II-in-S A B)
                  ( is-equiv-hom-II-in-S A B)
                  ( \ _ → hom-II S B C))
              ( total-equiv-family-of-equiv
                  ( first A → first B)
                  ( \ _ → hom-II S B C)
                  ( \ _ → first B → first C)
                  ( \ _ → equiv-hom-II-in-S B C))) in
    equiv-comp horn composable-hom composable-map
      equiv-horn-to-composable-hom
      equiv-composable-hom-to-map

#def S-is-segal-II uses (funext weakfunext extext)
  : is-segal-II S
  :=
    let simplex : U := ( ( t , s) : Δ²-II) → S in
    let horn : U
      := ( ( t₁ , t₂) : 𝕀 × 𝕀 | Δ²-II (t₁ , t₂) ∧ Λ-II (t₁ , t₂)) → S in
    let composable-map : U
      := Σ ( A : S)
        , (Σ ( B : S)
          , (Σ ( C : S)
            , (Σ ( f : first A → first B)
              , (first B → first C)))) in
    let equiv-simplex-to-horn : Equiv simplex horn
      := equiv-comp
        simplex
        composable-map
        horn
        equiv-S-simplex-to-composable-maps-II
        ( inv-equiv
          horn
          composable-map
          equiv-S-horn-to-composable-maps-II) in
    is-segal-is-local-horn-inclusion-II S
      ( is-equiv-homotopy
        simplex
        horn
        ( horn-restriction-II S)
        ( first equiv-simplex-to-horn)
        ( \ F →
            rev
              horn
              ( first equiv-simplex-to-horn F)
              ( horn-restriction-II S F)
              ( inv-equiv-cancel
                horn
                composable-map
                equiv-S-horn-to-composable-maps-II
                ( horn-restriction-II S F)))
        ( second equiv-simplex-to-horn))

```

## S is Rezk-II

```rzk

#def path-in-S-is-equiv uses (funext weakfunext)
  ( x y : S)
  : Equiv (x = y) (Equiv (first x) (first y))
  :=
    equiv-comp
      ( x = y)
      ( first x = first y)
      ( Equiv (first x) (first y))
      ( ap S U x y (projection-total-type U (is-a-cov funext weakfunext))
      , is-emb-subtype-projection
          U
          ( is-a-cov funext weakfunext)
          ( is-prop-is-a-cov funext weakfunext)
          x
          y)
      ( idtoeqv (first x) (first y)
      , univalence (first x) (first y))

#def hom-II-in-S-id uses (funext weakfunext)
  ( x : S)
  : hom-II-in-S x x (id-hom-II S x) = identity (first x)
  :=
    eq-htpy funext
      ( first x)
      ( \ _ → first x)
      ( hom-II-in-S x x (id-hom-II S x))
      ( identity (first x))
      ( \ a →
          amazing-covariant-uniqueness-line-II
            ( \ (_ : 𝕀 | TOP) → first x)
            ( s-is-covariant-arrow-II (\ _ → x))
            ( a)
            ( a)
            ( \ _ → a))

#def hom-II-in-S-comp uses (funext weakfunext extext)
  ( x y z : S)
  ( f : hom-II S x y)
  ( g : hom-II S y z)
  : hom-II-in-S x z (comp-is-segal-II S S-is-segal-II x y z f g)
    = comp
        ( first x)
        ( first y)
        ( first z)
        ( hom-II-in-S y z g)
        ( hom-II-in-S x y f)
	  :=
	    hom-II-in-S-diagonal
	      ( \ (t , s) →
	          second (first (S-is-segal-II x y z f g)) (t , s))

```

### Isomorphisms in S

```rzk

#def equiv-S-retraction-law-II-to-underlying uses (funext weakfunext extext)
  ( x y : S)
  ( f : hom-II S x y)
  ( g : hom-II S y x)
  : Equiv
      ( comp-is-segal-II S S-is-segal-II x y x f g = id-hom-II S x)
      ( homotopy
        ( first x)
        ( first x)
        ( comp
          ( first x)
          ( first y)
          ( first x)
          ( hom-II-in-S y x g)
          ( hom-II-in-S x y f))
        ( identity (first x)))
  :=
    equiv-comp
      ( comp-is-segal-II S S-is-segal-II x y x f g = id-hom-II S x)
      ( hom-II-in-S x x (comp-is-segal-II S S-is-segal-II x y x f g)
        = hom-II-in-S x x (id-hom-II S x))
      ( homotopy
        ( first x)
        ( first x)
        ( comp
          ( first x)
          ( first y)
          ( first x)
          ( hom-II-in-S y x g)
          ( hom-II-in-S x y f))
        ( identity (first x)))
      ( equiv-ap-is-equiv
        ( hom-II S x x)
        ( first x → first x)
        ( hom-II-in-S x x)
        ( is-equiv-hom-II-in-S x x)
        ( comp-is-segal-II S S-is-segal-II x y x f g)
        ( id-hom-II S x))
      ( equiv-comp
        ( hom-II-in-S x x (comp-is-segal-II S S-is-segal-II x y x f g)
          = hom-II-in-S x x (id-hom-II S x))
        ( comp
          ( first x)
          ( first y)
          ( first x)
          ( hom-II-in-S y x g)
          ( hom-II-in-S x y f)
          = hom-II-in-S x x (id-hom-II S x))
        ( homotopy
          ( first x)
          ( first x)
          ( comp
            ( first x)
            ( first y)
            ( first x)
            ( hom-II-in-S y x g)
            ( hom-II-in-S x y f))
          ( identity (first x)))
        ( equiv-preconcat
          ( first x → first x)
          ( comp
            ( first x)
            ( first y)
            ( first x)
            ( hom-II-in-S y x g)
            ( hom-II-in-S x y f))
          ( hom-II-in-S x x (comp-is-segal-II S S-is-segal-II x y x f g))
          ( hom-II-in-S x x (id-hom-II S x))
          ( rev
            ( first x → first x)
            ( hom-II-in-S x x (comp-is-segal-II S S-is-segal-II x y x f g))
            ( comp
              ( first x)
              ( first y)
              ( first x)
              ( hom-II-in-S y x g)
              ( hom-II-in-S x y f))
            ( hom-II-in-S-comp x y x f g)))
        ( equiv-comp
          ( comp
            ( first x)
            ( first y)
            ( first x)
            ( hom-II-in-S y x g)
            ( hom-II-in-S x y f)
            = hom-II-in-S x x (id-hom-II S x))
          ( comp
            ( first x)
            ( first y)
            ( first x)
            ( hom-II-in-S y x g)
            ( hom-II-in-S x y f)
            = identity (first x))
          ( homotopy
            ( first x)
            ( first x)
            ( comp
              ( first x)
              ( first y)
              ( first x)
              ( hom-II-in-S y x g)
              ( hom-II-in-S x y f))
            ( identity (first x)))
          ( equiv-postconcat
            ( first x → first x)
            ( comp
              ( first x)
              ( first y)
              ( first x)
              ( hom-II-in-S y x g)
              ( hom-II-in-S x y f))
            ( hom-II-in-S x x (id-hom-II S x))
            ( identity (first x))
            ( hom-II-in-S-id x))
          ( equiv-FunExt funext
            ( first x)
            ( \ _ → first x)
            ( comp
              ( first x)
              ( first y)
              ( first x)
              ( hom-II-in-S y x g)
              ( hom-II-in-S x y f))
            ( identity (first x)))))

#def equiv-S-section-law-II-to-underlying uses (funext weakfunext extext)
  ( x y : S)
  ( f : hom-II S x y)
  ( g : hom-II S y x)
  : Equiv
      ( comp-is-segal-II S S-is-segal-II y x y g f = id-hom-II S y)
      ( homotopy
        ( first y)
        ( first y)
        ( comp
          ( first y)
          ( first x)
          ( first y)
          ( hom-II-in-S x y f)
          ( hom-II-in-S y x g))
        ( identity (first y)))
  :=
    equiv-comp
      ( comp-is-segal-II S S-is-segal-II y x y g f = id-hom-II S y)
      ( hom-II-in-S y y (comp-is-segal-II S S-is-segal-II y x y g f)
        = hom-II-in-S y y (id-hom-II S y))
      ( homotopy
        ( first y)
        ( first y)
        ( comp
          ( first y)
          ( first x)
          ( first y)
          ( hom-II-in-S x y f)
          ( hom-II-in-S y x g))
        ( identity (first y)))
      ( equiv-ap-is-equiv
        ( hom-II S y y)
        ( first y → first y)
        ( hom-II-in-S y y)
        ( is-equiv-hom-II-in-S y y)
        ( comp-is-segal-II S S-is-segal-II y x y g f)
        ( id-hom-II S y))
      ( equiv-comp
        ( hom-II-in-S y y (comp-is-segal-II S S-is-segal-II y x y g f)
          = hom-II-in-S y y (id-hom-II S y))
        ( comp
          ( first y)
          ( first x)
          ( first y)
          ( hom-II-in-S x y f)
          ( hom-II-in-S y x g)
          = hom-II-in-S y y (id-hom-II S y))
        ( homotopy
          ( first y)
          ( first y)
          ( comp
            ( first y)
            ( first x)
            ( first y)
            ( hom-II-in-S x y f)
            ( hom-II-in-S y x g))
          ( identity (first y)))
        ( equiv-preconcat
          ( first y → first y)
          ( comp
            ( first y)
            ( first x)
            ( first y)
            ( hom-II-in-S x y f)
            ( hom-II-in-S y x g))
          ( hom-II-in-S y y (comp-is-segal-II S S-is-segal-II y x y g f))
          ( hom-II-in-S y y (id-hom-II S y))
          ( rev
            ( first y → first y)
            ( hom-II-in-S y y (comp-is-segal-II S S-is-segal-II y x y g f))
            ( comp
              ( first y)
              ( first x)
              ( first y)
              ( hom-II-in-S x y f)
              ( hom-II-in-S y x g))
            ( hom-II-in-S-comp y x y g f)))
        ( equiv-comp
          ( comp
            ( first y)
            ( first x)
            ( first y)
            ( hom-II-in-S x y f)
            ( hom-II-in-S y x g)
            = hom-II-in-S y y (id-hom-II S y))
          ( comp
            ( first y)
            ( first x)
            ( first y)
            ( hom-II-in-S x y f)
            ( hom-II-in-S y x g)
            = identity (first y))
          ( homotopy
            ( first y)
            ( first y)
            ( comp
              ( first y)
              ( first x)
              ( first y)
              ( hom-II-in-S x y f)
              ( hom-II-in-S y x g))
            ( identity (first y)))
          ( equiv-postconcat
            ( first y → first y)
            ( comp
              ( first y)
              ( first x)
              ( first y)
              ( hom-II-in-S x y f)
              ( hom-II-in-S y x g))
            ( hom-II-in-S y y (id-hom-II S y))
            ( identity (first y))
            ( hom-II-in-S-id y))
          ( equiv-FunExt funext
            ( first y)
            ( \ _ → first y)
            ( comp
              ( first y)
              ( first x)
              ( first y)
              ( hom-II-in-S x y f)
              ( hom-II-in-S y x g))
            ( identity (first y)))))

#def equiv-S-retraction-arrow-II-to-underlying uses (funext weakfunext extext)
  ( x y : S)
  ( f : hom-II S x y)
  : Equiv
      ( Retraction-arrow-II S S-is-segal-II x y f)
      ( has-retraction (first x) (first y) (hom-II-in-S x y f))
  :=
    equiv-comp
      ( Retraction-arrow-II S S-is-segal-II x y f)
      ( Σ ( g : hom-II S y x)
        , homotopy
          ( first x)
          ( first x)
          ( comp
            ( first x)
            ( first y)
            ( first x)
            ( hom-II-in-S y x g)
            ( hom-II-in-S x y f))
          ( identity (first x)))
      ( has-retraction (first x) (first y) (hom-II-in-S x y f))
      ( total-equiv-family-of-equiv
        ( hom-II S y x)
        ( \ g → comp-is-segal-II S S-is-segal-II x y x f g = id-hom-II S x)
        ( \ g →
          homotopy
            ( first x)
            ( first x)
            ( comp
              ( first x)
              ( first y)
              ( first x)
              ( hom-II-in-S y x g)
              ( hom-II-in-S x y f))
            ( identity (first x)))
        ( \ g → equiv-S-retraction-law-II-to-underlying x y f g))
      ( equiv-total-pullback-is-equiv
        ( hom-II S y x)
        ( first y → first x)
        ( hom-II-in-S y x)
        ( is-equiv-hom-II-in-S y x)
        ( \ g →
          homotopy
            ( first x)
            ( first x)
            ( comp
              ( first x)
              ( first y)
              ( first x)
              ( g)
              ( hom-II-in-S x y f))
            ( identity (first x))))

#def equiv-S-section-arrow-II-to-underlying uses (funext weakfunext extext)
  ( x y : S)
  ( f : hom-II S x y)
  : Equiv
      ( Section-arrow-II S S-is-segal-II x y f)
      ( has-section (first x) (first y) (hom-II-in-S x y f))
  :=
    equiv-comp
      ( Section-arrow-II S S-is-segal-II x y f)
      ( Σ ( g : hom-II S y x)
        , homotopy
          ( first y)
          ( first y)
          ( comp
            ( first y)
            ( first x)
            ( first y)
            ( hom-II-in-S x y f)
            ( hom-II-in-S y x g))
          ( identity (first y)))
      ( has-section (first x) (first y) (hom-II-in-S x y f))
      ( total-equiv-family-of-equiv
        ( hom-II S y x)
        ( \ g → comp-is-segal-II S S-is-segal-II y x y g f = id-hom-II S y)
        ( \ g →
          homotopy
            ( first y)
            ( first y)
            ( comp
              ( first y)
              ( first x)
              ( first y)
              ( hom-II-in-S x y f)
              ( hom-II-in-S y x g))
            ( identity (first y)))
        ( \ g → equiv-S-section-law-II-to-underlying x y f g))
      ( equiv-total-pullback-is-equiv
        ( hom-II S y x)
        ( first y → first x)
        ( hom-II-in-S y x)
        ( is-equiv-hom-II-in-S y x)
        ( \ g →
          homotopy
            ( first y)
            ( first y)
            ( comp
              ( first y)
              ( first x)
              ( first y)
              ( hom-II-in-S x y f)
              ( g))
            ( identity (first y))))

#def equiv-S-is-iso-arrow-II-to-underlying uses (funext weakfunext extext)
  ( x y : S)
  ( f : hom-II S x y)
  : Equiv
      ( is-iso-arrow-II S S-is-segal-II x y f)
      ( is-equiv (first x) (first y) (hom-II-in-S x y f))
	:=
	  equiv-product-equivs
	    ( Retraction-arrow-II S S-is-segal-II x y f)
	    ( has-retraction (first x) (first y) (hom-II-in-S x y f))
	    ( equiv-S-retraction-arrow-II-to-underlying x y f)
	    ( Section-arrow-II S S-is-segal-II x y f)
	    ( has-section (first x) (first y) (hom-II-in-S x y f))
	    ( equiv-S-section-arrow-II-to-underlying x y f)

#def S-Iso-is-Equiv uses (funext weakfunext extext)
  ( x y : S)
  : Equiv (Iso-II S S-is-segal-II x y) (Equiv (first x) (first y))
  :=
    equiv-comp
      ( Iso-II S S-is-segal-II x y)
      ( Σ ( f : hom-II S x y)
        , is-equiv (first x) (first y) (hom-II-in-S x y f))
      ( Equiv (first x) (first y))
      ( total-equiv-family-of-equiv
        ( hom-II S x y)
        ( \ f → is-iso-arrow-II S S-is-segal-II x y f)
        ( \ f → is-equiv (first x) (first y) (hom-II-in-S x y f))
        ( \ f → equiv-S-is-iso-arrow-II-to-underlying x y f))
      ( equiv-total-pullback-is-equiv
        ( hom-II S x y)
        ( first x → first y)
        ( hom-II-in-S x y)
        ( is-equiv-hom-II-in-S x y)
        ( \ f → is-equiv (first x) (first y) f))

```

### The path-to-iso comparison

```rzk

#def is-prop-is-iso-arrow-II-S uses (funext weakfunext extext)
  ( x y : S)
  ( f : hom-II S x y)
  : is-prop (is-iso-arrow-II S S-is-segal-II x y f)
  :=
    is-prop-is-retract-of-is-prop
      ( is-iso-arrow-II S S-is-segal-II x y f)
      ( is-equiv (first x) (first y) (hom-II-in-S x y f))
      ( first (equiv-S-is-iso-arrow-II-to-underlying x y f)
      , first (second (equiv-S-is-iso-arrow-II-to-underlying x y f)))
      ( is-prop-is-equiv funext
        ( first x)
        ( first y)
        ( hom-II-in-S x y f))

#def eq-S-Iso-II-eq-first uses (funext weakfunext extext)
  ( x y : S)
  ( iso iso' : Iso-II S S-is-segal-II x y)
  ( p : first iso = first iso')
  : iso = iso'
  :=
    path-of-pairs-pair-of-paths
      ( hom-II S x y)
      ( \ f → is-iso-arrow-II S S-is-segal-II x y f)
      ( first iso)
      ( first iso')
      ( p)
      ( second iso)
      ( second iso')
      ( first
        ( ( is-prop-is-iso-arrow-II-S x y (first iso'))
          ( transport
            ( hom-II S x y)
            ( \ f → is-iso-arrow-II S S-is-segal-II x y f)
            ( first iso)
            ( first iso')
            ( p)
            ( second iso))
          ( second iso')))

#def hom-II-in-S-iso-eq-II-is-path-map uses (funext weakfunext extext)
  ( x y : S)
  ( p : x = y)
  : hom-II-in-S x y (first (iso-eq-II S S-is-segal-II x y p))
    = first (first (path-in-S-is-equiv x y) p)
  :=
    ind-path
      ( S)
      ( x)
      ( \ y' p' →
        hom-II-in-S x y' (first (iso-eq-II S S-is-segal-II x y' p'))
        = first (first (path-in-S-is-equiv x y') p'))
      ( hom-II-in-S-id x)
      ( y)
      ( p)

#def iso-eq-II-S-is-path-in-S-is-equiv uses (funext weakfunext extext)
  ( x y : S)
  : homotopy
      ( x = y)
      ( Iso-II S S-is-segal-II x y)
      ( iso-eq-II S S-is-segal-II x y)
      ( comp
        ( x = y)
        ( Equiv (first x) (first y))
        ( Iso-II S S-is-segal-II x y)
        ( first
          ( inv-equiv
            ( Iso-II S S-is-segal-II x y)
            ( Equiv (first x) (first y))
            ( S-Iso-is-Equiv x y)))
        ( first (path-in-S-is-equiv x y)))
  :=
    \ p →
      let iso : Iso-II S S-is-segal-II x y
        := first
          ( inv-equiv
            ( Iso-II S S-is-segal-II x y)
            ( Equiv (first x) (first y))
            ( S-Iso-is-Equiv x y))
          ( first (path-in-S-is-equiv x y) p) in
      eq-S-Iso-II-eq-first
        x y
        ( iso-eq-II S S-is-segal-II x y p)
        ( iso)
        ( ap-cancel-has-retraction
          ( hom-II S x y)
          ( first x → first y)
          ( hom-II-in-S x y)
          ( first (is-equiv-hom-II-in-S x y))
          ( first (iso-eq-II S S-is-segal-II x y p))
          ( first iso)
          ( concat
            ( first x → first y)
            ( hom-II-in-S x y (first (iso-eq-II S S-is-segal-II x y p)))
            ( first (first (path-in-S-is-equiv x y) p))
            ( hom-II-in-S x y (first iso))
            ( hom-II-in-S-iso-eq-II-is-path-map x y p)
            ( rev
              ( first x → first y)
              ( hom-II-in-S x y (first iso))
              ( first (first (path-in-S-is-equiv x y) p))
              ( first-path-Σ
                ( first x → first y)
                ( \ f → is-equiv (first x) (first y) f)
                ( first (S-Iso-is-Equiv x y) iso)
                ( first (path-in-S-is-equiv x y) p)
                ( inv-equiv-cancel'
                  ( Iso-II S S-is-segal-II x y)
                  ( Equiv (first x) (first y))
                  ( S-Iso-is-Equiv x y)
                  ( first (path-in-S-is-equiv x y) p))))))

```

### Rezkness of S

```rzk

#def S-is-rezk-II uses (funext weakfunext extext)
  : is-rezk-II S
  :=
    ( S-is-segal-II
    , \ x y →
        let path-to-equiv : Equiv (x = y) (Equiv (first x) (first y))
          := path-in-S-is-equiv x y in
        let iso-to-equiv : Equiv (Iso-II S S-is-segal-II x y) (Equiv (first x) (first y))
          := S-Iso-is-Equiv x y in
        is-equiv-homotopy
          ( x = y)
          ( Iso-II S S-is-segal-II x y)
          ( iso-eq-II S S-is-segal-II x y)
          ( comp
            ( x = y)
            ( Equiv (first x) (first y))
            ( Iso-II S S-is-segal-II x y)
            ( first
              ( inv-equiv
                ( Iso-II S S-is-segal-II x y)
                ( Equiv (first x) (first y))
                iso-to-equiv))
            ( first path-to-equiv))
          ( iso-eq-II-S-is-path-in-S-is-equiv x y)
          ( is-equiv-comp
            ( x = y)
            ( Equiv (first x) (first y))
            ( Iso-II S S-is-segal-II x y)
            ( first path-to-equiv)
            ( second path-to-equiv)
            ( first
              ( inv-equiv
                ( Iso-II S S-is-segal-II x y)
                ( Equiv (first x) (first y))
                iso-to-equiv))
            ( second
              ( inv-equiv
                ( Iso-II S S-is-segal-II x y)
                ( Equiv (first x) (first y))
                iso-to-equiv))))

```
