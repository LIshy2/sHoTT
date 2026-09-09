# 4. Amazing covariance

This is a literate `rzk` file: `is-covariant-arrow-II`, amazing covariance
`is-a-cov`, and the extension theorem `is-a-cov-ext`. Directed univalence lives in
`05-diruniv.rzk.md`; the ordinary (non-amazing) covariance draft in `03-cub-covariant.rzk.md`.

```rzk
#lang rzk-1

#assume funext : FunExt
#assume weakfunext : WeakFunExt
#assume extext : ExtExt
```

## Prerequisites

- `hott/01-paths.rzk.md` — `ap`, `rev`, `concat`, `transport`.
- `hott/03-equivalences.rzk.md` — `Equiv`, `is-equiv`, `FunExt`, `eq-htpy`, `htpy-eq`, `equiv-comp`, `inv-ap-is-emb`.
- `hott/04-modalities.rzk.md` — `b-map`, `b-equiv`, `b-elim`, `b-path-commute-fwd`.
- `hott/05-half-adjoint-equivalences.rzk.md` — `is-emb-is-equiv`.
- `hott/06-sigma.rzk.md` — `eq-pair`, `total-type`.
- `hott/07-contractible.rzk.md` — `is-contr`, `WeakFunExt`, `equiv-total-type-is-contr-fiber`, `transport-section-eq-at`, `transport-section-eq-at-cancel`.
- `hott/08-fibers.rzk.md` — `fib`.
- `hott/09-families-of-maps.rzk.md` — `total-equiv-family-of-equiv`, `total-b-equiv-family2`.
- `hott/10-propositions.rzk.md` — `is-prop-Unit`, `is-prop-is-prop`, `is-prop-flat`.
- `hott/11-trivial-fibrations.rzk.md` — `is-equiv-domain-sum-of-fibers`.
- `simplicial-hott/03-extension-types.rzk.md` — `ExtExt`, `naiveextext-extext`, `ap-ext-eq-htpy-at`.
- `simplicial-hott/04-right-orthogonal.rzk.md` — RS17 Thm 8.5 / pullback via right orthogonality.
- `simplicial-hott/07-discrete.rzk.md` — `is-discrete`, `is-discrete-function-type`, `is-discrete-extension-type`, `is-discrete-Σ`, `is-discrete-Id`, `is-discrete-op`, `is-contr-of-op`.
- `hott/06-sigma.rzk.md` — `equiv-dependent-curry`, `inv-equiv-dependent-curry`, `equiv-choice3`.
- `simplicial-hott/03-extension-types.rzk.md` — `equiv-ext-shape-fun`.
- `hott/04-modalities.rzk.md` — Modality operations and type aliases.
- `simplicial-hott/05-segal-types.rzk.md` — `hom`, `hom-II`, `dhom-II`, `dhom-from-II`.
- `simplicial-hott/02-simplicial-type-theory.rzk.md` — `shape-at-1`, `equiv-shape-1-op-uninv`, `shape-at-1-of-eq-form-1`, `eq-form-1-of-shape-at-1`, `is-prop-shape-at-1`, `fun-monotonicity-at`, `fun-monotonicity`, `sec-shape-at-1-along-form`, `dhom-II-form-line-shape-at-1`, `is-prop-dhom-II-form-line-shape-at-1`, `is-prop-Σ-dhom-II-form-line-shape-at-1`.
- `triangulated/03-cub-covariant.rzk.md` — `is-covariant-arrow-II`, `covariant-transport-line-II`, `covariant-transport-line-inv-II`, `equiv-is-cov-i-coslice`, `is-covariant-arrow-II-coslice`, `is-covariant-ext`.


## Covariant families

```rzk

#def is-prop-is-covariant-arrow-II uses (weakfunext funext)
  ( A : (t : 𝕀 | TOP) → U)
  : is-prop (is-covariant-arrow-II A)
  := is-prop-is-covariant-II
      funext weakfunext ⌈𝕀⌉ (equiv-ext-shape-family-fwd 𝕀 □¹ (\ t → A t))

#def is-covariant-arrow-II-Prop uses (weakfunext funext) (A : (t : 𝕀 | TOP) → U)
  : Prop
  := (is-covariant-arrow-II A , is-prop-is-covariant-arrow-II A)

#def equiv-pointwise-op-I-U
  : Equiv ((i : 𝕀) → ᵒᵖ U) (ᵒᵖ (𝕀 → U))
  :=
    inv-equiv
      ( ᵒᵖ (𝕀 → U))
      ( (i : 𝕀) → ᵒᵖ U)
      ( op-ext-commute-equiv (\ (_ : 𝕀) → U))
```

## Amazing covariance

Definition 5.10

```rzk

#def is-a-cov uses (funext weakfunext) (X : U)
  : U
  := amazing-predicate is-covariant-arrow-II-Prop X

#def is-prop-is-a-cov uses (funext weakfunext) (A : U)
  : is-prop (is-a-cov A)
  := is-prop-amazing-predicate funext is-covariant-arrow-II-Prop A

```

## Amazing covariance machinery

Lemma 5.11
```rzk
#def is-a-cov-transpose uses (funext weakfunext)
  ( A :♭ U)
  ( h :♭ A → U)
  ( f :♭ (a : A) → is-a-cov (h a))
  : ( ♭ ( ( g : 𝕀 → A) → is-covariant-arrow-II (\ b → h (g b))))
  := amazing-transpose funext weakfunext (is-covariant-arrow-II-Prop) (A) (h) (f)

#def is-a-cov-untranspose uses (funext weakfunext)
  ( A :♭ U)
  ( h :♭ A → U)
  ( f :♭ (g : 𝕀 → A) → is-covariant-arrow-II (\ b → h (g b)))
  : ( ♭ ( ( a : A) → is-a-cov (h a)))
  := amazing-untranspose (is-covariant-arrow-II-Prop) (A) (h) (f)

#def is-a-cov-transposition-equiv uses (funext weakfunext)
  ( A :♭ U)
  ( h :♭ A → U)
  : Equiv
    ( ♭ ( ( a : A) → is-a-cov (h a)))
    ( ♭ ( ( g : 𝕀 → A) → is-covariant-arrow-II (\ b → h (g b))))
  := amazing-transpose-untranspose-equiv funext weakfunext (is-covariant-arrow-II-Prop) (A) (h)

#def amazing-covariant-uniqueness-line-II
  ( A : (t : 𝕀 | TOP) → U)
  ( cov : is-covariant-arrow-II A)
  ( a0 : A 0₂)
  ( a1 : A 1₂)
  ( h : dhom-II ⌈𝕀⌉
      (pt-⌈𝕀⌉ 0₂) (pt-⌈𝕀⌉ 1₂) (\ t → pt-⌈𝕀⌉ t)
      (equiv-ext-shape-family-fwd 𝕀 □¹ (\ t → A t)) a0 a1)
  : covariant-transport-line-II A cov (\ k → pt-⌈𝕀⌉ k) a0 = a1
  :=
    covariant-uniqueness-II
      ( ⌈𝕀⌉)
      ( pt-⌈𝕀⌉ 0₂) ( pt-⌈𝕀⌉ 1₂)
      ( \ (t : 𝕀) → pt-⌈𝕀⌉ t)
      ( equiv-ext-shape-family-fwd 𝕀 □¹ (\ t → A t))
      ( cov)
      ( a0)
      ( a1 , h)

#def amazing-covariant-transport-line-II uses (funext weakfunext)
  ( A : 𝕀 → U)
  ( is-a-cov-A : (i : 𝕀) → is-a-cov (A i))
  ( l : 𝕀 → ⌈𝕀⌉)
  : equiv-ext-shape-family-fwd 𝕀 □¹ A (l 0₂) → equiv-ext-shape-family-fwd 𝕀 □¹ A (l 1₂)
  :=
    covariant-transport-line-II
      ( \ (t : 𝕀 | TOP) → A t)
      ( b-extract
          ( ( g' : 𝕀 → Σ (X : U) , is-a-cov X)
              → is-covariant-arrow-II (\ b → first (g' b)))
          ( is-a-cov-transpose
              ( Σ ( X : U) , is-a-cov X)
              ( \ (X , _) → X)
              ( \ (_ , cX) → cX))
          ( \ k → (A k , is-a-cov-A k)))
      ( l)

#def amazing-covariant-transport-line-const-II uses (funext weakfunext)
  ( A : 𝕀 → U)
  ( is-a-cov-A : (i : 𝕀) → is-a-cov (A i))
  ( j : 𝕀)
  ( x : A j)
  : amazing-covariant-transport-line-II A is-a-cov-A
      (\ k → pt-⌈𝕀⌉ j) x = x
  :=
    covariant-transport-line-const-II
      ( \ (t : 𝕀 | TOP) → A t)
      ( b-extract
          ( ( g' : 𝕀 → Σ (X : U) , is-a-cov X)
              → is-covariant-arrow-II (\ b → first (g' b)))
          ( is-a-cov-transpose
              ( Σ ( X : U) , is-a-cov X)
              ( \ (X , _) → X)
              ( \ (_ , cX) → cX))
          ( \ k → (A k , is-a-cov-A k)))
      ( pt-⌈𝕀⌉ j)
      ( x)

#def amazing-covariant-transport-line-const-at-0-II uses (funext weakfunext)
  ( A : 𝕀 → U)
  ( is-a-cov-A : (i : 𝕀) → is-a-cov (A i))
  ( x : A 0₂)
  : amazing-covariant-transport-line-II A is-a-cov-A
      (\ k → pt-⌈𝕀⌉ (inf 0₂ k)) x = x
  :=
    covariant-transport-line-const-at-0-II
      ( \ (t : 𝕀 | TOP) → A t)
      ( b-extract
          ( ( g' : 𝕀 → Σ (X : U) , is-a-cov X)
              → is-covariant-arrow-II (\ b → first (g' b)))
          ( is-a-cov-transpose
              ( Σ ( X : U) , is-a-cov X)
              ( \ (X , _) → X)
              ( \ (_ , cX) → cX))
          ( \ k → (A k , is-a-cov-A k)))
      ( x)

#def amazing-covariant-transport-line-const-0-sup-II uses (funext weakfunext)
  ( A : 𝕀 → U)
  ( is-a-cov-A : (i : 𝕀) → is-a-cov (A i))
  ( j : 𝕀)
  ( x : A 0₂)
  : amazing-covariant-transport-line-II A is-a-cov-A
      (\ k → pt-⌈𝕀⌉ (inf 0₂ (sup j k))) x = x
  :=
    covariant-transport-line-const-0-sup-II
      ( \ (t : 𝕀 | TOP) → A t)
      ( b-extract
          ( ( g' : 𝕀 → Σ (X : U) , is-a-cov X)
              → is-covariant-arrow-II (\ b → first (g' b)))
          ( is-a-cov-transpose
              ( Σ ( X : U) , is-a-cov X)
              ( \ (X , _) → X)
              ( \ (_ , cX) → cX))
          ( \ k → (A k , is-a-cov-A k)))
      ( j)
      ( x)

#def amazing-covariant-transport-line-const-1-sup-II uses (funext weakfunext)
  ( A : 𝕀 → U)
  ( is-a-cov-A : (i : 𝕀) → is-a-cov (A i))
  ( i : 𝕀)
  ( x : A i)
  : amazing-covariant-transport-line-II A is-a-cov-A
      (\ k → pt-⌈𝕀⌉ (inf i (sup 1₂ k))) x = x
  := amazing-covariant-transport-line-const-II A is-a-cov-A i x

#def amazing-covariant-transport-line-const-0-sup-1-II uses (funext weakfunext)
  ( A : 𝕀 → U)
  ( is-a-cov-A : (i : 𝕀) → is-a-cov (A i))
  ( x : A 0₂)
  : amazing-covariant-transport-line-const-0-sup-II A is-a-cov-A 1₂ x
    = amazing-covariant-transport-line-const-1-sup-II A is-a-cov-A 0₂ x
  := refl

#def amazing-covariant-transport-line-inv-II uses (funext weakfunext)
  ( packed : ᵒᵖ (𝕀 → Σ (X : U) , is-a-cov X))
  ( l : 𝕀 → ⌈𝕀⌉)
  : ( let mod ᵒᵖ p := packed in
      let mod ᵒᵖ lam0 := op-shape-line-flip l in
        ᵒᵖ (equiv-ext-shape-family-fwd 𝕀 □¹ (\ i → first (p i)) (lam0 0₂))
          → ᵒᵖ (equiv-ext-shape-family-fwd 𝕀 □¹ (\ i → first (p i)) (lam0 1₂)))
  :=
    let packed-A : ᵒᵖ (𝕀 → U)
      :=
        let mod ᵒᵖ p := packed in
          mod ᵒᵖ (\ i → first (p i))
    in
    let cov-A
      : let mod ᵒᵖ A := packed-A in
          ᵒᵖ (is-covariant-arrow-II (\ (t : 𝕀 | TOP) → A t))
      :=
        let mod ᵒᵖ p := packed in
          mod ᵒᵖ (
            b-extract
              ( ( g' : 𝕀 → Σ (X : U) , is-a-cov X)
                  → is-covariant-arrow-II (\ b → first (g' b)))
              ( is-a-cov-transpose
                  ( Σ ( X : U) , is-a-cov X)
                  ( \ (X , _) → X)
                  ( \ (_ , cX) → cX))
              ( p))
    in
    let packed-A-shape : ᵒᵖ (⌈𝕀⌉ → U)
      :=
        let mod ᵒᵖ A := packed-A in
          mod ᵒᵖ (equiv-ext-shape-family-fwd 𝕀 □¹ A)
    in
      covariant-transport-line-inv-II packed-A-shape cov-A l
```

## Amazing covariance closure properties

```rzk


#def is-a-cov-const-cov uses (funext weakfunext) (A : U) (is-a-cov-A : is-a-cov A)
  : is-covariant-arrow-II (\ (_ : 𝕀 | TOP) → A)
  :=
    b-extract
      ( ( g : 𝕀 → Σ (A' : U) , is-a-cov A')
        → is-covariant-arrow-II (\ b → first (g b)))
      ( is-a-cov-transpose
          ( Σ ( A' : U) , is-a-cov A')
          ( \ (A' , _) → A')
          ( \ (_ , cA') → cA'))
      ( \ _ → (A , is-a-cov-A))

#def is-discrete-is-a-cov uses (funext weakfunext)
  ( A : U)
  ( is-a-cov-A : is-a-cov A)
  : is-discrete-II A
  :=
    is-discrete-is-covariant-II
      ( ⌈𝕀⌉)
      ( equiv-ext-shape-family-fwd 𝕀 □¹ (\ _ → A))
      ( is-a-cov-const-cov A is-a-cov-A)
      ( pt-⌈𝕀⌉ 0₂)
```

GWB, Lemma 5.14

```rzk

-- GWB, Lemma 5.17
#def is-a-cov-sigma-closed uses (funext weakfunext)
  ( A : U) (B : A → U)
  ( is-a-cov-A : is-a-cov A)
  ( is-a-cov-B : (a : A) → is-a-cov (B a))
  : is-a-cov (Σ (a : A) , B a)
  :=
    b-extract
      ( ( w
        : Σ ( A' : U)
          , ( Σ ( _ : is-a-cov A')
          , ( Σ ( B' : A' → U)
          , ( ( a : A') → is-a-cov (B' a)))))
        → is-a-cov (Σ (a : first w) , (first (second (second w))) a))
      ( is-a-cov-untranspose
          ( Σ ( A' : U)
          , ( Σ ( _ : is-a-cov A')
          , ( Σ ( B' : A' → U)
          , ( ( a : A') → is-a-cov (B' a)))))
          ( \ (A' , (_ , (B' , _))) → Σ (a : A') , B' a)
          ( \ g →
            is-covariant-arrow-II-Σ
              ( \ c → first (g c))
              ( \ c a → (first (second (second (g c)))) a)
              ( b-extract
                  ( ( g' : 𝕀 → (Σ (A' : U) , (Σ (_ : is-a-cov A') , (Σ (B' : A' → U) , ((a : A') → is-a-cov (B' a))))))
                    → is-covariant-arrow-II (\ b → first (g' b)))
                  ( is-a-cov-transpose
                      ( Σ ( A' : U) , (Σ (_ : is-a-cov A') , (Σ (B' : A' → U) , ((a : A') → is-a-cov (B' a)))))
                      ( \ (A' , _) → A')
                      ( \ (_ , (cA' , _)) → cA'))
                  ( g))
              ( \ s →
                b-extract
                  ( ( G : 𝕀 → (Σ (w : Σ (A' : U) , (Σ (_ : is-a-cov A') , (Σ (B' : A' → U) , ((a : A') → is-a-cov (B' a))))) , first w))
                    → is-covariant-arrow-II (\ b → (first (second (second (first (G b))))) (second (G b))))
                  ( is-a-cov-transpose
                      ( Σ ( w : Σ (A' : U) , (Σ (_ : is-a-cov A') , (Σ (B' : A' → U) , ((a : A') → is-a-cov (B' a))))) , first w)
                      ( \ ((_ , (_ , (B' , _))) , a) → B' a)
                      ( \ ((_ , (_ , (_ , cB'))) , a) → cB' a))
                  ( \ c → (g c , s c)))))
      ( A , (is-a-cov-A , (B , is-a-cov-B)))


-- Lemma 5.14(3)
#def is-a-cov-id-closed uses (funext weakfunext) (A : U) (is-a-cov-A : is-a-cov A) (x y : A)
  : is-a-cov (x = y)
  :=
    b-extract
      ( ( w : Σ (A' : U) , (Σ (_ : is-a-cov A') , (Σ (_ : A') , A')))
        → is-a-cov ((first (second (second w))) = (second (second (second w)))))
      ( is-a-cov-untranspose
          ( Σ ( A' : U) , (Σ (_ : is-a-cov A') , (Σ (_ : A') , A')))
          ( \ (_ , (_ , (x' , y'))) → x' = y')
          ( \ g →
            is-covariant-arrow-II-Id
              ( \ c → first (g c))
              ( b-extract
                  ( ( g' : 𝕀 → (Σ (A' : U) , (Σ (_ : is-a-cov A') , (Σ (_ : A') , A'))))
                    → is-covariant-arrow-II (\ b → first (g' b)))
                  ( is-a-cov-transpose
                      ( Σ ( A' : U) , (Σ (_ : is-a-cov A') , (Σ (_ : A') , A')))
                      ( \ (A' , _) → A')
                      ( \ (_ , (cA' , _)) → cA'))
                  ( g))
              ( \ c → first (second (second (g c))))
              ( \ c → second (second (second (g c))))))
      ( A , (is-a-cov-A , (x , y)))

#def is-a-cov-fib uses (funext weakfunext) (A B : U) (is-a-cov-A : is-a-cov A) (is-a-cov-B : is-a-cov B) (f : A → B) (b : B)
  : is-a-cov (fib A B f b)
  :=
    is-a-cov-sigma-closed
      A
      ( \ a → (f a) = b)
      is-a-cov-A
      ( \ a → is-a-cov-id-closed B is-a-cov-B (f a) b)

#def equiv-realize-shape-at-1-map
  ( f : 𝕀 → ⌈𝕀⌉)
  ( x : ⌈𝕀⌉)
  : Equiv
      ( match x ( point i ⇒ shape-at-1 (f i)))
      ( shape-at-1 (match x ( point i ⇒ f i)))
  := match x
      ( point i ⇒ equiv-identity (shape-at-1 (f i)))

-- Lemma 5.16
#def is-a-cov-i===0 uses (funext weakfunext extext) (i : 𝕀)
  : is-a-cov (Shape 1 (\ _ → i ≡ 1₂))
  :=
    b-extract
      ( ( i' : 𝕀) → is-a-cov (Shape 1 (\ _ → i' ≡ 1₂)))
      ( first
          ( b-equiv
              ( ( t : ⌈𝕀⌉) → is-a-cov (shape-at-1 t))
              ( ( i' : 𝕀) → is-a-cov (Shape 1 (\ _ → i' ≡ 1₂)))
              ( inv-equiv
                  ( ( i' : 𝕀) → is-a-cov (Shape 1 (\ _ → i' ≡ 1₂)))
                  ( ( t : ⌈𝕀⌉) → is-a-cov (shape-at-1 t))
                  ( equiv-ext-shape-fun
                      funext
                      𝕀
                      ( \ _ → TOP)
                      ( \ t → is-a-cov (shape-at-1 t)))))
          ( is-a-cov-untranspose
              ( ⌈𝕀⌉)
              ( shape-at-1)
              ( \ (f0 : 𝕀 → ⌈𝕀⌉) →
                equiv-is-covariant-II
                  ( funext)
                  ( ⌈𝕀⌉)
                  ( equiv-ext-shape-family-fwd 𝕀 □¹ (\ i' → shape-at-1 (f0 i')))
                  ( \ s → shape-at-1
                      (match s ( point i' ⇒ f0 i')))
                  ( \ s → equiv-realize-shape-at-1-map f0 s)
                  ( \ (x : ⌈𝕀⌉) (y : ⌈𝕀⌉)
                    (arr : hom-II ⌈𝕀⌉ x y)
                    (a0 : shape-at-1
                            (match x ( point i' ⇒ f0 i'))) →
                    let larr : 𝕀 → ⌈𝕀⌉ := \ j → arr j in
                    let f : 𝕀 → ⌈𝕀⌉
                      := \ j → match (larr j) ( point i' ⇒ f0 i')
                    in
                    let e0
                      : (f 0₂) = pt-⌈𝕀⌉ (1₂)
                      := eq-form-1-of-shape-at-1 (f 0₂) a0
                    in
                    let e1
                      : (f 1₂) = pt-⌈𝕀⌉ (1₂)
                      := fun-monotonicity f e0
                    in
                    let a1
                      : shape-at-1 (f 1₂)
                      := shape-at-1-of-eq-form-1 (f 1₂) e1
                    in
                    let h
                      : dhom-II ⌈𝕀⌉
                          (pt-⌈𝕀⌉ 0₂) (pt-⌈𝕀⌉ 1₂)
                          (\ t → pt-⌈𝕀⌉ t)
                          (\ s → match s ( point j ⇒ shape-at-1 (f j)))
                          a0 a1
                      := dhom-II-form-line-shape-at-1 f a0 a1 e0
                    in
                      is-contr-is-inhabited-is-prop
                        ( Σ ( a1' : shape-at-1 (f 1₂))
                        , dhom-II ⌈𝕀⌉
                            (pt-⌈𝕀⌉ 0₂) (pt-⌈𝕀⌉ 1₂)
                            (\ t → pt-⌈𝕀⌉ t)
                            (\ s → match s ( point j ⇒ shape-at-1 (f j)))
                            a0 a1')
                        ( is-prop-Σ-dhom-II-form-line-shape-at-1 extext f a0)
                        ( a1 , h)))))
      ( i)
```
## Amazing covariance of function types

We first work with a proposition in the opposite modality. The parameter
package contains only types and terms; it does not quantify over topes.

```rzk
#def is-a-cov-equiv uses (funext weakfunext)
  ( A B : U)
  ( e : Equiv A B)
  ( cov-B : is-a-cov B)
  : is-a-cov A
  := transport U is-a-cov B A
      (rev U A B (first (ua A B) e)) cov-B

#def is-covariant-arrow-is-a-cov uses (funext weakfunext)
  ( A : 𝕀 → U)
  ( cov-A : (i : 𝕀) → is-a-cov (A i))
  : is-covariant-arrow-II A
  := b-extract
      ((g : 𝕀 → Σ (X : U) , is-a-cov X)
        → is-covariant-arrow-II (\ i → first (g i)))
      (is-a-cov-transpose
        (Σ (X : U) , is-a-cov X)
        (\ (X , _) → X) (\ (_ , c) → c))
      (\ i → (A i , cov-A i))

#def op-realize-type-family
  ( P : 𝕀 → ᵒᵖ U)
  : ᵒᵖ (⌈𝕀⌉ → U)
  := let mod ᵒᵖ P0 := op-ext-commute-bwd (\ _ → U) P in
      mod ᵒᵖ (equiv-ext-shape-family-fwd 𝕀 □¹ P0)

#def is-covariant-op-realize-is-a-cov uses (funext weakfunext)
  ( P : 𝕀 → ᵒᵖ U)
  ( cov-P : (i : 𝕀) → let mod ᵒᵖ P0 := P i in ᵒᵖ (is-a-cov P0))
  : let mod ᵒᵖ C := op-realize-type-family P in
      ᵒᵖ (is-covariant-II ⌈𝕀⌉ C)
  := let mod ᵒᵖ g :=
      op-ext-commute-bwd (\ _ → Σ (X : U) , is-a-cov X)
        (\ i → let mod ᵒᵖ X := P i in
          let mod ᵒᵖ c := cov-P i in mod ᵒᵖ (X , c)) in
      mod ᵒᵖ (is-covariant-arrow-is-a-cov
        (\ i → first (g i)) (\ i → second (g i)))

#def is-covariant-op-prop-function uses (funext weakfunext extext)
  ( P : 𝕀 → ᵒᵖ U)
  ( prop-P : (i : 𝕀) → is-prop (let mod ᵒᵖ X := P i in ᵒᵖ X))
  ( cov-P : (i : 𝕀) → let mod ᵒᵖ X := P i in ᵒᵖ (is-a-cov X))
  ( A : 𝕀 → U)
  ( cov-A : (i : 𝕀) → is-a-cov (A i))
  : is-covariant-arrow-II (\ i → (let mod ᵒᵖ X := P i in ᵒᵖ X) → A i)
  := is-covariant-op-function funext extext
      (op-realize-type-family P)
      (is-covariant-op-realize-is-a-cov P cov-P)
      (\ s → match s (point i ⇒ prop-P i))
      A (is-covariant-arrow-is-a-cov A cov-A)
      (\ i → is-discrete-is-a-cov (A i) (cov-A i))

#def op-prop-function-data uses (funext weakfunext)
  : U
  := Σ (P : ᵒᵖ U)
    , Σ (_ : is-prop (let mod ᵒᵖ X := P in ᵒᵖ X))
    , Σ (_ : let mod ᵒᵖ X := P in ᵒᵖ (is-a-cov X))
    , Σ (A : U) , is-a-cov A

#def op-prop-function-family uses (funext weakfunext)
  ( w : op-prop-function-data)
  : U
  := (let mod ᵒᵖ X := first w in ᵒᵖ X)
    → first (second (second (second w)))

#def is-a-cov-op-prop-function uses (funext weakfunext extext)
  ( P : ᵒᵖ U)
  ( prop-P : is-prop (let mod ᵒᵖ X := P in ᵒᵖ X))
  ( cov-P : let mod ᵒᵖ X := P in ᵒᵖ (is-a-cov X))
  ( A : U)
  ( cov-A : is-a-cov A)
  : is-a-cov ((let mod ᵒᵖ X := P in ᵒᵖ X) → A)
  := b-extract
      ((w : op-prop-function-data) → is-a-cov (op-prop-function-family w))
      (is-a-cov-untranspose op-prop-function-data op-prop-function-family
        (\ g → is-covariant-op-prop-function
          (\ i → first (g i))
          (\ i → first (second (g i)))
          (\ i → first (second (second (g i))))
          (\ i → first (second (second (second (g i)))))
          (\ i → second (second (second (second (g i)))))))
      (P , (prop-P , (cov-P , (A , cov-A))))
```

## Extensions over a tope

Lemma 5.18 follows by replacing the extension with functions out of the
opposite shape realisation. The tope remains a schematic parameter.

```rzk
#def is-prop-unit-shape
  ( phi : 1 → TOPE)
  : is-prop (Shape 1 phi)
  := \ x y → match x (point u ⇒
      is-prop-is-contr (Shape 1 phi)
        (point 1 phi u , \ z → match z (point v ⇒ refl))
        (point 1 phi u) y)

#def equiv-ext-op-shape-function uses (funext)
  ( phi : ᵒᵖ TOPE)
  ( A : U)
  : Equiv
      ((t : 1 | uninvᵒᵖ phi) → A)
      ((let mod ᵒᵖ p := phi in ᵒᵖ (Shape 1 (\ _ → p))) → A)
  := equiv-comp
      ((t : 1 | uninvᵒᵖ phi) → A)
      (Shape 1 (\ _ → uninvᵒᵖ phi) → A)
      ((let mod ᵒᵖ p := phi in ᵒᵖ (Shape 1 (\ _ → p))) → A)
      (equiv-ext-shape-fun funext 1 (\ _ → uninvᵒᵖ phi) (\ _ → A))
      ((\ h c → h (first (equiv-shape-1-op-uninv phi) c))
      , is-equiv-precomp-is-equiv funext
          (let mod ᵒᵖ p := phi in ᵒᵖ (Shape 1 (\ _ → p)))
          (Shape 1 (\ _ → uninvᵒᵖ phi)) A
          (first (equiv-shape-1-op-uninv phi))
          (second (equiv-shape-1-op-uninv phi)))

#def is-a-cov-ext uses (funext weakfunext extext)
  ( phi : ᵒᵖ TOPE)
  ( shape-is-a-cov : let mod ᵒᵖ p := phi in
      ᵒᵖ (is-a-cov (Shape 1 (\ _ → p))))
  ( A : U)
  ( is-a-cov-A : is-a-cov A)
  : is-a-cov ((t : 1 | uninvᵒᵖ phi) → A)
  := is-a-cov-equiv
      ((t : 1 | uninvᵒᵖ phi) → A)
      ((let mod ᵒᵖ p := phi in ᵒᵖ (Shape 1 (\ _ → p))) → A)
      (equiv-ext-op-shape-function phi A)
      (is-a-cov-op-prop-function
        (let mod ᵒᵖ p := phi in mod ᵒᵖ (Shape 1 (\ _ → p)))
        (is-prop-Equiv-is-prop
          (let mod ᵒᵖ p := phi in ᵒᵖ (Shape 1 (\ _ → p)))
          (Shape 1 (\ _ → uninvᵒᵖ phi))
          (equiv-shape-1-op-uninv phi)
          (is-prop-unit-shape (\ _ → uninvᵒᵖ phi)))
        shape-is-a-cov A is-a-cov-A)
```
