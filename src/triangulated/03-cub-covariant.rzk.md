# 3. Cubical (ordinary) covariance

```rzk
#lang rzk-1

#assume funext : FunExt
#assume weakfunext : WeakFunExt
#assume extext : ExtExt
```

## Pullback along the cubical base point

```rzk
#def orthogonality-pullback-fiber uses (funext weakfunext)
  ( n m : nat)
  ( F0 : product (I^n n) ⌈𝕀⌉ → U)
  : U
  :=
    Σ ( c : I^n m → product (I^n n) ⌈𝕀⌉)
    , F0 (c (zero-vec-I^n m))

#def orthogonality-pullback-fwd uses (funext weakfunext)
  ( n m : nat)
  ( F0 : product (I^n n) ⌈𝕀⌉ → U)
  : ( I^n m
      → Σ ( t : product (I^n n) ⌈𝕀⌉)
        , F0 t)
    → orthogonality-pullback-fiber n m F0
  :=
    \ f →
      ( \ t → first (f t)
      , second (f (zero-vec-I^n m)))

#def orthogonality-pullback uses (funext weakfunext)
  ( n m : nat)
  ( F0 : product (I^n n) ⌈𝕀⌉ → U)
  : Equiv
      ( I^n m
        → Σ ( t : product (I^n n) ⌈𝕀⌉)
          , F0 t)
      ( orthogonality-pullback-fiber n m F0)
  :=
    ( orthogonality-pullback-fwd n m F0
    , ?orthogonality-pullback)

#def orthogonality-pullback-split uses (funext weakfunext)
  ( n m : nat)
  ( F0 : product (I^n n) ⌈𝕀⌉ → U)
  : U
  :=
    Σ ( v : I^n m → I^n n)
    , Σ ( theta : I^n m → ⌈𝕀⌉)
    , F0
        ( v (zero-vec-I^n m)
        , theta (zero-vec-I^n m))

#def equiv-orthogonality-pullback-split uses (funext weakfunext)
  ( n m : nat)
  ( F0 : product (I^n n) ⌈𝕀⌉ → U)
  : Equiv (orthogonality-pullback-fiber n m F0) (orthogonality-pullback-split n m F0)
  :=
    equiv-has-inverse
      ( orthogonality-pullback-fiber n m F0)
      ( orthogonality-pullback-split n m F0)
      ( \ (c , p) →
          ( \ t → first (c t)
          , ( \ t → second (c t)
            , p)))
      ( \ (v , (theta , p)) →
          ( \ t → (v t , theta t)
          , p))
      ( \ _ → refl)
      ( \ _ → refl)

#def orthogonality-pullback-flat-commute uses (funext weakfunext)
  ( n m :♭ nat)
  ( F0 :♭ product (I^n n) ⌈𝕀⌉ → U)
  : Equiv
      ( ♭ ( orthogonality-pullback-split n m F0))
      ( Σ ( v : ♭ (I^n m → I^n n))
      , ( let mod ♭ v' := v in
          Σ ( theta : ♭ (I^n m → ⌈𝕀⌉))
          , ( let mod ♭ theta' := theta in
              ♭
                ( F0
                    ( v' (zero-vec-I^n m)
                    , theta' (zero-vec-I^n m))))))
  :=
    b-sigma2-commute-equiv
      ( I^n m → I^n n)
      ( I^n m → ⌈𝕀⌉)
      ( \ v theta →
          F0
            ( v (zero-vec-I^n m)
            , theta (zero-vec-I^n m)))

#def equiv-orthogonality-to-flat uses (funext weakfunext)
  ( n m :♭ nat)
  ( F0 :♭ product (I^n n) ⌈𝕀⌉ → U)
  : Equiv
      ( ♭
          ( I^n m
            → Σ ( t : product (I^n n) ⌈𝕀⌉)
              , F0 t))
      ( ♭ ( orthogonality-pullback-split n m F0))
  :=
    let mod ♭ F-uncurried :=
      mod ♭ (orthogonality-pullback-fiber n m F0) in
    let mod ♭ curry-F :=
      mod ♭ (equiv-orthogonality-pullback-split n m F0) in
    b-equiv
      ( I^n m
        → Σ ( t : product (I^n n) ⌈𝕀⌉)
          , F0 t)
      ( orthogonality-pullback-split n m F0)
      ( equiv-comp
          ( I^n m
            → Σ ( t : product (I^n n) ⌈𝕀⌉)
              , F0 t)
          ( F-uncurried)
          ( orthogonality-pullback-split n m F0)
          ( orthogonality-pullback n m F0)
          ( curry-F))
```

## Ordinary covariance over 𝕀

```rzk title="RS17 Def 8.2, cubical"
#def is-covariant-II
  ( A : U)
  ( C : A → U)
  : U
  :=
    ( x : A) → (y : A) → (f : hom-II A x y) → (u : C x)
  → is-contr (dhom-from-II A x y f C u)
```

```rzk
#def is-discrete-is-covariant-II
  ( A : U)
  ( C : A → U)
  ( is-cov-C : is-covariant-II A C)
  ( x : A)
  : is-discrete-II (C x)
  :=
    ( \ u v →
    is-equiv-fiberwise-is-equiv-total
      ( C x)
      ( \ v' → (u = v'))
      ( hom-II (C x) u)
      ( hom-eq-II (C x) u)
      ( is-equiv-are-contr
        ( Σ ( y : (C x)) , u = y)
        ( Σ ( y : (C x)) , hom-II (C x) u y)
        ( is-contr-based-paths (C x) u)
        ( is-cov-C x x (id-hom-II A x) u)
        ( total-map
          ( C x)
          ( \ v' → u = v')
          ( hom-II (C x) u)
          ( hom-eq-II (C x) u)))
      ( v))
```

```rzk
#def covariant-transport-II
  ( A : U)
  ( x y : A)
  ( f : hom-II A x y)
  ( C : A → U)
  ( cov : is-covariant-II A C)
  ( u : C x)
  : C y
  := first (center-contraction (dhom-from-II A x y f C u) (cov x y f u))

#def covariant-lift-II
  ( A : U)
  ( x y : A)
  ( f : hom-II A x y)
  ( C : A → U)
  ( cov : is-covariant-II A C)
  ( u : C x)
  : dhom-II A x y f C u (covariant-transport-II A x y f C cov u)
  := second (center-contraction (dhom-from-II A x y f C u) (cov x y f u))

#def covariant-uniqueness-II
  ( A : U)
  ( x y : A)
  ( f : hom-II A x y)
  ( C : A → U)
  ( cov : is-covariant-II A C)
  ( u : C x)
  ( lift : dhom-from-II A x y f C u)
  : covariant-transport-II A x y f C cov u = first lift
  :=
    first-path-Σ
      ( C y)
      ( \ v → dhom-II A x y f C u v)
      ( center-contraction (dhom-from-II A x y f C u) (cov x y f u))
      ( lift)
      ( homotopy-contraction (dhom-from-II A x y f C u) (cov x y f u) lift)

#def id-arr-covariant-transport-II
  ( A : U)
  ( x : A)
  ( C : A → U)
  ( cov : is-covariant-II A C)
  ( u : C x)
  : covariant-transport-II A x x (\ _ → x) C cov u = u
  := covariant-uniqueness-II A x x (\ _ → x) C cov u (u , \ _ → u)

#def is-covariant-II-substitution
  ( A B : U)
  ( C : A → U)
  ( cov : is-covariant-II A C)
  ( g : B → A)
  : is-covariant-II B (\ b → C (g b))
  := \ x y f u → cov (g x) (g y) (\ t → g (f t)) u
```

## Covariance is a proposition

```rzk
#def is-prop-is-covariant-II uses (weakfunext funext)
  ( A : U)
  ( C : A → U)
  : is-prop (is-covariant-II A C)
  :=
    is-prop-fiberwise-prop4 funext A
      ( \ _ → A)
      ( \ x y → hom-II A x y)
      ( \ x _ _ → C x)
      ( \ x y f u → is-contr (dhom-from-II A x y f C u))
      ( \ x y f u → is-prop-is-contr-itself weakfunext (dhom-from-II A x y f C u))

#def is-covariant-II-Prop uses (weakfunext funext)
  ( A : U)
  ( C : A → U)
  : Prop
  := (is-covariant-II A C , is-prop-is-covariant-II A C)
```

## Transport along a line in the interval

```rzk
#def is-covariant-arrow-II
  ( C : (t : 𝕀 | TOP) → U)
  : U
  := is-covariant-II ⌈𝕀⌉ (equiv-ext-shape-family-fwd 𝕀 □¹ (\ t → C t))

#def covariant-transport-line-II
  ( C : (t : 𝕀 | TOP) → U)
  ( cov : is-covariant-arrow-II C)
  ( l : 𝕀 → ⌈𝕀⌉)
  : equiv-ext-shape-family-fwd 𝕀 □¹ (\ t → C t) (l 0₂)
    → equiv-ext-shape-family-fwd 𝕀 □¹ (\ t → C t) (l 1₂)
  :=
    \ u →
      covariant-transport-II
        ⌈𝕀⌉ (l 0₂) (l 1₂) (\ t → l t)
        ( equiv-ext-shape-family-fwd 𝕀 □¹ (\ t → C t))
        cov u

#def covariant-transport-line-const-II
  ( C : (t : 𝕀 | TOP) → U)
  ( cov : is-covariant-arrow-II C)
  ( j : ⌈𝕀⌉)
  ( u : equiv-ext-shape-family-fwd 𝕀 □¹ (\ t → C t) j)
  : covariant-transport-line-II C cov (\ _ → j) u = u
  := id-arr-covariant-transport-II
      ⌈𝕀⌉ j (equiv-ext-shape-family-fwd 𝕀 □¹ (\ t → C t)) cov u

#def covariant-transport-line-const-at-0-II
  ( C : (t : 𝕀 | TOP) → U)
  ( cov : is-covariant-arrow-II C)
  ( u : C 0₂)
  : covariant-transport-line-II C cov (\ k → pt-⌈𝕀⌉ (inf 0₂ k)) u = u
  := id-arr-covariant-transport-II
      ⌈𝕀⌉ (pt-⌈𝕀⌉ 0₂) (equiv-ext-shape-family-fwd 𝕀 □¹ (\ t → C t)) cov u

#def covariant-transport-line-const-0-sup-II
  ( C : (t : 𝕀 | TOP) → U)
  ( cov : is-covariant-arrow-II C)
  ( j : 𝕀)
  ( u : C 0₂)
  : covariant-transport-line-II C cov
      ( \ k → pt-⌈𝕀⌉ (inf 0₂ (sup j k))) u = u
  := id-arr-covariant-transport-II
      ⌈𝕀⌉ (pt-⌈𝕀⌉ 0₂) (equiv-ext-shape-family-fwd 𝕀 □¹ (\ t → C t)) cov u

#def covariant-transport-line-const-1-sup-II
  ( C : (t : 𝕀 | TOP) → U)
  ( cov : is-covariant-arrow-II C)
  ( i : 𝕀)
  ( u : C i)
  : covariant-transport-line-II C cov
      ( \ k → pt-⌈𝕀⌉ (inf i (sup 1₂ k))) u = u
  := id-arr-covariant-transport-II
      ⌈𝕀⌉ (pt-⌈𝕀⌉ i) (equiv-ext-shape-family-fwd 𝕀 □¹ (\ t → C t)) cov u
```

## The extension theorem

```rzk
#def op-shape-line-flip
  ( l : 𝕀 → ⌈𝕀⌉)
  : ᵒᵖ (𝕀 → ⌈𝕀⌉)
  :=
    op-ext-commute-bwd (\ (_ : 𝕀) → ⌈𝕀⌉)
      ( \ i →
          match (l i)
            ( point j ⇒
                let mod ᵒᵖ j0 : 𝕀 := flipᵒᵖ j in
                  mod ᵒᵖ (pt-⌈𝕀⌉ j0)))

#def op-shape-point-flip
  ( s : ⌈𝕀⌉)
  : ᵒᵖ ⌈𝕀⌉
  :=
    match s
      ( point i ⇒
          let mod ᵒᵖ j : 𝕀 := flipᵒᵖ i in
            mod ᵒᵖ (pt-⌈𝕀⌉ j))

#def op-family-at
  ( C : ᵒᵖ (⌈𝕀⌉ → U))
  ( s : ᵒᵖ ⌈𝕀⌉)
  : U
  :=
    let mod ᵒᵖ C0 := C in
    let mod ᵒᵖ s0 := s in
      ᵒᵖ (C0 s0)

#def covariant-transport-line-inv-II
  ( packed : ᵒᵖ (⌈𝕀⌉ → U))
  ( cov
    : let mod ᵒᵖ C0 := packed in
        ᵒᵖ (is-covariant-II ⌈𝕀⌉ C0))
  ( l : 𝕀 → ⌈𝕀⌉)
  : ( let mod ᵒᵖ C0 := packed in
      let mod ᵒᵖ lam0 := op-shape-line-flip l in
        ᵒᵖ (C0 (lam0 0₂)) → ᵒᵖ (C0 (lam0 1₂)))
  :=
    \ x →
      let mod ᵒᵖ C0 := packed in
      let mod ᵒᵖ cov0 := cov in
      let mod ᵒᵖ lam0 := op-shape-line-flip l in
      let mod ᵒᵖ x0 := x in
        mod ᵒᵖ (
          covariant-transport-II
            ⌈𝕀⌉ (lam0 0₂) (lam0 1₂) (\ t → lam0 t)
            C0 cov0 x0)
#def equiv-is-cov-i-coslice
  ( A : 𝕀 → U)
  ( a0 : A 0₂)
  : Equiv
      ( Σ ( a1 : A 1₂) , dhom-II ⌈𝕀⌉
          ( pt-⌈𝕀⌉ 0₂) (pt-⌈𝕀⌉ 1₂) (\ t → pt-⌈𝕀⌉ t)
          ( equiv-ext-shape-family-fwd 𝕀 □¹ A) a0 a1)
      ( Σ ( φ : (i : 𝕀) → A i) , φ 0₂ = a0)
  :=
    equiv-has-inverse
      ( Σ ( a1 : A 1₂) , dhom-II ⌈𝕀⌉
          ( pt-⌈𝕀⌉ 0₂) (pt-⌈𝕀⌉ 1₂) (\ t → pt-⌈𝕀⌉ t)
          ( equiv-ext-shape-family-fwd 𝕀 □¹ A) a0 a1)
      ( Σ ( φ : (i : 𝕀) → A i) , φ 0₂ = a0)
      ( \ (a1 , h) → (\ t → h t , refl))
      ( \ (φ , p) →
          ( φ 1₂
          , ind-path (A 0₂) (φ 0₂)
              ( \ a0' _ → dhom-II ⌈𝕀⌉
                  ( pt-⌈𝕀⌉ 0₂) (pt-⌈𝕀⌉ 1₂) (\ t → pt-⌈𝕀⌉ t)
                  ( equiv-ext-shape-family-fwd 𝕀 □¹ A) a0' (φ 1₂))
              ( \ t → φ t)
              a0 p))
      ( \ (a1 , h) → refl)
      ( \ (φ , p) →
          ind-path (A 0₂) (φ 0₂)
            ( \ a0' p' →
                ( \ t →
                    ind-path (A 0₂) (φ 0₂)
                      ( \ a0'' _ → dhom-II ⌈𝕀⌉
                          ( pt-⌈𝕀⌉ 0₂) (pt-⌈𝕀⌉ 1₂) (\ t → pt-⌈𝕀⌉ t)
                          ( equiv-ext-shape-family-fwd 𝕀 □¹ A) a0'' (φ 1₂))
                      ( \ t' → φ t')
                      a0' p' t
                , refl)
                =_{Σ (ψ : (i : 𝕀) → A i) , ψ 0₂ = a0'}
  ( φ , p'))
            ( refl)
            a0 p)



#def is-covariant-arrow-II-coslice
  ( A : 𝕀 → U)
  ( cov : is-covariant-arrow-II A)
  ( a0 : A 0₂)
  : is-contr (Σ (φ : (i : 𝕀) → A i) , φ 0₂ = a0)
  :=
    is-contr-equiv-is-contr
      ( Σ ( a1 : A 1₂) , dhom-II ⌈𝕀⌉
          ( pt-⌈𝕀⌉ 0₂) (pt-⌈𝕀⌉ 1₂) (\ t → pt-⌈𝕀⌉ t)
          ( equiv-ext-shape-family-fwd 𝕀 □¹ A) a0 a1)
      ( Σ ( φ : (i : 𝕀) → A i) , φ 0₂ = a0)
      ( equiv-is-cov-i-coslice A a0)
      ( cov (pt-⌈𝕀⌉ 0₂) (pt-⌈𝕀⌉ 1₂) (\ t → pt-⌈𝕀⌉ t) a0)

```

## Closure properties

```rzk
#def equiv-is-covariant-II uses (funext)
  ( A : U)
  ( B C : A → U)
  ( equiv-BC : (a : A) → Equiv (B a) (C a))
  ( is-covariant-C : is-covariant-II A C)
  : is-covariant-II A B
  :=
    let family-eq
      : B = C
      :=
        eq-htpy funext A (\ _ → U) B C
          ( \ a → first (ua (B a) (C a)) (equiv-BC a))
    in
      transport
        ( A → U)
        ( is-covariant-II A)
        ( C) (B)
        ( rev (A → U) B C family-eq)
        ( is-covariant-C)

#def is-covariant-II-Σ
  ( A : U)
  ( C : A → U)
  ( D : (Σ (a : A) , C a) → U)
  ( cov-C : is-covariant-II A C)
  ( cov-D : is-covariant-II (Σ (a : A) , C a) D)
  : is-covariant-II A (\ a → Σ (c : C a) , D (a , c))
  := ?is-covariant-II-Σ

#def is-covariant-II-Id
  ( A : U)
  ( C : A → U)
  ( cov-C : is-covariant-II A C)
  ( u v : (a : A) → C a)
  : is-covariant-II A (\ a → u a = v a)
  := ?is-covariant-II-Id

#def is-covariant-arrow-II-Σ
  ( A : 𝕀 → U)
  ( B : (i : 𝕀) → A i → U)
  ( cov-a : is-covariant-arrow-II A)
  ( is-cov-B : (s : (t : 𝕀) → A t) → is-covariant-arrow-II (\ t → B t (s t)))
  : is-covariant-arrow-II (\ i → Σ (a : A i) , B i a)
  := ?is-covariant-II-Σ

#def is-covariant-arrow-II-Id
  ( A : 𝕀 → U)
  ( is-cov-A : is-covariant-arrow-II A)
  ( u v : (i : 𝕀) → A i)
  : is-covariant-arrow-II (\ t → u t = v t)
  := ?is-covariant-II-Id


-- Transport on a constant opposite line is the identity.
-- This is the function-space argument used by the extension theorem.
#def covariant-transport-line-inv-const-II
  ( C : ᵒᵖ (⌈𝕀⌉ → U))
  ( cov : let mod ᵒᵖ C0 := C in ᵒᵖ (is-covariant-II ⌈𝕀⌉ C0))
  ( i : 𝕀)
  ( c : op-family-at C (op-shape-point-flip (pt-⌈𝕀⌉ i)))
  : covariant-transport-line-inv-II C cov (\ _ → pt-⌈𝕀⌉ i) c = c
  := let mod ᵒᵖ C0 := C in
      let mod ᵒᵖ cov0 := cov in
      let mod ᵒᵖ j := flipᵒᵖ i in
      let mod ᵒᵖ c0 := c in
        op-path-commute-fwd (C0 (pt-⌈𝕀⌉ j))
          ( covariant-transport-II ⌈𝕀⌉ (pt-⌈𝕀⌉ j) (pt-⌈𝕀⌉ j)
            ( \ _ → pt-⌈𝕀⌉ j) C0 cov0 c0)
          c0
          ( mod ᵒᵖ (id-arr-covariant-transport-II
            ⌈𝕀⌉ (pt-⌈𝕀⌉ j) C0 cov0 c0))

-- Functions from an opposite covariant family into a discrete covariant family.
#def is-covariant-op-function uses (funext extext)
  ( C : ᵒᵖ (⌈𝕀⌉ → U))
  ( is-cov-C : let mod ᵒᵖ C0 := C in ᵒᵖ (is-covariant-II ⌈𝕀⌉ C0))
  ( D : 𝕀 → U)
  ( cov-D : is-covariant-arrow-II D)
  ( disc-D : (i : 𝕀) → is-discrete-II (D i))
  : is-covariant-arrow-II
      ( \ i → op-family-at C (op-shape-point-flip (pt-⌈𝕀⌉ i)) → D i)
  :=
    let function-family : ⌈𝕀⌉ → U
      := equiv-ext-shape-family-fwd 𝕀 □¹
          ( \ i →
              op-family-at C (op-shape-point-flip (pt-⌈𝕀⌉ i)) → D i)
    in
    let transport-line-inv-endpoints
      : ( l : 𝕀 → ⌈𝕀⌉)
        → op-family-at C (op-shape-point-flip (l 1₂))
        → op-family-at C (op-shape-point-flip (l 0₂))
      :=
        \ l x → covariant-transport-line-inv-II C is-cov-C l x
    in
    let transport-line-inv-specified
      : ( l : 𝕀 → ⌈𝕀⌉)
      → ( s1 : ⌈𝕀⌉)
      → ( l 1₂ = s1)
      → ( s0 : ⌈𝕀⌉)
      → ( l 0₂ = s0)
      → op-family-at C (op-shape-point-flip s1)
        → op-family-at C (op-shape-point-flip s0)
      :=
        \ l s1 e1 s0 e0 x →
          let start
            : op-family-at C (op-shape-point-flip (l 1₂))
            :=
              transport
                ( ⌈𝕀⌉)
                ( \ s → op-family-at C (op-shape-point-flip s))
                ( s1) (l 1₂)
                ( rev ⌈𝕀⌉ (l 1₂) s1 e1)
                ( x)
          in
          let finish := transport-line-inv-endpoints l start
          in
            transport
              ( ⌈𝕀⌉)
              ( \ s → op-family-at C (op-shape-point-flip s))
              ( l 0₂) (s0) (e0) (finish)
    in
    \ (x : ⌈𝕀⌉) →
    match x
      into (\ x' →
        ( y : ⌈𝕀⌉)
        → ( f : hom-II ⌈𝕀⌉ x' y)
        → ( u : function-family x')
        → is-contr
            ( dhom-from-II
                ⌈𝕀⌉ x' y f (function-family) u))
      ( point x0 ⇒
        \ (y : ⌈𝕀⌉)
          ( f : hom-II ⌈𝕀⌉ (pt-⌈𝕀⌉ x0) y)
          ( u : op-family-at C (op-shape-point-flip (pt-⌈𝕀⌉ x0)) → D x0)
  → let l : 𝕀 → ⌈𝕀⌉ := \ k → f k in
    let DS : ⌈𝕀⌉ → U := equiv-ext-shape-family-fwd 𝕀 □¹ D
    in
    let eval-op-function
 : ( s : ⌈𝕀⌉)
        → function-family s
        → op-family-at C (op-shape-point-flip s)
        → DS s
      :=
        \ s →
          match s
            into (\ s' →
              function-family s'
              → op-family-at C (op-shape-point-flip s')
              → DS s')
            ( point _ ⇒ \ h c → h c)
    in
    let extend-along
 : ( r s : ⌈𝕀⌉)
        → hom-II ⌈𝕀⌉ r s
        → function-family r
        → function-family s
      :=
        \ r s →
          match s
            into (\ s' →
              hom-II ⌈𝕀⌉ r s'
              → function-family r
              → function-family s')
            ( point a ⇒
                \ line pr ca →
                  let ca0
                    := transport-line-inv-endpoints line ca
                  in
                  let initial := eval-op-function r pr ca0
                  in
                    covariant-transport-II
                      ⌈𝕀⌉ (line 0₂) (line 1₂) (\ t → line t)
                      DS cov-D initial)
    in
    let E : 𝕀 → U
      := \ i → function-family (f i)
    in
      let f0 : E 0₂ := u in
        let phi
 : ( i : 𝕀) → E i
          :=
            \ i →
              extend-along
                ( f 0₂) (f i) (\ k → f (inf i k)) f0
        in
        let phi0-eq-f0 : phi 0₂ = f0
          :=
            eq-htpy funext
              ( op-family-at C (op-shape-point-flip (pt-⌈𝕀⌉ x0)))
              ( \ _ → D x0)
              ( phi 0₂)
              ( f0)
              ( \ c →
                  let c0'
                    := transport-line-inv-specified
                        ( \ k → f (inf 0₂ k))
                        ( pt-⌈𝕀⌉ x0) (refl)
                        ( pt-⌈𝕀⌉ x0) (refl)
                        c
                  in
                    concat (D x0)
                      ( phi 0₂ c)
                      ( f0 c0')
                      ( f0 c)
                      ( id-arr-covariant-transport-II
                          ⌈𝕀⌉ (pt-⌈𝕀⌉ x0) DS cov-D (f0 c0'))
                      ( ap
                          ( op-family-at C
                              ( op-shape-point-flip (pt-⌈𝕀⌉ x0)))
                          ( D x0)
                          ( c0') (c) (f0)
                          ( covariant-transport-line-inv-const-II C is-cov-C x0 c)))
        in
        let contr-center
 : Σ ( φ : (i : 𝕀) → E i) , φ 0₂ = f0
          := (phi , phi0-eq-f0)
        in
        let contr-hom
 : ( y : Σ (φ : (i : 𝕀) → E i) , φ 0₂ = f0)
              → contr-center = y
          :=
            \ (p , q) →
              let H-sec
 : ( j : 𝕀) → (i : 𝕀) → E i
                :=
                  \ j i →
                    extend-along
                      ( f (inf i j)) (f i)
                      ( \ k → f (inf i (sup j k)))
                      ( p (inf i j))
              in
              let d
 : ( j : 𝕀) → H-sec j 0₂ = p 0₂
                :=
                  \ j →
                    eq-htpy funext
                      ( op-family-at C (op-shape-point-flip (pt-⌈𝕀⌉ x0)))
                      ( \ _ → D x0)
                      ( H-sec j 0₂)
                      ( p 0₂)
                      ( \ c →
                          let c-mid
                            := transport-line-inv-specified
                                ( \ k → f (inf 0₂ (sup j k)))
                                ( f 0₂) (refl)
                                ( pt-⌈𝕀⌉ x0)
                                ( rev ⌈𝕀⌉ (pt-⌈𝕀⌉ x0) (f 0₂) refl)
                                c
                          in
                            concat (D x0)
                              ( H-sec j 0₂ c)
                              ( p 0₂ c-mid)
                              ( p 0₂ c)
                              ( id-arr-covariant-transport-II
                                  ⌈𝕀⌉ (pt-⌈𝕀⌉ x0) DS cov-D (p 0₂ c-mid))
                              ( ap
                                  ( op-family-at C
                                      ( op-shape-point-flip (pt-⌈𝕀⌉ x0)))
                                  ( D x0)
                                  ( c-mid) (c) (p 0₂)
                                  ( covariant-transport-line-inv-const-II C is-cov-C x0 c)))
              in
              let r
 : ( j : 𝕀) → H-sec j 0₂ = f0
                :=
                  \ j →
                    concat (E 0₂) (H-sec j 0₂) (p 0₂) f0 (d j) q
              in
              let pack
 : ( j : 𝕀)
                  → Σ ( φ : (i : 𝕀) → E i) , φ 0₂ = f0
                := \ j → (H-sec j , r j)
              in
              let is-discrete-E-i
 : ( i : 𝕀) → is-discrete-II (E i)
                :=
                  \ i →
                    match (f i)
                      into (\ s →
                        is-discrete-II
                          ( function-family s))
                      ( point a ⇒
                          is-discrete-function-type-II
                            funext
                            ( op-family-at C
                                ( op-shape-point-flip (pt-⌈𝕀⌉ a)))
                            ( \ _ → D a)
                            ( \ _ → disc-D a))
              in
              let is-discrete-E-I
 : is-discrete-II ((i : 𝕀) → E i)
                :=
                  is-discrete-extension-type-II
                    extext
                    ( 𝕀)
                    ( \ _ → TOP)
                    ( \ i → E i)
                    ( is-discrete-E-i)
              in
              let is-discrete-fib
 : ( φ : (i : 𝕀) → E i)
                  → is-discrete-II (φ 0₂ = f0)
                :=
                  \ φ →
                    is-discrete-Id-II extext
                      ( E 0₂)
                      ( is-discrete-E-i 0₂)
                      ( φ 0₂)
                      f0
              in
              let is-discrete-total
 : is-discrete-II
                    ( Σ ( φ : (i : 𝕀) → E i) , φ 0₂ = f0)
                :=
                  is-discrete-Σ-II
                    ( ( i : 𝕀) → E i)
                    ( \ φ → φ 0₂ = f0)
                    ( is-discrete-E-I)
                    ( is-discrete-fib)
              in
              let pack0-eq
 : pack 0₂ = contr-center
                :=
                  ind-path
                    ( E 0₂)
                    ( p 0₂)
                    ( \ f0' q' →
                        let phi'
 : ( i : 𝕀) → E i
                          :=
                            \ i →
                              extend-along
                                ( f 0₂) (f i) (\ k → f (inf i k)) f0'
                        in
                        let phi0'
 : phi' 0₂ = f0'
                          :=
                            eq-htpy funext
                              ( op-family-at C
                                  ( op-shape-point-flip (pt-⌈𝕀⌉ x0)))
                              ( \ _ → D x0)
                              ( phi' 0₂)
                              ( f0')
                              ( \ c →
                                  let c0'
                                    := transport-line-inv-specified
                                        ( \ k → f (inf 0₂ k))
                                        ( pt-⌈𝕀⌉ x0) (refl)
                                        ( pt-⌈𝕀⌉ x0) (refl)
                                        c
                                  in
                                    concat (D x0)
                                      ( phi' 0₂ c)
                                      ( f0' c0')
                                      ( f0' c)
                                      ( id-arr-covariant-transport-II
                                          ⌈𝕀⌉ (pt-⌈𝕀⌉ x0) DS cov-D (f0' c0'))
                                      ( ap
                                          ( op-family-at C
                                              ( op-shape-point-flip (pt-⌈𝕀⌉ x0)))
                                          ( D x0)
                                          ( c0') (c) (f0')
                                          ( covariant-transport-line-inv-const-II C is-cov-C x0 c)))
                        in
                        let r'
 : ( j : 𝕀) → H-sec j 0₂ = f0'
                          :=
                            \ j →
                              concat
                                ( E 0₂)
                                ( H-sec j 0₂)
                                ( p 0₂)
                                ( f0')
                                ( d j)
                                ( q')
                        in
                          ( H-sec 0₂ , r' 0₂)
                          =_{Σ (φ : (i : 𝕀) → E i) , φ 0₂ = f0'}
  ( phi' , phi0'))
                    ( refl)
                    ( f0)
                    ( q)
              in
              let pack1-eq
 : pack 1₂ = (p , q)
                :=
                  let ptwise
 : ( i : 𝕀) → H-sec 1₂ i = p i
                    :=
                      \ i →
                        ( match (f i)
                            into (\ s →
                              ( pa : function-family s)
                              → extend-along s s (\ _ → s) pa = pa)
                            ( point a ⇒
                                \ pa →
                                    eq-htpy funext
                                      ( op-family-at C
                                          ( op-shape-point-flip (pt-⌈𝕀⌉ a)))
                                      ( \ _ → D a)
                                      ( extend-along
                                          ( pt-⌈𝕀⌉ a) (pt-⌈𝕀⌉ a)
                                          ( \ _ → pt-⌈𝕀⌉ a) pa)
                                      ( pa)
                                      ( \ c →
                                          let c-mid
                                            := transport-line-inv-endpoints
                                                ( \ _ → pt-⌈𝕀⌉ a) c
                                          in
                                            concat (D a)
                                              ( extend-along
                                                  ( pt-⌈𝕀⌉ a) (pt-⌈𝕀⌉ a)
                                                  ( \ _ → pt-⌈𝕀⌉ a) pa c)
                                              ( pa c-mid)
                                              ( pa c)
                                              ( id-arr-covariant-transport-II
                                                  ⌈𝕀⌉ (pt-⌈𝕀⌉ a) DS cov-D (pa c-mid))
                                              ( ap
                                                  ( op-family-at C
                                                      ( op-shape-point-flip (pt-⌈𝕀⌉ a)))
                                                  ( D a)
                                                  ( c-mid) (c) (pa)
                                                  ( covariant-transport-line-inv-const-II C is-cov-C a c)))))
                            ( p i)
                  in
                  let H-sec1=p
 : H-sec 1₂ = p
                    :=
                      first
                        ( second
                            ( extext
                                ( 𝕀)
                                ( \ _ → TOP)
                                ( \ _ → BOT)
                                ( \ i → E i)
                                ( \ _ → recBOT)
                                ( H-sec 1₂)
                                ( p)))
                        ( ptwise)
                  in
                  let d1=ap-eval
 : d 1₂
                      = ap
                          ( ( i : 𝕀) → E i)
                          ( E 0₂)
                          ( H-sec 1₂)
                          ( p)
                          ( \ φ → φ 0₂)
                          ( H-sec1=p)
                    :=
                      concat
                        ( H-sec 1₂ 0₂ = p 0₂)
                        ( d 1₂)
                        ( ptwise 0₂)
                        ( ap
                            ( ( i : 𝕀) → E i)
                            ( E 0₂)
                            ( H-sec 1₂)
                            ( p)
                            ( \ φ → φ 0₂)
                            ( H-sec1=p))
                        ( refl)
                        ( rev
                            ( H-sec 1₂ 0₂ = p 0₂)
                            ( ap
                                ( ( i : 𝕀) → E i)
                                ( E 0₂)
                                ( H-sec 1₂)
                                ( p)
                                ( \ φ → φ 0₂)
                                ( H-sec1=p))
                            ( ptwise 0₂)
                            ( ap-ext-eq-htpy-at
                                extext
                                𝕀
                                ( \ _ → TOP)
                                ( \ _ → BOT)
                                ( \ i → E i)
                                ( \ _ → recBOT)
                                0₂
                                ( H-sec 1₂)
                                ( p)
                                ( ptwise)))
                  in
                  let pack1-eq-second
 : transport
                        ( ( i : 𝕀) → E i)
                        ( \ φ → φ 0₂ = f0)
                        ( H-sec 1₂)
                        ( p)
                        ( H-sec1=p)
                        ( r 1₂)
                      = q
                    :=
                      transport-section-eq-at-cancel-cube
                        𝕀
                        E
                        0₂
                        f0
                        ( H-sec 1₂)
                        p
                        ( H-sec1=p)
                        ( d 1₂)
                        q
                        ( d1=ap-eval)
                  in
                    eq-pair
                      ( ( i : 𝕀) → E i)
                      ( \ φ → φ 0₂ = f0)
                      ( pack 1₂)
                      ( p , q)
                      ( H-sec1=p
                      , pack1-eq-second)
              in
              let arrow-pack
 : hom-II
                    ( Σ ( φ : (i : 𝕀) → E i) , φ 0₂ = f0)
                    ( pack 0₂)
                    ( pack 1₂)
                := \ t → pack t
              in
              let arrow
 : hom-II
                    ( Σ ( φ : (i : 𝕀) → E i) , φ 0₂ = f0)
                    ( contr-center)
                    ( p , q)
                :=
                  transport
                    ( Σ ( φ : (i : 𝕀) → E i) , φ 0₂ = f0)
                    ( \ z →
                        hom-II
                          ( Σ ( φ : (i : 𝕀) → E i) , φ 0₂ = f0)
                          ( z)
                          ( p , q))
                    ( pack 0₂)
                    ( contr-center)
                    ( pack0-eq)
                    ( transport
                        ( Σ ( φ : (i : 𝕀) → E i) , φ 0₂ = f0)
                        ( \ z →
                            hom-II
                              ( Σ ( φ : (i : 𝕀) → E i) , φ 0₂ = f0)
                              ( pack 0₂)
                              ( z))
                        ( pack 1₂)
                        ( p , q)
                        ( pack1-eq)
                        ( arrow-pack))
              in
                first
                  ( has-inverse-is-equiv
                      ( contr-center = (p , q))
                      ( hom-II
                          ( Σ ( φ : (i : 𝕀) → E i) , φ 0₂ = f0)
                          ( contr-center)
                          ( p , q))
                      ( hom-eq-II
                          ( Σ ( φ : (i : 𝕀) → E i) , φ 0₂ = f0)
                          ( contr-center)
                          ( p , q))
                      ( is-discrete-total contr-center (p , q)))
                  ( arrow)
        in
          is-contr-equiv-is-contr'
            ( Σ ( f1 : E 1₂) , dhom-II (⌈𝕀⌉) (pt-⌈𝕀⌉ 0₂) (pt-⌈𝕀⌉ 1₂) (\ t → pt-⌈𝕀⌉ t) (equiv-ext-shape-family-fwd 𝕀 □¹ E) f0 f1)
            ( Σ ( φ : (i : 𝕀) → E i) , φ 0₂ = f0)
            ( equiv-is-cov-i-coslice E f0)
            ( contr-center , contr-hom))

#def is-covariant-ext uses (funext extext)
  ( phi-i : 𝕀 → ᵒᵖ TOPE)
  ( shape-cov
    : let mod ᵒᵖ phi0 :=
        op-ext-commute-bwd (\ (_ : 𝕀) → TOPE) phi-i
      in
        ᵒᵖ
          ( is-covariant-II ⌈𝕀⌉
              ( equiv-ext-shape-family-fwd 𝕀 □¹ (\ i → Shape 1 (\ _ → phi0 i)))))
  ( D : 𝕀 → U)
  ( cov-D : is-covariant-arrow-II (\ (t : 𝕀 | TOP) → D t))
  ( disc-D : (i : 𝕀) → is-discrete-II (D i))
  : is-covariant-II
      ( ⌈𝕀⌉)
      ( equiv-ext-shape-family-fwd 𝕀 □¹
          ( \ i → (s : 1 | uninvᵒᵖ (phi-i i)) → D i))
  :=
    let C : ᵒᵖ (⌈𝕀⌉ → U)
      :=
        let mod ᵒᵖ phi0 :=
          op-ext-commute-bwd (\ (_ : 𝕀) → TOPE) phi-i
        in
          mod ᵒᵖ
            ( equiv-ext-shape-family-fwd 𝕀 □¹ (\ i → Shape 1 (\ _ → phi0 i)))
    in
    let extension-family : ⌈𝕀⌉ → U
      := equiv-ext-shape-family-fwd 𝕀 □¹
          ( \ i → (s : 1 | uninvᵒᵖ (phi-i i)) → D i)
    in
    let function-family : ⌈𝕀⌉ → U
      := equiv-ext-shape-family-fwd 𝕀 □¹
          ( \ i →
              op-family-at C (op-shape-point-flip (pt-⌈𝕀⌉ i)) → D i)
    in
    let cov-functions
      : is-covariant-II ⌈𝕀⌉ function-family
      := is-covariant-op-function C shape-cov D cov-D disc-D
    in
    let family-equiv
      : ( s : ⌈𝕀⌉)
        → Equiv (extension-family s) (function-family s)
      :=
        \ s →
          match s
            into (\ s' → Equiv (extension-family s') (function-family s'))
            ( point a ⇒
                equiv-comp
                  ( ( t : 1 | uninvᵒᵖ (phi-i a)) → D a)
                  ( Shape 1 (\ _ → uninvᵒᵖ (phi-i a)) → D a)
                  ( ( let mod ᵒᵖ p := phi-i a in
                        ᵒᵖ (Shape 1 (\ _ → p))) → D a)
                  ( equiv-ext-shape-fun
                      funext 1 (\ _ → uninvᵒᵖ (phi-i a)) (\ _ → D a))
                  ( ( \ h c →
                        h (first (equiv-shape-1-op-uninv (phi-i a)) c))
                    , is-equiv-precomp-is-equiv
                        funext
                        ( let mod ᵒᵖ p := phi-i a in
                            ᵒᵖ (Shape 1 (\ _ → p)))
                        ( Shape 1 (\ _ → uninvᵒᵖ (phi-i a)))
                        ( D a)
                        ( first (equiv-shape-1-op-uninv (phi-i a)))
                        ( second (equiv-shape-1-op-uninv (phi-i a)))))
    in
    let family-eq : extension-family = function-family
      := eq-htpy funext ⌈𝕀⌉ (\ _ → U) extension-family function-family
          ( \ s → first (ua
              ( extension-family s) (function-family s)) (family-equiv s))
    in
      transport
        ( ⌈𝕀⌉ → U)
        ( is-covariant-II ⌈𝕀⌉)
        ( function-family) (extension-family)
        ( rev (⌈𝕀⌉ → U) extension-family function-family family-eq)
        cov-functions

```
