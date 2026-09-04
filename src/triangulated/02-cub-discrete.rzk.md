# 2x. Discreteness over the interval `𝕀`

This is a literate `rzk` file: it mirrors the `Δ¹`-based discreteness theory of
`simplicial-hott/07-discrete.rzk.md` over the built-in interval `𝕀`, giving
`is-discrete-II`, its comparison with `𝕀`-locality, and the closure properties
(extension types, identity types, `Σ`-types) needed for amazing covariance.

```rzk
#lang rzk-1

#assume extext : ExtExt
```

## Prerequisites

- `hott/03-equivalences.rzk.md` — `is-equiv`, `Equiv`, `equiv-comp`, `equiv-triple-comp`, `is-equiv-homotopy`, `Equiv-of-maps`, `is-equiv-Equiv-is-equiv`, `is-equiv-Equiv-is-equiv'`.
- `hott/07-contractible.rzk.md` — `is-contr-based-paths`, `is-equiv-are-contr`.
- `hott/09-families-of-maps.rzk.md` — `total-map`, `is-equiv-fiberwise-is-equiv-total`, `is-equiv-total-is-equiv-fiberwise`, `total-equiv-family-of-equiv`, `free-paths`, `constant-free-path`, `is-equiv-constant-free-path`.
- `hott/11-trivial-fibrations.rzk.md` — `equiv-total-pullback-is-equiv`.
- `simplicial-hott/03-extension-types.rzk.md` — `ExtExt`, `equiv-ExtExt`, `ext-htpy-eq`, `equiv-extensions-equiv`, `fubini`, `inv-equiv-axiom-choice`, `equiv-ap-is-equiv`.
- `simplicial-hott/05-segal-types.rzk.md` — `hom-II`, `dhom-from-II`.

## Hom-equality and discreteness over `𝕀`

```rzk
#def is-discrete-II
  ( A : U)
  : U
  := (x : A) → (y : A) → is-equiv (x = y) (hom-II A x y) (hom-eq-II A x y)
```

## Arrow types over `𝕀`

```rzk
#def arr-II
  ( A : U)
  : U
  := 𝕀 → A

#def fibered-arr-II'
  ( A : U)
  : U
  := Σ ( ( a , b) : product A A) , hom-II A a b

#def fibered-arr-free-arr-II'
  ( A : U)
  : arr-II A → fibered-arr-II' A
  := \ σ → ((σ 0₂ , σ 1₂) , σ)

#def is-equiv-fibered-arr-free-arr-II'
  ( A : U)
  : is-equiv (arr-II A) (fibered-arr-II' A) (fibered-arr-free-arr-II' A)
  :=
    ( ( ( \ ((_ , _) , σ) → σ) , (\ _ → refl))
    , ( ( \ ((_ , _) , σ) → σ) , (\ _ → refl)))
```

## `𝕀`-locality

```rzk
#def is-𝕀-local
  ( A : U)
  : U
  := is-equiv A (𝕀 → A) (\ a _ → a)

#def equiv-of-maps-total-map-hom-eq-const-𝕀
  ( A : U)
  : Equiv-of-maps
    ( A) (𝕀 → A)
    ( \ a _ → a)
    ( free-paths A) (fibered-arr-II' A)
    ( \ ((a , b) , p) → ((a , b) , hom-eq-II A a b p))
  :=
  ( ( ( constant-free-path A
      , fibered-arr-free-arr-II' A)
    , \ _ → refl)
  , ( is-equiv-constant-free-path A
    , is-equiv-fibered-arr-free-arr-II' A))

#def is-𝕀-local-is-discrete-II
  ( A : U)
  ( is-discrete-II-A : is-discrete-II A)
  : is-𝕀-local A
  :=
    is-equiv-Equiv-is-equiv (A) (𝕀 → A) (\ a _ → a)
      ( free-paths A) (fibered-arr-II' A)
      ( \ ((a , b) , p) → ((a , b) , hom-eq-II A a b p))
    ( equiv-of-maps-total-map-hom-eq-const-𝕀 A)
    ( is-equiv-total-is-equiv-fiberwise
        ( product A A) (\ (a , b) → a = b) (\ (a , b) → hom-II A a b)
      ( \ (a , b) → hom-eq-II A a b)
      ( \ (a , b) → is-discrete-II-A a b))

#def is-discrete-is-𝕀-local-II
  ( A : U)
  ( is-𝕀-local-A : is-𝕀-local A)
  : is-discrete-II A
  :=
  \ a b →
    ( is-equiv-fiberwise-is-equiv-total (product A A) (\ (a , b) → a = b)
        ( \ (a , b) → hom-II A a b)
      ( \ (a , b) → hom-eq-II A a b)
      ( is-equiv-Equiv-is-equiv' (A) (𝕀 → A) (\ a _ → a)
          ( free-paths A) (fibered-arr-II' A)
          ( \ ((a , b) , p) → ((a , b) , hom-eq-II A a b p))
        ( equiv-of-maps-total-map-hom-eq-const-𝕀 A)
        ( is-𝕀-local-A)))
    ( a , b)
```

## The boundary of the `𝕀`-arrow

```rzk
#def ∂𝕀
  : 𝕀 → TOPE
  := \ t → (t ≡ 0₂ ∨ t ≡ 1₂)
```

## Extension types into discrete families

```rzk
#def equiv-hom-eq-extension-type-is-discrete-II uses (extext)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( A : ψ → U)
  ( is-discrete-A : (t : ψ) → is-discrete-II (A t))
  ( f g : (t : ψ) → A t)
  : Equiv (f = g) (hom-II ((t : ψ) → A t) f g)
  :=
    equiv-triple-comp
      ( f = g)
      ( ( t : ψ) → f t = g t)
      ( ( t : ψ) → hom-II (A t) (f t) (g t))
      ( hom-II ((t : ψ) → A t) f g)
      ( equiv-ExtExt extext I ψ (\ _ → BOT) A (\ _ → recBOT) f g)
      ( equiv-extensions-equiv extext I ψ (\ _ → BOT)
        ( \ t → f t = g t)
        ( \ t → hom-II (A t) (f t) (g t))
        ( \ t → (hom-eq-II (A t) (f t) (g t) , (is-discrete-A t (f t) (g t))))
        ( \ _ → recBOT))
      ( fubini
        ( I)
        ( 𝕀)
        ( ψ)
        ( \ t → BOT)
        ( \ (_ : 𝕀) → TOP)
        ( ∂𝕀)
        ( \ t s → A t)
        ( \ (t , s) → recOR (s ≡ 0₂ ↦ f t , s ≡ 1₂ ↦ g t)))

#def compute-hom-eq-extension-type-is-discrete-II uses (extext)
  ( I : CUBE)
  ( ψ : (t : I) → TOPE)
  ( A : ψ → U)
  ( is-discrete-A : (t : ψ) → is-discrete-II (A t))
  ( f g : (t : ψ) → A t)
  ( h : f = g)
  : ( hom-eq-II ((t : ψ) → A t) f g h)
  = ( first (equiv-hom-eq-extension-type-is-discrete-II I ψ A is-discrete-A f g)) h
  :=
    ind-path
      ( ( t : ψ) → A t)
      ( f)
      ( \ g' h' →
        ( hom-eq-II ((t : ψ) → A t) f g' h')
      = ( first (equiv-hom-eq-extension-type-is-discrete-II I ψ A is-discrete-A f g') h'))
      ( refl)
      ( g)
      ( h)

#def is-discrete-extension-type-II uses (extext)
  ( I : CUBE)
  ( ψ : (t : I) → TOPE)
  ( A : ψ → U)
  ( is-discrete-A : (t : ψ) → is-discrete-II (A t))
  : is-discrete-II ((t : ψ) → A t)
  :=
    \ f g →
    is-equiv-homotopy
      ( f = g)
      ( hom-II ((t : ψ) → A t) f g)
      ( hom-eq-II ((t : ψ) → A t) f g)
      ( first (equiv-hom-eq-extension-type-is-discrete-II I ψ A is-discrete-A f g))
      ( compute-hom-eq-extension-type-is-discrete-II I ψ A is-discrete-A f g)
      ( second (equiv-hom-eq-extension-type-is-discrete-II I ψ A is-discrete-A f g))
```

## `Σ`-types of discrete families

```rzk
#def is-discrete-Σ-II
  ( A : U)
  ( B : A → U)
  ( is-discrete-A : is-discrete-II A)
  ( is-discrete-B : (a : A) → is-discrete-II (B a))
  : is-discrete-II (Σ (a : A) , B a)
  :=
    is-discrete-is-𝕀-local-II
      ( Σ (a : A) , B a)
      ( second
        ( equiv-comp
          ( Σ (a : A) , B a)
          ( Σ (φ : 𝕀 → A) , ((t : 𝕀) → B (φ t)))
          ( 𝕀 → (Σ (a : A) , B a))
          ( equiv-comp
            ( Σ (a : A) , B a)
            ( Σ (a : A) , (𝕀 → B a))
            ( Σ (φ : 𝕀 → A) , ((t : 𝕀) → B (φ t)))
            ( total-equiv-family-of-equiv
              ( A) (B) (\ a → 𝕀 → B a)
              ( \ a → (\ b _ → b , is-𝕀-local-is-discrete-II (B a) (is-discrete-B a))))
            ( equiv-total-pullback-is-equiv
              ( A) (𝕀 → A) (\ a _ → a)
              ( is-𝕀-local-is-discrete-II A is-discrete-A)
              ( \ φ → (t : 𝕀) → B (φ t))))
          ( inv-equiv-axiom-choice
            ( 𝕀) (\ _ → TOP) (\ _ → BOT) (\ _ → A) (\ _ x → B x)
            ( \ _ → recBOT) (\ _ → recBOT))))
```

## Identity types of discrete types

```rzk
#def is-discrete-Id-II uses (extext)
  ( A : U)
  ( is-discrete-A : is-discrete-II A)
  ( x y : A)
  : is-discrete-II (x = y)
  :=
    let la : is-equiv A (𝕀 → A) (\ a _ → a)
      := is-𝕀-local-is-discrete-II A is-discrete-A
    in
    let e : Equiv (x = y) (𝕀 → (x = y))
      := equiv-comp (x = y)
           ( (\ (_ : 𝕀) → x) = (\ (_ : 𝕀) → y))
           ( 𝕀 → (x = y))
           ( equiv-ap-is-equiv A (𝕀 → A) (\ a _ → a) la x y)
           ( equiv-ExtExt extext 𝕀 (\ _ → TOP) (\ _ → BOT) (\ _ → A) (\ _ → recBOT)
               (\ _ → x) (\ _ → y))
    in
    is-discrete-is-𝕀-local-II (x = y)
      ( is-equiv-homotopy (x = y) (𝕀 → (x = y))
          ( \ p _ → p)
          ( first e)
          ( \ p → ind-path A x
              ( \ y' p' →
                  ( \ (_ : 𝕀 | ⊤) → p')
                  = ext-htpy-eq 𝕀 (\ _ → TOP) (\ _ → BOT) (\ _ → A) (\ _ → recBOT)
                      (\ _ → x) (\ _ → y')
                      ( ap A (𝕀 → A) x y' (\ a _ → a) p'))
              ( refl)
              ( y) (p))
          ( second e))
```
