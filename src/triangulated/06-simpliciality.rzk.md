# 6. Simpliciality

```rzk
#lang rzk-1

#assume funext : FunExt
```

## Simplicial types

A type is simplicial when it sees every pair of points of the cubical interval
as comparable. The shape below realizes the proposition expressing this
comparability.

```rzk
#def totality-shape
  ( i j : 𝕀)
  : U
  := Shape 1 (\ _ → i ≤ j ∨ j ≤ i)

#def is-simplicial
  ( A : U)
  : U
  := (i j : 𝕀) →
    is-equiv A (totality-shape i j → A) (\ a _ → a)
```

Simpliciality is invariant under equivalence.

```rzk
#def is-simplicial-equiv-is-simplicial uses (funext)
  ( A B : U)
  ( A≃B : Equiv A B)
  ( is-simplicial-B : is-simplicial B)
  : is-simplicial A
  :=
    \ i j →
      let P : U := totality-shape i j in
      is-equiv-Equiv-is-equiv
        ( A) (P → A) (\ a _ → a)
        ( B) (P → B) (\ b _ → b)
        ( ( ( first A≃B
            , \ f p → first A≃B (f p))
          , \ _ → refl)
        , ( second A≃B
          , second
              ( equiv-function-equiv-family
                  funext P (\ _ → A) (\ _ → B) (\ _ → A≃B))))
        ( is-simplicial-B i j)
```

## Closure properties

Simplicial types are closed under dependent function types.

```rzk
#def is-simplicial-function-type uses (funext)
  ( X : U)
  ( A : X → U)
  ( is-simplicial-A : (x : X) → is-simplicial (A x))
  : is-simplicial ((x : X) → A x)
  :=
    \ i j →
      let P : U := totality-shape i j in
      is-equiv-comp
        ( (x : X) → A x)
        ( (x : X) → P → A x)
        ( P → (x : X) → A x)
        ( \ f x _ → f x)
        ( is-equiv-function-is-equiv-family
            funext X A (\ x → P → A x)
            ( \ _ a _ → a)
            ( \ x → is-simplicial-A x i j))
        ( \ f p x → f x p)
        ( is-equiv-has-inverse
            ( (x : X) → P → A x)
            ( P → (x : X) → A x)
            ( \ f p x → f x p)
            ( \ g x p → g p x
            , (\ _ → refl , \ _ → refl)))
```

Simplicial types are closed under dependent sums.

```rzk
#def is-simplicial-Σ
  ( A : U)
  ( B : A → U)
  ( is-simplicial-A : is-simplicial A)
  ( is-simplicial-B : (a : A) → is-simplicial (B a))
  : is-simplicial (Σ (a : A) , B a)
  :=
    \ i j →
      let P : U := totality-shape i j in
      second
        ( equiv-triple-comp
            ( Σ (a : A) , B a)
            ( Σ (a : A) , P → B a)
            ( Σ (f : P → A) , (p : P) → B (f p))
            ( P → Σ (a : A) , B a)
            ( total-equiv-family-of-equiv
                A B (\ a → P → B a)
                ( \ a → (\ b _ → b , is-simplicial-B a i j)))
            ( equiv-total-pullback-is-equiv
                A (P → A) (\ a _ → a)
                ( is-simplicial-A i j)
                ( \ f → (p : P) → B (f p)))
            ( inv-equiv-choice P (\ _ → A) (\ p a → B a)))
```

Simplicial types are closed under identity types.

```rzk
#def is-simplicial-Id uses (funext)
  ( A : U)
  ( is-simplicial-A : is-simplicial A)
  ( x y : A)
  : is-simplicial (x = y)
  :=
    \ i j →
      let P : U := totality-shape i j in
      let is-equiv-const : is-equiv A (P → A) (\ a _ → a)
        := is-simplicial-A i j in
      let e : Equiv (x = y) (P → (x = y))
        := equiv-comp
            ( x = y)
            ( (\ (_ : P) → x) = (\ (_ : P) → y))
            ( P → (x = y))
            ( equiv-ap-is-equiv
                A (P → A) (\ a _ → a) is-equiv-const x y)
            ( equiv-FunExt
                funext P (\ _ → A) (\ _ → x) (\ _ → y)) in
      is-equiv-homotopy
        ( x = y)
        ( P → (x = y))
        ( \ p _ → p)
        ( first e)
        ( \ p →
            ind-path A x
              ( \ y' p' →
                  (\ (_ : P) → p')
                  = htpy-eq P (\ _ → A)
                      (\ _ → x) (\ _ → y')
                      (ap A (P → A) x y' (\ a _ → a) p'))
              ( refl)
              ( y) (p))
        ( second e)
```

## The simplicial monad

GWB24, Proposition 3.1.

```rzk
#postulate simp-monad (A : U) : U

#postulate is-simplicial-simp-monad (A : U)
  : is-simplicial (simp-monad A)

#postulate simp-monad-pure (A : U) : A → simp-monad A
```

Consequently, a type equivalent to its simplicial reflection is simplicial.

```rzk
#def is-simplicial-equiv-simp-monad uses (funext)
  ( A : U)
  ( A≃simp-A : Equiv A (simp-monad A))
  : is-simplicial A
  :=
    is-simplicial-equiv-is-simplicial
      A (simp-monad A) A≃simp-A (is-simplicial-simp-monad A)
```
