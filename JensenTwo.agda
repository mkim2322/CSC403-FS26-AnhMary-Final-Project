{-# OPTIONS --safe --without-K #-}

module JensenTwo where

open import Relation.Binary.PropositionalEquality using (_≡_)

record OrderedStructure : Set₁ where
  infix  4 _≤_
  infixl 6 _+_
  infixl 7 _*_
  field
    Carrier : Set
    _≤_     : Carrier → Carrier → Set
    0# 1#   : Carrier
    _+_ _*_ : Carrier → Carrier → Carrier
    ≤-refl  : ∀ {x} → x ≤ x
    ≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
    +-mono  : ∀ {x y u v} → x ≤ y → u ≤ v → x + u ≤ y + v
    *-mono  : ∀ {t x y} → 0# ≤ t → x ≤ y → t * x ≤ t * y

module Jensen (S : OrderedStructure) where
  open OrderedStructure S renaming (Carrier to ℝ)

  Convex : (ℝ → ℝ) → Set
  Convex f =
    ∀ (t s x y : ℝ) → 0# ≤ t → 0# ≤ s → t + s ≡ 1#
    → f (t * x + s * y) ≤ t * f x + s * f y

  data Dist : Set where
    pure : ℝ → Dist
    mix  : (t s : ℝ) → 0# ≤ t → 0# ≤ s → t + s ≡ 1# → Dist → Dist → Dist

  mean : Dist → ℝ
  mean (pure x)            = x
  mean (mix t s _ _ _ d e) = t * mean d + s * mean e

  expect : (ℝ → ℝ) → Dist → ℝ
  expect f (pure x)            = f x
  expect f (mix t s _ _ _ d e) = t * expect f d + s * expect f e

  jensen : (f : ℝ → ℝ) → Convex f → (d : Dist) → f (mean d) ≤ expect f d
  jensen f cf (pure x) = ≤-refl
  jensen f cf (mix t s 0≤t 0≤s t+s≡1 d e) =
    ≤-trans
      (cf t s (mean d) (mean e) 0≤t 0≤s t+s≡1)
      (+-mono (*-mono 0≤t (jensen f cf d))
              (*-mono 0≤s (jensen f cf e)))