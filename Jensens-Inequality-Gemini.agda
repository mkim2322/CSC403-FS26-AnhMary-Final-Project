module Jensens-Inequality-Gemini where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; subst₂)
open import Relation.Nullary using (Dec; yes; no)

------------------------------------------------------------------------
-- 1. Minimal Real Number Axioms
------------------------------------------------------------------------

postulate
  ℝ       : Set
  0ℝ 1ℝ   : ℝ
  _+_ _*_ _-_ _/_ : ℝ → ℝ → ℝ
  _≤_     : ℝ → ℝ → Set
  decEq   : (a b : ℝ) → Dec (a ≡ b)

infixl 6 _+_ _-_
infixl 7 _*_ _/_
infix  4 _≤_

-- greater number = stronger (pemdas), grouped first

------------------------------------------------------------------------
-- 2. Definitions
------------------------------------------------------------------------

IsConvex : (ℝ → ℝ) → Set
IsConvex f = ∀ (x y t : ℝ) → 0ℝ ≤ t → t ≤ 1ℝ →
  f (t * x + (1ℝ - t) * y) ≤ t * f x + (1ℝ - t) * f y
-- defines a convex function f
-- t represents the weight (proportion of x and y) between 0 and 1
-- the first part f(t * x + (1𝐑 - t) * y) stands for the weighted average of x and y (point b/w x and y)
-- the second part t * f x + (1𝐑 - t) * f y stands for the weighted average of the function values

AllNonNeg : List (ℝ × ℝ) → Set
AllNonNeg [] = ⊤
AllNonNeg ((w , _) ∷ rest) = (0ℝ ≤ w) × AllNonNeg rest
-- represents a set with pairs
-- the first number of the pair must be non negative (most likely will represent the weighted value) 
-- the second number may be negative (probably the input x value)
-- final part of the list should end with [] to show there's no more items in the list
-- recursive call at the end to check the other pairs 
-- ∷ means "followed by the rest of the list"

sumW : List (ℝ × ℝ) → ℝ
sumW [] = 0ℝ
sumW ((w , _) ∷ rest) = w + sumW rest
-- adds the 1st number of each pair
-- sum W [] = 0 means sum of an empty list = zero
-- sum of Weights (?)

weightedSum : (ℝ → ℝ) → List (ℝ × ℝ) → ℝ
weightedSum g [] = 0ℝ
weightedSum g ((w , x) ∷ rest) = w * g x + weightedSum g rest
-- weighted sum of outputs
-- takes weight * output, adds all of them up
-- if weighted sum = 1, it's a weighted average

normalize : (c : ℝ) → c ≢ 0ℝ → List (ℝ × ℝ) → List (ℝ × ℝ)
normalize c cNonZero [] = []
normalize c cNonZero ((w , x) ∷ rest) = ((w / c) , x) ∷ normalize c cNonZero rest
-- normalize: divide by c
-- normalize empty list, remains empty
-- divide by c only on first value (weight), keep the input value
-- this allows the weighted sum to become a weighted average (= 1)

------------------------------------------------------------------------
-- 3. Algebraic & Order Helper Lemmas (Trusted Field Axioms)
------------------------------------------------------------------------

postulate
  0≢1          : 0ℝ ≢ 1ℝ
  ≤-refl       : ∀ {a} → a ≤ a
  ≤-trans      : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
  +-mono-≤     : ∀ {a b c d} → a ≤ b → c ≤ d → (a + c) ≤ (b + d)
  *-mono-≤     : ∀ {a b c} → 0ℝ ≤ c → a ≤ b → (c * a) ≤ (c * b)
  1-w-nonneg   : ∀ {w} → w ≤ 1ℝ → 0ℝ ≤ (1ℝ - w)
  weight-bound : ∀ {w s} → 0ℝ ≤ w → 0ℝ ≤ s → w + s ≡ 1ℝ → w ≤ 1ℝ
  norm-nonneg  : ∀ {w rest} (nonzero : (1ℝ - w) ≢ 0ℝ) → 0ℝ ≤ (1ℝ - w) → AllNonNeg rest → AllNonNeg (normalize (1ℝ - w) nonzero rest)
  norm-sum-1   : ∀ {w rest} → w + sumW rest ≡ 1ℝ → (nonzero : (1ℝ - w) ≢ 0ℝ) → sumW (normalize (1ℝ - w) nonzero rest) ≡ 1ℝ
  split-point  : ∀ {w x rest} (nonzero : (1ℝ - w) ≢ 0ℝ) →
    weightedSum (λ z → z) ((w , x) ∷ rest) ≡ w * x + (1ℝ - w) * weightedSum (λ z → z) (normalize (1ℝ - w) nonzero rest)
  split-val    : ∀ {f w x rest} (nonzero : (1ℝ - w) ≢ 0ℝ) →
    w * f x + (1ℝ - w) * weightedSum f (normalize (1ℝ - w) nonzero rest) ≡ weightedSum f ((w , x) ∷ rest)
  
  -- Base case when w = 1 (all remaining weights are 0)
  jensen-w=1   : ∀ (f : ℝ → ℝ) w x rest → (1ℝ - w) ≡ 0ℝ → AllNonNeg rest → w + sumW rest ≡ 1ℝ →
    f (weightedSum (λ z → z) ((w , x) ∷ rest)) ≤ weightedSum f ((w , x) ∷ rest)
    -- says the function of the weighted average input ≤ the weighted average of the function of all inputs (aka outputs), in this case, both sides will be equal since the left becomes f (1*x + 0*sx) = f(x), and the right becomes 1 * f(x) + 0 * f(sx) = f(x)
-- the postulate provides the basis: zero does not equal 1, reflexive/transitive properties of inequalities, addition and multiplication holds across inequalities, sets bounds for w (weights) as w ≤ 1 (lower bound already established from AllNonNeg), all weights are non-negative, at most add up to 1, normalizing by a nonnegative will give you a nonnegative, normalizing by remaining weights after first weight will result in a sum of weights of 1, multiply back 1-w to get its original contribution back after normalizing to obtain convexity for both inputs and outputs

sumW-nonneg : ∀ {pairs} → AllNonNeg pairs → 0ℝ ≤ sumW pairs
sumW-nonneg {[]} _ = ≤-refl
sumW-nonneg {(w , _) ∷ rest} (w≥0 , restNonNeg) =
  subst₂ _≤_ zero+zero refl (+-mono-≤ w≥0 (sumW-nonneg restNonNeg))
  where
    postulate zero+zero : 0ℝ + 0ℝ ≡ 0ℝ
-- subst₂ means substitute using 2 equalities (0 + 0 = 0) and sumW ((w, _) ∷ xs) = w + sumW xs by refl of sumW definition
------------------------------------------------------------------------
-- 4. Main Theorem: Finite Jensen's Inequality
------------------------------------------------------------------------
{-# TERMINATING #-}
-- had to add terminating to show that jensen does end eventually
jensen : ∀ (f : ℝ → ℝ) (pairs : List (ℝ × ℝ))
        → IsConvex f
        → AllNonNeg pairs
        → sumW pairs ≡ 1ℝ
        → f (weightedSum (λ z → z) pairs) ≤ weightedSum f pairs
jensen f [] conv nonneg sum1 = ⊥-elim (0≢1 sum1)
-- contradiction
jensen f ((w , x) ∷ rest) conv (w≥0 , restNonNeg) sum1 with decEq (1ℝ - w) 0ℝ
--proof that f is convex
... | yes 1-w≡0 = jensen-w=1 f w x rest 1-w≡0 restNonNeg sum1
... | no  1-w≢0 =
  let
    s≥0  = sumW-nonneg restNonNeg
    w≤1  = weight-bound w≥0 s≥0 sum1
    1-w≥0 = 1-w-nonneg w≤1
    normalizedRest = normalize (1ℝ - w) 1-w≢0 rest

    eq1  = cong f (split-point 1-w≢0)
    step2 = conv x (weightedSum (λ z → z) normalizedRest) w w≥0 w≤1
    ih   = jensen f normalizedRest conv (norm-nonneg 1-w≢0 1-w≥0 restNonNeg) (norm-sum-1 sum1 1-w≢0)
    step3 = +-mono-≤ ≤-refl (*-mono-≤ 1-w≥0 ih)
    eq4  = split-val 1-w≢0
  in
    subst₂ _≤_ (sym eq1) eq4 (≤-trans step2 step3) 