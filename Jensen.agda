-- Jensen's inequality (finite, weighted form) over an abstract ordered field.
--
--   f convex,  wᵢ > 0,  Σ wᵢ = 1   ⟹   f (Σ wᵢ xᵢ) ≤ Σ wᵢ f(xᵢ)
--
-- The standard library has no real numbers, so we abstract over an ordered
-- field (instantiate with ℚ, a constructive ℝ, ...).  The proof is by
-- induction on the list of weighted points, renormalising the tail.

module Jensen where

open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

------------------------------------------------------------------------
-- Interface: just the laws the proof needs

record OrderedField : Set₁ where
  infix  4 _≤_ _<_
  infixl 6 _+_
  infixl 7 _*_
  field
    F          : Set
    0# 1#      : F
    _+_ _*_    : F → F → F
    _≤_ _<_    : F → F → Set
    inv        : F → F

    -- ring laws
    +-identityʳ : ∀ a → a + 0# ≡ a
    *-zeroʳ     : ∀ a → a * 0# ≡ 0#
    *-identityˡ : ∀ a → 1# * a ≡ a
    *-comm      : ∀ a b → a * b ≡ b * a
    *-assoc     : ∀ a b c → (a * b) * c ≡ a * (b * c)
    distribˡ    : ∀ a b c → a * (b + c) ≡ a * b + a * c

    -- inverses of positive elements
    inv-invʳ    : ∀ a → 0# < a → a * inv a ≡ 1#
    inv-pos     : ∀ {a} → 0# < a → 0# < inv a

    -- order
    ≤-refl      : ∀ {a} → a ≤ a
    ≤-trans     : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
    <⇒≤         : ∀ {a b} → a < b → a ≤ b
    +-pos       : ∀ {a b} → 0# < a → 0# < b → 0# < a + b
    *-pos       : ∀ {a b} → 0# < a → 0# < b → 0# < a * b
    +-monoʳ-≤   : ∀ c {a b} → a ≤ b → c + a ≤ c + b
    *-monoˡ-≤   : ∀ {c a b} → 0# ≤ c → a ≤ b → c * a ≤ c * b

------------------------------------------------------------------------

module Jensen (𝔽 : OrderedField) where
  open OrderedField 𝔽

  -- A weighted point is (weight , point).
  Pt : Set
  Pt = F × F

  wsum mean : List Pt → F
  wsum []             = 0#
  wsum ((w , x) ∷ l)  = w + wsum l
  mean []             = 0#
  mean ((w , x) ∷ l)  = w * x + mean l

  fsum : (F → F) → List Pt → F
  fsum f []             = 0#
  fsum f ((w , x) ∷ l)  = w * f x + fsum f l

  scale : F → List Pt → List Pt
  scale c []             = []
  scale c ((w , x) ∷ l)  = (c * w , x) ∷ scale c l

  -- all weights strictly positive
  data AllPos : List Pt → Set where
    []ᵖ   : AllPos []
    _∷ᵖ_  : ∀ {w x l} → 0# < w → AllPos l → AllPos ((w , x) ∷ l)

  -- Convexity (two-point form)
  Convex : (F → F) → Set
  Convex f = ∀ x y a b → 0# ≤ a → 0# ≤ b → a + b ≡ 1#
           → f (a * x + b * y) ≤ a * f x + b * f y

  ----------------------------------------------------------------------
  -- Lemmas about scaling

  scale-wsum : ∀ c l → wsum (scale c l) ≡ c * wsum l
  scale-wsum c []            = sym (*-zeroʳ c)
  scale-wsum c ((w , x) ∷ l) =
    trans (cong (λ z → c * w + z) (scale-wsum c l))
          (sym (distribˡ c w (wsum l)))

  scale-mean : ∀ c l → mean (scale c l) ≡ c * mean l
  scale-mean c []            = sym (*-zeroʳ c)
  scale-mean c ((w , x) ∷ l) =
    trans (cong₂ _+_ (*-assoc c w x) (scale-mean c l))
          (sym (distribˡ c (w * x) (mean l)))

  scale-fsum : ∀ f c l → fsum f (scale c l) ≡ c * fsum f l
  scale-fsum f c []            = sym (*-zeroʳ c)
  scale-fsum f c ((w , x) ∷ l) =
    trans (cong₂ _+_ (*-assoc c w (f x)) (scale-fsum f c l))
          (sym (distribˡ c (w * f x) (fsum f l)))

  scale-pos : ∀ {c l} → 0# < c → AllPos l → AllPos (scale c l)
  scale-pos pc []ᵖ         = []ᵖ
  scale-pos pc (pw ∷ᵖ pl)  = *-pos pc pw ∷ᵖ scale-pos pc pl

  wsum-pos : ∀ {w x l} → AllPos ((w , x) ∷ l) → 0# < wsum ((w , x) ∷ l)
  wsum-pos {w} {l = []} (pw ∷ᵖ _) =
    subst (λ z → 0# < z) (sym (+-identityʳ w)) pw
  wsum-pos {l = _ ∷ _}  (pw ∷ᵖ pl) = +-pos pw (wsum-pos pl)

  cancel : ∀ t → 0# < t → ∀ m → t * (inv t * m) ≡ m
  cancel t pt m =
    trans (sym (*-assoc t (inv t) m))
          (trans (cong (λ z → z * m) (inv-invʳ t pt))
                 (*-identityˡ m))

  *-zeroˡ : ∀ a → 0# * a ≡ 0#
  *-zeroˡ a = trans (*-comm 0# a) (*-zeroʳ a)

  ----------------------------------------------------------------------
  -- Jensen's inequality

  {-# TERMINATING #-}
  jensen : ∀ f → Convex f → ∀ (p : Pt) (ps : List Pt)
         → AllPos (p ∷ ps) → wsum (p ∷ ps) ≡ 1#
         → f (mean (p ∷ ps)) ≤ fsum f (p ∷ ps)

  -- one point: its weight is 1
  jensen f cv (w , x) [] (pw ∷ᵖ _) s =
    let step  = cv x x w 0# (<⇒≤ pw) ≤-refl s
        step₁ = subst (λ v → f (w * x + 0# * x) ≤ w * f x + v)
                      (*-zeroˡ (f x)) step
    in subst (λ u → f (w * x + u) ≤ w * f x + 0#) (*-zeroˡ x) step₁

  -- inductive step: split off the head, renormalise the tail
  jensen f cv (w , x) ((w′ , x′) ∷ ps′) (pw ∷ᵖ pl) s =
    let l′   = (w′ , x′) ∷ ps′
        t    = wsum l′
        t>0  = wsum-pos pl
        c    = inv t
        norm = scale c l′

        norm-pos : AllPos norm
        norm-pos = scale-pos (inv-pos t>0) pl

        norm-sum : wsum norm ≡ 1#
        norm-sum = trans (scale-wsum c l′)
                         (trans (*-comm c t) (inv-invʳ t t>0))

        -- induction hypothesis for the normalised tail
        ih : f (mean norm) ≤ fsum f norm
        ih = jensen f cv (c * w′ , x′) (scale c ps′) norm-pos norm-sum

        y = mean norm

        recoverM : t * y ≡ mean l′
        recoverM = trans (cong (λ z → t * z) (scale-mean c l′))
                         (cancel t t>0 (mean l′))

        recoverF : t * fsum f norm ≡ fsum f l′
        recoverF = trans (cong (λ z → t * z) (scale-fsum f c l′))
                         (cancel t t>0 (fsum f l′))

        -- convexity for head vs. (renormalised) tail
        conv : f (w * x + t * y) ≤ w * f x + t * f y
        conv = cv x y w t (<⇒≤ pw) (<⇒≤ t>0) s

        step : w * f x + t * f y ≤ w * f x + t * fsum f norm
        step = +-monoʳ-≤ (w * f x) (*-monoˡ-≤ (<⇒≤ t>0) ih)

        rhs : w * f x + t * fsum f norm ≡ w * f x + fsum f l′
        rhs = cong (λ z → w * f x + z) recoverF

        lhs : w * x + t * y ≡ w * x + mean l′
        lhs = cong (λ z → w * x + z) recoverM

        chain : f (w * x + t * y) ≤ w * f x + fsum f l′
        chain = subst (λ z → f (w * x + t * y) ≤ z) rhs (≤-trans conv step)
    in subst (λ z → f z ≤ w * f x + fsum f l′) lhs chain