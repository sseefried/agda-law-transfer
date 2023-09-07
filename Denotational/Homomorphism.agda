{-# OPTIONS --without-K --safe #-}

open import Level using (Level)
open import Data.Product using (_,_)
open import Level using (Level ; _⊔_ ; suc)
open import Relation.Binary.Core using (Rel)
open import Algebra.Core using (Op₁ ; Op₂)

module Denotational.Homomorphism
  {a b} {ℓ} {A : Set a} {B : Set b}
  (⟦_⟧ : A → B) (_≈ᴮ_ : Rel B ℓ)
  where


record HasBinOp {a} (A : Set a) : Set a where
  infixr 29 _∙_
  field
    _∙_ : A → A → A

record HasIdentity {a} (A : Set a) : Set a where
  field
    ε : A

record HasInverse {a} (A : Set a) : Set a where
  infix 21 _⁻¹
  field
    _⁻¹ : A → A

-- 1 binary operation & 1 element
record HasMonoidOps {a} (A : Set a) : Set a where
  infixr 29 _∙_
  field
    _∙_ : A → A → A
    ε   : A

  instance -- methods must be named to be re-exported
    hasBinOpFromMonoid : HasBinOp A
    hasBinOpFromMonoid = record { _∙_ = _∙_ }

    hasIdentityFromMonoid : HasIdentity A
    hasIdentityFromMonoid = record { ε = ε }

-- 1 binary operation, 1 unary operation & 1 element
--
-- The name, HasGroupOps, is only representative. Also includes other
-- structures such as UnitalMagma
record HasGroupOps {a} (A : Set a) : Set a where
  infixr 29 _∙_
  infix 21 _⁻¹
  field
    _∙_ : A → A → A
    ε   : A
    _⁻¹ : A → A

  instance -- methods must be named to be re-exported
    hasMonoidOpsFromGroup : HasMonoidOps A
    hasMonoidOpsFromGroup = record { _∙_ = _∙_ ; ε = ε }

    hasInverseFromGroup : HasInverse A
    hasInverseFromGroup = record { _⁻¹ = _⁻¹ }

-- 2 binary operations & 1 element
--
-- The name, HasNearSemiringOps, is only representative. Also includes other
-- structures such as IsSemiringWithoutOne.
record HasNearSemiringOps {a} (A : Set a) : Set a where
  infixr 26 _+_
  infixr 27 _*_
  field
    _+_ : A → A → A
    _*_ : A → A → A
    0#  : A

  instance
    hasMonoidOpsFromNearSemiring : HasMonoidOps A
    hasMonoidOpsFromNearSemiring = record { _∙_ = _+_ ; ε = 0# }

    hasBinOpFromNearSemiring : HasBinOp A
    hasBinOpFromNearSemiring = record { _∙_ = _*_ }

-- 2 binary operations & 2 elements
--
-- The name, HasSemiringOps, is only representative. Also includes other
-- structures such as IsKleeneAlgebra and IsQuasiring
record HasSemiringOps {a} (A : Set a) : Set a where
  infixr 26 _+_
  infixr 27 _*_
  field
    _+_ : A → A → A
    _*_ : A → A → A
    0#  : A
    1#  : A

  instance
    hasPlusZeroMonoidOpsFromNearSemiring : HasMonoidOps A
    hasPlusZeroMonoidOpsFromNearSemiring = record { _∙_ = _+_ ; ε = 0# }

    hasStarOneMonoidOpsFromNearSemiring : HasMonoidOps A
    hasStarOneMonoidOpsFromNearSemiring = record { _∙_ = _*_ ; ε = 1# }

record HasNearringOps {a} (A : Set a) : Set a where
  infixr 26 _+_
  infixr 27 _*_
  infixl 21 _⁻¹
  field
    _+_ : A → A → A
    _*_ : A → A → A
    _⁻¹ : A → A
    0#  : A
    1#  : A

  instance
    hasGroupOpsFromNearringOps : HasGroupOps A
    hasGroupOpsFromNearringOps = record { _∙_ = _*_ ; ε = 1# ; _⁻¹ = _⁻¹ }
    hasMonoidOpsFromNearringOps : HasMonoidOps A
    hasMonoidOpsFromNearringOps = record { _∙_ = _+_ ; ε = 0# }

-- 2 binary operations, 1 unary operation & 2 elements
--
-- The name, HasRingOps, is only representative. Also includes other
-- structures such as IsNonAssociatiaveRing
record HasRingOps {a} (A : Set a) : Set a where
  infixr 26 _+_
  infixr 27 _*_
  field
    _+_ : A → A → A
    _*_ : A → A → A
    -_  : A → A
    0#  : A
    1#  : A

  instance
    hasGroupOpsFromRingOps : HasGroupOps A
    hasGroupOpsFromRingOps = record { _∙_ = _+_ ; ε = 0# ; _⁻¹ = -_ }
    hasMonoidOpsFromRingOps : HasMonoidOps A
    hasMonoidOpsFromRingOps = record { _∙_ = _*_ ; ε = 1# }

-- 3 binary operations
--
-- The name, HasQuasigroupOps, is only representative. Also includes
-- other structures such as IsLoop
record HasQuasigroupOps {a} (A : Set a) : Set a where
  infixr 29 _∙_
  field
    _∙_  : A → A → A
    _\\_ : A → A → A
    _//_ : A → A → A

  instance
    hasBinOpFromQuasigroupOps1 : HasBinOp A
    hasBinOpFromQuasigroupOps1 = record { _∙_ = _∙_ }
    hasBinOpFromQuasigroupOps2 : HasBinOp A
    hasBinOpFromQuasigroupOps2 = record { _∙_ = _\\_ }
    hasBinOpFromQuasigroupOps3 : HasBinOp A
    hasBinOpFromQuasigroupOps3 = record { _∙_ = _//_ }

record Equiv {a} (A : Set a) : Set (a ⊔ suc ℓ) where
  infixr 20 _≈_
  field
    _≈_ : Rel A ℓ

open import Algebra.Definitions
open import Algebra.Structures
open Equiv ⦃ … ⦄

instance
  _ : Equiv B
  _ = record { _≈_ = _≈ᴮ_ }
  _ : Equiv A
  _ = record { _≈_ = _≈ᴬ_ }
        where
          _≈ᴬ_  : Rel A ℓ
          x ≈ᴬ y = ⟦ x ⟧ ≈ ⟦ y ⟧
--
-- Helper functions
--
FromHasBinOp : {a : _} {A : Set a} → ⦃ Equiv A ⦄
             → (Rel A _ → Op₂ A → Set (a ⊔ ℓ)) → HasBinOp A → Set _
FromHasBinOp {a} f o = f _≈_ _∙_
  where open HasBinOp o

FromMonoidOps : {a : _} {A : Set a} → ⦃ Equiv A ⦄
              → (Rel A _ → Op₂ A → A → Set (a ⊔ ℓ)) → HasMonoidOps A → Set _
FromMonoidOps {a} f o = f  _≈_ _∙_ ε
  where open HasMonoidOps o

FromGroupOps : {a : _} {A : Set a} → ⦃ Equiv A ⦄
             → (Rel A _ → Op₂ A → A → Op₁ A → Set (a ⊔ ℓ))
             → HasGroupOps A → Set _
FromGroupOps {a} f o = f _≈_ _∙_ ε _⁻¹
  where open HasGroupOps o

-- The name, FromSemiringOps, is only representative. Also includes
FromSemiringOps : {a : Level} {A : Set a} → ⦃ Equiv A ⦄
            → (Rel A _ → Op₂ A → Op₂ A → A → A → Set (a ⊔ ℓ))
            → HasSemiringOps A → Set _
FromSemiringOps {a} f o = f _≈_ _+_ _*_ 0#  1#
  where open HasSemiringOps o

FromNearringOps : {a : Level} {A : Set a} → ⦃ Equiv A ⦄
            → (Rel A _ → Op₂ A → Op₂ A → A → A → Op₁ A → Set (a ⊔ ℓ))
            → HasNearringOps A → Set _
FromNearringOps {a} f o = f _≈_ _+_ _*_ 0#  1# _⁻¹
  where open HasNearringOps o

FromRingOps : {a : Level} {A : Set a} → ⦃ Equiv A ⦄
            → (Rel A _ → Op₂ A → Op₂ A → Op₁ A → A → A → Set (a ⊔ ℓ))
            → HasRingOps A → Set _
FromRingOps {a} f o = f _≈_ _+_ _*_ -_ 0#  1#
  where open HasRingOps o

FromQuasigroupOps : {a : Level} {A : Set a} → ⦃ Equiv A ⦄
            → (Rel A _ → Op₂ A → Op₂ A → Op₂ A → Set (a ⊔ ℓ))
            → HasQuasigroupOps A → Set _
FromQuasigroupOps {a} f o = f _≈_ _∙_ _\\_ _//_
  where open HasQuasigroupOps o

------------------------------------------------------------------------
-- Structures with 1 binary operation
------------------------------------------------------------------------

record IsMagmaHomomorphism
         ⦃ hasBinOpA : HasBinOp A ⦄
         ⦃ hasBinOpB : HasBinOp B ⦄
         ⦃ isMagmaB : FromHasBinOp IsMagma hasBinOpB ⦄ : Set (a ⊔ ℓ) where

  open HasBinOp ⦃ … ⦄
  open IsMagma ⦃ … ⦄

  field
    ∙-homo : ∀ x y → ⟦ x ∙ y ⟧ ≈ ⟦ x ⟧ ∙ ⟦ y ⟧

  isMagma-trans : IsMagma {a} _≈_ _∙_
  isMagma-trans =
    record { isEquivalence = record { refl = refl ; sym = sym ; trans = trans }
           ; ∙-cong = ∙-congruent
           }
    where
      open import Relation.Binary.Reasoning.Setoid (setoid)

      ∙-congruent : Congruent₂ _≈_ _∙_
      ∙-congruent {x} {y} {u} {v} x≈y u≈v =
        begin
          ⟦ x ∙ u ⟧
        ≈⟨ ∙-homo x u ⟩
          ⟦ x ⟧ ∙ ⟦ u ⟧
        ≈⟨ ∙-cong x≈y u≈v ⟩
          ⟦ y ⟧ ∙ ⟦ v ⟧
        ≈⟨ sym (∙-homo y v) ⟩
          ⟦ y ∙ v ⟧
        ∎

record IsCommutativeMagmaHomomorphism
         ⦃ hasBinOpA : HasBinOp A ⦄
         ⦃ hasBinOpB : HasBinOp B ⦄
         ⦃ isCommutativeMagmaB : FromHasBinOp IsCommutativeMagma hasBinOpB ⦄ : Set (a ⊔ ℓ) where
  open HasBinOp ⦃ … ⦄
  open IsCommutativeMagma ⦃ … ⦄

  instance
    _ : IsMagma {b} _≈_ _∙_
    _ = isMagma

  field
    isMagmaHomomorphism : IsMagmaHomomorphism

  open IsMagmaHomomorphism isMagmaHomomorphism public

  isCommutativeMagma-trans : IsCommutativeMagma {a} _≈_ _∙_
  isCommutativeMagma-trans =
    record
      { isMagma = isMagma-trans
      ; comm = ∙-comm
      }
   where
     open import Relation.Binary.Reasoning.Setoid (setoid)
     ∙-comm : Commutative _≈_ _∙_
     ∙-comm x y =
       begin
         ⟦ x ∙ y ⟧
       ≈⟨ ∙-homo x y ⟩
         ⟦ x ⟧ ∙ ⟦ y ⟧
       ≈⟨ comm ⟦ x ⟧ ⟦ y ⟧ ⟩
         ⟦ y ⟧ ∙ ⟦ x ⟧
       ≈⟨ sym (∙-homo y x) ⟩
         ⟦ y ∙ x ⟧
       ∎

record IsIdempotentMagmaHomomorphism
         ⦃ hasBinOpA : HasBinOp A ⦄
         ⦃ hasBinOpB : HasBinOp B ⦄
         ⦃ isIdempotentMagmaB : FromHasBinOp IsIdempotentMagma hasBinOpB ⦄ : Set (a ⊔ ℓ) where
  open HasBinOp ⦃ … ⦄
  open IsIdempotentMagma ⦃ … ⦄

  instance
    _ : IsMagma {b} _≈_ _∙_
    _ = isMagma

  field
    isMagmaHomomorphism : IsMagmaHomomorphism

  open IsMagmaHomomorphism isMagmaHomomorphism public

  isIdempotentMagma-trans : IsIdempotentMagma {a} _≈_ _∙_
  isIdempotentMagma-trans =
    record
      { isMagma = isMagma-trans
      ; idem = ∙-idem
      }
   where
     open import Relation.Binary.Reasoning.Setoid (setoid)
     ∙-idem : Idempotent _≈_ _∙_
     ∙-idem x =
       begin
         ⟦ x ∙ x ⟧
       ≈⟨ ∙-homo x x ⟩
         ⟦ x ⟧ ∙ ⟦ x ⟧
       ≈⟨ idem ⟦ x ⟧ ⟩
         ⟦ x ⟧
       ∎

record IsAlternativeMagmaHomomorphism
         ⦃ hasBinOpA : HasBinOp A ⦄
         ⦃ hasBinOpB : HasBinOp B ⦄
         ⦃ isIdempotentMagmaB : FromHasBinOp IsAlternativeMagma hasBinOpB ⦄ : Set (a ⊔ ℓ) where
  open HasBinOp ⦃ … ⦄
  open IsAlternativeMagma ⦃ … ⦄

  instance
    _ : IsMagma {b} _≈_ _∙_
    _ = isMagma

  field
    isMagmaHomomorphism : IsMagmaHomomorphism

  open IsMagmaHomomorphism isMagmaHomomorphism public

  isAlternativeMagma-trans : IsAlternativeMagma {a} _≈_ _∙_
  isAlternativeMagma-trans =
    record
      { isMagma = isMagma-trans
      ; alter = altˡ , altʳ
      }
   where
     open import Relation.Binary.Reasoning.Setoid (setoid)
     altˡ : LeftAlternative _≈_ _∙_
     altˡ x y =
       begin
         ⟦ (x ∙ x) ∙ y ⟧
       ≈⟨ ∙-homo (x ∙ x) y ⟩
         ⟦ x ∙ x ⟧ ∙ ⟦ y ⟧
       ≈⟨ ∙-congʳ (∙-homo x x) ⟩
         (⟦ x ⟧ ∙ ⟦ x ⟧) ∙ ⟦ y ⟧
       ≈⟨ alternativeˡ ⟦ x ⟧ ⟦ y ⟧ ⟩
         ⟦ x ⟧ ∙ (⟦ x ⟧ ∙ ⟦ y ⟧)
       ≈⟨ ∙-congˡ (sym (∙-homo x  y)) ⟩
         ⟦ x ⟧ ∙ ⟦ x ∙ y ⟧
       ≈⟨ sym (∙-homo x (x ∙ y)) ⟩
         ⟦ x ∙ (x ∙ y) ⟧
       ∎

     altʳ : RightAlternative _≈_ _∙_
     altʳ x y =
       begin
         ⟦ x ∙ (y ∙ y) ⟧
       ≈⟨ ∙-homo x (y ∙ y) ⟩
         ⟦ x ⟧ ∙ ⟦ y ∙ y ⟧
       ≈⟨ ∙-congˡ (∙-homo y y) ⟩
         ⟦ x ⟧ ∙ (⟦ y ⟧ ∙ ⟦ y ⟧)
       ≈⟨ alternativeʳ ⟦ x ⟧ ⟦ y ⟧ ⟩
         (⟦ x ⟧ ∙ ⟦ y ⟧) ∙ ⟦ y ⟧
       ≈⟨ ∙-congʳ (sym (∙-homo x y)) ⟩
         ⟦ x ∙ y ⟧ ∙ ⟦ y ⟧
       ≈⟨ sym (∙-homo (x ∙ y) y) ⟩
         ⟦ (x ∙ y) ∙ y ⟧
       ∎

record IsFlexibleMagmaHomomorphism
         ⦃ hasBinOpA : HasBinOp A ⦄
         ⦃ hasBinOpB : HasBinOp B ⦄
         ⦃ isIdempotentMagmaB : FromHasBinOp IsFlexibleMagma hasBinOpB ⦄ : Set (a ⊔ ℓ) where
  open HasBinOp ⦃ … ⦄
  open IsFlexibleMagma ⦃ … ⦄

  instance
    _ : IsMagma {b} _≈_ _∙_
    _ = isMagma

  field
    isMagmaHomomorphism : IsMagmaHomomorphism

  open IsMagmaHomomorphism isMagmaHomomorphism public

  isFlexibleMagma-trans : IsFlexibleMagma {a} _≈_ _∙_
  isFlexibleMagma-trans =
    record
      { isMagma = isMagma-trans
      ; flex = flexible
      }
   where
     open import Relation.Binary.Reasoning.Setoid (setoid)
     flexible :  Flexible _≈_ _∙_
     flexible x y =
       begin
         ⟦ (x ∙ y) ∙ x ⟧
       ≈⟨ ∙-homo (x ∙ y) x ⟩
         ⟦ x ∙ y ⟧ ∙ ⟦ x ⟧
       ≈⟨ ∙-congʳ (∙-homo x y) ⟩
         (⟦ x ⟧ ∙ ⟦ y ⟧) ∙ ⟦ x ⟧
       ≈⟨ flex ⟦ x ⟧ ⟦ y ⟧ ⟩
         ⟦ x ⟧ ∙ (⟦ y ⟧ ∙ ⟦ x ⟧)
       ≈⟨ ∙-congˡ (sym (∙-homo y x)) ⟩
         ⟦ x ⟧ ∙ ⟦ y ∙ x ⟧
       ≈⟨ sym (∙-homo x (y ∙ x)) ⟩
         ⟦ x ∙ (y ∙ x) ⟧
       ∎


record IsMedialMagmaHomomorphism
         ⦃ hasBinOpA : HasBinOp A ⦄
         ⦃ hasBinOpB : HasBinOp B ⦄
         ⦃ isIdempotentMagmaB : FromHasBinOp IsMedialMagma hasBinOpB ⦄ : Set (a ⊔ ℓ) where
  open HasBinOp ⦃ … ⦄
  open IsMedialMagma ⦃ … ⦄

  instance
    _ : IsMagma {b} _≈_ _∙_
    _ = isMagma

  field
    isMagmaHomomorphism : IsMagmaHomomorphism

  open IsMagmaHomomorphism isMagmaHomomorphism public

  isMedialMagma-trans : IsMedialMagma {a} _≈_ _∙_
  isMedialMagma-trans =
    record
      { isMagma = isMagma-trans
      ; medial = ∙-medial
      }
   where
     open import Relation.Binary.Reasoning.Setoid (setoid)
     ∙-medial :  Medial _≈_ _∙_
     ∙-medial x y u z =
       begin
         ⟦ (x ∙ y) ∙ (u ∙ z) ⟧
       ≈⟨ ∙-homo (x ∙ y) (u ∙ z) ⟩
         ⟦ (x ∙ y) ⟧ ∙ (⟦ u ∙ z ⟧)
       ≈⟨ ∙-cong (∙-homo x y ) (∙-homo u z) ⟩
         (⟦ x ⟧ ∙ ⟦ y ⟧) ∙ (⟦ u ⟧ ∙ ⟦ z ⟧)
       ≈⟨ medial ⟦ x ⟧ ⟦ y ⟧ ⟦ u ⟧ ⟦ z ⟧ ⟩
         (⟦ x ⟧ ∙ ⟦ u ⟧) ∙ (⟦ y ⟧ ∙ ⟦ z ⟧)
       ≈⟨ sym (∙-cong (∙-homo x u) (∙-homo y z)) ⟩
         ⟦ x ∙ u ⟧ ∙ ⟦ y ∙ z ⟧
       ≈⟨ sym (∙-homo (x ∙ u) (y ∙ z)) ⟩
         ⟦ (x ∙ u) ∙ (y ∙ z) ⟧
       ∎

record IsSemimedialMagmaHomomorphism
         ⦃ hasBinOpA : HasBinOp A ⦄
         ⦃ hasBinOpB : HasBinOp B ⦄
         ⦃ isIdempotentMagmaB : FromHasBinOp IsSemimedialMagma hasBinOpB ⦄ : Set (a ⊔ ℓ) where
  open HasBinOp ⦃ … ⦄
  open IsSemimedialMagma ⦃ … ⦄

  instance
    _ : IsMagma {b} _≈_ _∙_
    _ = isMagma

  field
    isMagmaHomomorphism : IsMagmaHomomorphism

  open IsMagmaHomomorphism isMagmaHomomorphism public

  isSemimedialMagma-trans : IsSemimedialMagma {a} _≈_ _∙_
  isSemimedialMagma-trans =
    record
      { isMagma = isMagma-trans
      ; semiMedial = ∙-semiMedialˡ , ∙-semiMedialʳ
      }
   where
     open import Relation.Binary.Reasoning.Setoid (setoid)
     ∙-semiMedialˡ :  LeftSemimedial _≈_ _∙_
     ∙-semiMedialˡ x y z =
       begin
         ⟦ (x ∙ x) ∙ (y ∙ z) ⟧
       ≈⟨ ∙-homo (x ∙ x) (y ∙ z) ⟩
         ⟦ (x ∙ x) ⟧ ∙ (⟦ y ∙ z ⟧)
       ≈⟨ ∙-cong (∙-homo x x ) (∙-homo y z) ⟩
         (⟦ x ⟧ ∙ ⟦ x ⟧) ∙ (⟦ y ⟧ ∙ ⟦ z ⟧)
       ≈⟨ semimedialˡ ⟦ x ⟧ ⟦ y ⟧ ⟦ z ⟧ ⟩
         (⟦ x ⟧ ∙ ⟦ y ⟧) ∙ (⟦ x ⟧ ∙ ⟦ z ⟧)
       ≈⟨ sym (∙-cong (∙-homo x y) (∙-homo x z)) ⟩
         ⟦ x ∙ y ⟧ ∙ ⟦ x ∙ z ⟧
       ≈⟨ sym (∙-homo (x ∙ y) (x ∙ z)) ⟩
         ⟦ (x ∙ y) ∙ (x ∙ z) ⟧
       ∎

     ∙-semiMedialʳ :  RightSemimedial _≈_ _∙_
     ∙-semiMedialʳ x y z =
       begin
         ⟦ (y ∙ z) ∙ (x ∙ x) ⟧
       ≈⟨ ∙-homo (y ∙ z) (x ∙ x) ⟩
         ⟦ (y ∙ z) ⟧ ∙ (⟦ x ∙ x ⟧)
       ≈⟨ ∙-cong (∙-homo y z ) (∙-homo x x) ⟩
         (⟦ y ⟧ ∙ ⟦ z ⟧) ∙ (⟦ x ⟧ ∙ ⟦ x ⟧)
       ≈⟨ semimedialʳ ⟦ x ⟧ ⟦ y ⟧ ⟦ z ⟧ ⟩
         (⟦ y ⟧ ∙ ⟦ x ⟧) ∙ (⟦ z ⟧ ∙ ⟦ x ⟧)
       ≈⟨ sym (∙-cong (∙-homo y x) (∙-homo z x)) ⟩
         ⟦ y ∙ x ⟧ ∙ ⟦ z ∙ x ⟧
       ≈⟨ sym (∙-homo (y ∙ x) (z ∙ x)) ⟩
         ⟦ (y ∙ x) ∙ (z ∙ x) ⟧
       ∎

record IsSelectiveMagmaHomomorphism
         ⦃ hasBinOpA : HasBinOp A ⦄
         ⦃ hasBinOpB : HasBinOp B ⦄
         ⦃ isIdempotentMagmaB : FromHasBinOp IsSelectiveMagma hasBinOpB ⦄ : Set (a ⊔ ℓ) where
  open HasBinOp ⦃ … ⦄
  open IsSelectiveMagma ⦃ … ⦄

  instance
    _ : IsMagma {b} _≈_ _∙_
    _ = isMagma

  field
    isMagmaHomomorphism : IsMagmaHomomorphism

  open import Data.Sum

  open IsMagmaHomomorphism isMagmaHomomorphism public

  isSelectiveMagma-trans : IsSelectiveMagma {a} _≈_ _∙_
  isSelectiveMagma-trans =
    record
      { isMagma = isMagma-trans
      ; sel     = selective
      }
   where
     open import Relation.Binary.Reasoning.Setoid (setoid)
     selective : Selective _≈_ _∙_
     selective x y with sel ⟦ x ⟧ ⟦ y ⟧
     ... | inj₁ ⟦x⟧∙⟦y⟧≈⟦x⟧ = inj₁ (
            begin
              ⟦ x ∙ y ⟧
            ≈⟨ ∙-homo x y ⟩
              ⟦ x ⟧ ∙ ⟦ y ⟧
            ≈⟨ ⟦x⟧∙⟦y⟧≈⟦x⟧ ⟩
             ⟦ x ⟧
            ∎)
     ... | inj₂ ⟦x⟧∙⟦y⟧≈⟦y⟧ = inj₂ (
            begin
              ⟦ x ∙ y ⟧
            ≈⟨ ∙-homo x y ⟩
              ⟦ x ⟧ ∙ ⟦ y ⟧
            ≈⟨ ⟦x⟧∙⟦y⟧≈⟦y⟧ ⟩
             ⟦ y ⟧
            ∎)

record IsSemigroupHomomorphism
         ⦃ hasBinOpA : HasBinOp A ⦄
         ⦃ hasBinOpB : HasBinOp B ⦄
         ⦃ isSemigroupB : FromHasBinOp IsSemigroup hasBinOpB ⦄ : Set (a ⊔ ℓ) where

  open HasBinOp ⦃ … ⦄
  open IsSemigroup ⦃ … ⦄ -- brings into scope 'isMagma' and 'assoc'

  instance
    _ : IsMagma {b} _≈_ _∙_
    _ = isMagma

  field
    isMagmaHomomorphism : IsMagmaHomomorphism

  -- brings record fields '∙-homo' and 'isMagma-trans' into
  -- scope and re-exports them
  open IsMagmaHomomorphism isMagmaHomomorphism public

  isSemigroup-trans : IsSemigroup {a} _≈_ _∙_
  isSemigroup-trans =
    record
      { isMagma = isMagma-trans
      ; assoc = ∙-assoc
      }
    where
      open import Relation.Binary.Reasoning.Setoid (setoid)

      ∙-assoc : Associative _≈_ _∙_
      ∙-assoc x y z =
        begin
          ⟦ (x ∙ y) ∙ z ⟧
        ≈⟨ ∙-homo (x ∙ y) z ⟩
          ⟦ x ∙ y ⟧ ∙ ⟦ z ⟧
        ≈⟨ ∙-congʳ (∙-homo x y) ⟩
          (⟦ x ⟧ ∙ ⟦ y ⟧) ∙ ⟦ z ⟧
        ≈⟨ assoc ⟦ x ⟧ ⟦ y ⟧ ⟦ z ⟧ ⟩
          ⟦ x ⟧ ∙ (⟦ y ⟧ ∙ ⟦ z ⟧)
        ≈⟨ sym  (∙-congˡ (∙-homo y z)) ⟩
          ⟦ x ⟧ ∙ ⟦ y ∙ z ⟧
        ≈⟨ sym (∙-homo x (y ∙ z)) ⟩
          ⟦ x ∙ (y ∙ z) ⟧
        ∎

record IsBandHomomorphism
         ⦃ hasBinOpA : HasBinOp A ⦄
         ⦃ hasBinOpB : HasBinOp B ⦄
         ⦃ isBandB : FromHasBinOp IsBand hasBinOpB ⦄ : Set (a ⊔ ℓ) where

  open HasBinOp ⦃ … ⦄
  open IsBand ⦃ … ⦄

  instance
    _ : IsSemigroup {b} _≈_ _∙_
    _ = isSemigroup

  field
    isSemigroupHomomorphism : IsSemigroupHomomorphism

  -- brings record fields '∙-homo' and 'isMagma-trans' into
  -- scope and re-exports them
  open IsSemigroupHomomorphism isSemigroupHomomorphism public

  isBand-trans : IsBand {a} _≈_ _∙_
  isBand-trans =
    record
      { isSemigroup = isSemigroup-trans
      ; idem = ∙-idem
      }
    where
      open import Relation.Binary.Reasoning.Setoid (setoid)

      ∙-idem : Idempotent _≈_ _∙_
      ∙-idem x =
        begin
          ⟦ x ∙ x ⟧
        ≈⟨ ∙-homo x x ⟩
          ⟦ x ⟧ ∙ ⟦ x ⟧
        ≈⟨ idem ⟦ x ⟧ ⟩
          ⟦ x ⟧
        ∎

record IsCommutativeSemigroupHomomorphism
         ⦃ hasBinOpA : HasBinOp A ⦄
         ⦃ hasBinOpB : HasBinOp B ⦄
         ⦃ isCommutativeSemigroupB : FromHasBinOp IsCommutativeSemigroup hasBinOpB ⦄ : Set (a ⊔ ℓ) where

  open HasBinOp ⦃ … ⦄
  open IsCommutativeSemigroup ⦃ … ⦄

  instance
    _ : IsSemigroup {b} _≈_ _∙_
    _ = isSemigroup

  field
    isSemigroupHomomorphism : IsSemigroupHomomorphism

  -- brings record fields '∙-homo' and 'isMagma-trans' into
  -- scope and re-exports them
  open IsSemigroupHomomorphism isSemigroupHomomorphism public


  ∙-comm : Commutative _≈_ _∙_
  ∙-comm x y =
    begin
      ⟦ x ∙ y ⟧
    ≈⟨ ∙-homo x y ⟩
      ⟦ x ⟧ ∙ ⟦ y ⟧
    ≈⟨ comm ⟦ x ⟧ ⟦ y ⟧ ⟩
      ⟦ y ⟧ ∙ ⟦ x ⟧
    ≈⟨ sym (∙-homo y x) ⟩
      ⟦ y ∙ x ⟧
    ∎
    where
      open import Relation.Binary.Reasoning.Setoid (setoid)

  isCommutativeSemigroup-trans : IsCommutativeSemigroup {a} _≈_ _∙_
  isCommutativeSemigroup-trans =
    record
      { isSemigroup = isSemigroup-trans
      ; comm = ∙-comm
      }

  isCommutativeMagma-trans : IsCommutativeMagma {a} _≈_ _∙_
  isCommutativeMagma-trans =
    record
      { isMagma = isMagma-trans
      ; comm = ∙-comm
      }

------------------------------------------------------------------------
-- Structures with 1 binary operation & 1 element
------------------------------------------------------------------------

record IsUnitalMagmaHomomorphism
         ⦃ hasMonoidOpsA : HasMonoidOps A ⦄
         ⦃ hasMonoidOpsB : HasMonoidOps B ⦄
         ⦃ isUnitalMagmaB : FromMonoidOps IsUnitalMagma hasMonoidOpsB ⦄ : Set (a ⊔ ℓ) where

  open HasMonoidOps ⦃ … ⦄
  open IsUnitalMagma ⦃ … ⦄

  instance
    _ : IsMagma {b} _≈_ _∙_
    _ = isMagma

  field
    isMagmaHomomorphism : IsMagmaHomomorphism
    ε-homo : ⟦ ε ⟧ ≈ ε

  -- Bring record fields into scope and re-export them
  open IsMagmaHomomorphism isMagmaHomomorphism public

  isUnitalMagma-trans : IsUnitalMagma {a} _≈_ _∙_ ε
  isUnitalMagma-trans =
    record
      { isMagma = isMagma-trans
      ; identity = ∙-identityˡ , ∙-identityʳ
      }
    where
      open import Relation.Binary.Reasoning.Setoid (setoid)
      ∙-identityˡ : LeftIdentity _≈_ ε _∙_
      ∙-identityˡ x =
        begin
          ⟦ ε ∙ x ⟧
        ≈⟨ ∙-homo ε x  ⟩
          ⟦ ε ⟧ ∙ ⟦ x ⟧
        ≈⟨ ∙-congʳ ε-homo ⟩
          ε ∙ ⟦ x ⟧
        ≈⟨ identityˡ ⟦ x ⟧ ⟩
          ⟦ x ⟧
        ∎

      ∙-identityʳ : RightIdentity _≈_ ε _∙_
      ∙-identityʳ x =
        begin
          ⟦ x ∙ ε ⟧
        ≈⟨ ∙-homo x ε ⟩
          ⟦ x ⟧ ∙ ⟦ ε ⟧
        ≈⟨ ∙-congˡ ε-homo ⟩
          ⟦ x ⟧ ∙ ε
        ≈⟨ identityʳ ⟦ x ⟧ ⟩
          ⟦ x ⟧
        ∎

record IsMonoidHomomorphism
         ⦃ hasMonoidOpsA : HasMonoidOps A ⦄
         ⦃ hasMonoidOpsB : HasMonoidOps B ⦄
         ⦃ isMonoidB : FromMonoidOps IsMonoid hasMonoidOpsB ⦄ : Set (a ⊔ ℓ) where

  open HasMonoidOps ⦃ … ⦄
  open IsMonoid ⦃ … ⦄

  instance
    _ : IsSemigroup {b} _≈_ _∙_
    _ = isSemigroup

  field
    isSemigroupHomomorphism : IsSemigroupHomomorphism
    ε-homo : ⟦ ε ⟧ ≈ ε

  -- Bring record fields into scope and re-export them
  open IsSemigroupHomomorphism isSemigroupHomomorphism public

  open import Relation.Binary.Reasoning.Setoid (setoid)

  ∙-identityˡ : LeftIdentity _≈_ ε _∙_
  ∙-identityˡ x =
    begin
      ⟦ ε ∙ x ⟧
    ≈⟨ ∙-homo ε x  ⟩
      ⟦ ε ⟧ ∙ ⟦ x ⟧
    ≈⟨ ∙-congʳ ε-homo ⟩
      ε ∙ ⟦ x ⟧
    ≈⟨ identityˡ ⟦ x ⟧ ⟩
      ⟦ x ⟧
    ∎

  ∙-identityʳ : RightIdentity _≈_ ε _∙_
  ∙-identityʳ x =
    begin
      ⟦ x ∙ ε ⟧
    ≈⟨ ∙-homo x ε ⟩
      ⟦ x ⟧ ∙ ⟦ ε ⟧
    ≈⟨ ∙-congˡ ε-homo ⟩
      ⟦ x ⟧ ∙ ε
    ≈⟨ identityʳ ⟦ x ⟧ ⟩
      ⟦ x ⟧
    ∎

  isMonoid-trans : IsMonoid {a} _≈_ _∙_ ε
  isMonoid-trans =
    record
      { isSemigroup = isSemigroup-trans
      ; identity = ∙-identityˡ , ∙-identityʳ
      }

  isUnitalMagma-trans : IsUnitalMagma {a} _≈_ _∙_ ε
  isUnitalMagma-trans =
    record
      { isMagma = isMagma-trans
      ; identity = ∙-identityˡ , ∙-identityʳ
      }

record IsCommutativeMonoidHomomorphism
         ⦃ hasMonoidOpsA : HasMonoidOps A ⦄
         ⦃ hasMonoidOpsB : HasMonoidOps B ⦄
         ⦃ isMonoidB : FromMonoidOps IsCommutativeMonoid hasMonoidOpsB ⦄ : Set (a ⊔ ℓ) where

  open HasMonoidOps ⦃ … ⦄
  open IsCommutativeMonoid ⦃ … ⦄

  instance
    _ : IsMonoid {b} _≈_ _∙_ ε
    _ = isMonoid

  field
    isMonoidHomomorphism : IsMonoidHomomorphism

  -- Bring record fields into scope and re-export them
  open IsMonoidHomomorphism isMonoidHomomorphism public

  ∙-comm : Commutative _≈_ _∙_
  ∙-comm x y =
    begin
      ⟦ x ∙ y ⟧
    ≈⟨ ∙-homo x y ⟩
      ⟦ x ⟧ ∙ ⟦ y ⟧
    ≈⟨ comm ⟦ x ⟧ ⟦ y ⟧ ⟩
      ⟦ y ⟧ ∙ ⟦ x ⟧
    ≈⟨ sym (∙-homo y x) ⟩
      ⟦ y ∙ x ⟧
    ∎
    where
      open import Relation.Binary.Reasoning.Setoid (setoid)

  isCommutativeMonoid-trans : IsCommutativeMonoid {a} _≈_ _∙_ ε
  isCommutativeMonoid-trans =
    record
      { isMonoid = isMonoid-trans
      ; comm = ∙-comm
      }

  isCommutativeSemigroup-trans : IsCommutativeSemigroup {a} _≈_ _∙_
  isCommutativeSemigroup-trans =
    record
      { isSemigroup = isSemigroup-trans
      ; comm = ∙-comm
      }

record IsIdempotentCommutativeMonoidHomomorphism
         ⦃ hasMonoidOpsA : HasMonoidOps A ⦄
         ⦃ hasMonoidOpsB : HasMonoidOps B ⦄
         ⦃ isIdempotentCommutativeMonoidB : FromMonoidOps IsIdempotentCommutativeMonoid hasMonoidOpsB ⦄ : Set (a ⊔ ℓ) where

  open HasMonoidOps ⦃ … ⦄
  open IsIdempotentCommutativeMonoid ⦃ … ⦄

  instance
    _ : IsCommutativeMonoid {b} _≈_ _∙_ ε
    _ = isCommutativeMonoid

  field
    isCommutativeMonoidHomomorphism : IsCommutativeMonoidHomomorphism

  open IsCommutativeMonoidHomomorphism isCommutativeMonoidHomomorphism public

  ∙-idem : Idempotent {a} _≈_ _∙_
  ∙-idem x =
    begin
      ⟦ x ∙ x ⟧
    ≈⟨ ∙-homo x x ⟩
      ⟦ x ⟧ ∙ ⟦ x ⟧
    ≈⟨ idem ⟦ x ⟧ ⟩
      ⟦ x ⟧
    ∎
    where open import Relation.Binary.Reasoning.Setoid (setoid)

  isIdempotentCommutativeMonoid-trans : IsIdempotentCommutativeMonoid {a} _≈_ _∙_ ε
  isIdempotentCommutativeMonoid-trans =
    record
      { isCommutativeMonoid = isCommutativeMonoid-trans
      ; idem = ∙-idem
      }

------------------------------------------------------------------------
-- Structures with 1 binary operation, 1 unary operation & 1 element
------------------------------------------------------------------------

record IsInvertibleMagmaHomomorphism : Set (a ⊔ ℓ) where
  -- FIXME: Not done

record IsInvertibleUnitalMagmaHomomorphism : Set (a ⊔ ℓ) where
  -- FIXME: Not done

record IsGroupHomomorphism
         ⦃ hasGroupOpsA : HasGroupOps A ⦄
         ⦃ hasGroupOpsB : HasGroupOps B ⦄
         ⦃ isGroupB : FromGroupOps IsGroup hasGroupOpsB ⦄ : Set (a ⊔ ℓ) where

  open HasGroupOps ⦃ … ⦄
  open IsGroup ⦃ … ⦄

  instance
    _ : IsMonoid {b} _≈_ _∙_ ε
    _ = isMonoid

  field
    isMonoidHomomorphism : IsMonoidHomomorphism
    ⁻¹-homo : ∀ x → ⟦ x ⁻¹ ⟧ ≈ ⟦ x ⟧ ⁻¹

  open IsMonoidHomomorphism isMonoidHomomorphism public

  isGroup-trans : IsGroup {a} _≈_ _∙_ ε _⁻¹
  isGroup-trans =
    record
      { isMonoid = isMonoid-trans
      ; inverse = invˡ , invʳ
      ; ⁻¹-cong = ⁻¹-congruent
      }
    where
      open import Relation.Binary.Reasoning.Setoid (setoid)

      invˡ : LeftInverse {a} _≈_ ε _⁻¹ _∙_
      invˡ x =
        begin
            ⟦ (x ⁻¹) ∙ x ⟧
          ≈⟨ ∙-homo (x ⁻¹)  x   ⟩
           ⟦ x ⁻¹ ⟧ ∙ ⟦ x ⟧
          ≈⟨ ∙-cong (⁻¹-homo  x) refl ⟩
            (⟦ x ⟧ ⁻¹) ∙ ⟦ x ⟧
          ≈⟨ inverseˡ ⟦ x ⟧ ⟩
             ε
          ≈⟨  sym ε-homo ⟩
            ⟦ ε ⟧
          ∎

      invʳ : RightInverse {a} _≈_ ε _⁻¹ _∙_
      invʳ x =
        begin
            ⟦ x ∙ (x ⁻¹) ⟧
          ≈⟨ ∙-homo x (x ⁻¹)    ⟩
           ⟦ x ⟧ ∙ ⟦ x ⁻¹ ⟧
          ≈⟨ ∙-cong refl (⁻¹-homo x)  ⟩
            ⟦ x ⟧ ∙ (⟦ x ⟧ ⁻¹)
          ≈⟨ inverseʳ ⟦ x ⟧ ⟩
             ε
          ≈⟨  sym ε-homo ⟩
            ⟦ ε ⟧
          ∎

      ⁻¹-congruent : Congruent₁ {a} _≈_ _⁻¹
      ⁻¹-congruent {x} {u} ⟦x⟧≈⟦u⟧ =
        begin
          ⟦ x ⁻¹ ⟧
        ≈⟨ ⁻¹-homo x ⟩
          ⟦ x ⟧ ⁻¹
        ≈⟨ ⁻¹-cong ⟦x⟧≈⟦u⟧ ⟩
          ⟦ u ⟧ ⁻¹
        ≈⟨ sym (⁻¹-homo u) ⟩
          ⟦ u ⁻¹ ⟧
        ∎

record IsAbelianGroupHomomorphism
         ⦃ hasGroupOpsA : HasGroupOps A ⦄
         ⦃ hasGroupOpsB : HasGroupOps B ⦄
         ⦃ isAbelianGroupB : FromGroupOps IsAbelianGroup hasGroupOpsB ⦄ : Set (a ⊔ ℓ) where

  open HasGroupOps ⦃ … ⦄
  open IsAbelianGroup ⦃ … ⦄

  instance
    _ : IsGroup {b} _≈_ _∙_ ε _⁻¹
    _ = isGroup

  field
    isgroupHomomorphism : IsGroupHomomorphism

  open IsGroupHomomorphism isgroupHomomorphism public

  isAbelianGroup-trans : IsAbelianGroup _≈_ _∙_ ε _⁻¹
  isAbelianGroup-trans =
    record
      { isGroup = isGroup-trans
      ; comm    = ∙-comm
      }
    where
      open import Relation.Binary.Reasoning.Setoid (setoid)

      ∙-comm : Commutative {a} _≈_ _∙_
      ∙-comm x y =
        begin
          ⟦ x ∙ y ⟧
        ≈⟨ ∙-homo x y ⟩
          ⟦ x ⟧ ∙ ⟦ y ⟧
        ≈⟨ comm ⟦ x ⟧ ⟦ y ⟧ ⟩
          ⟦ y ⟧ ∙ ⟦ x ⟧
        ≈⟨ sym (∙-homo y x ) ⟩
          ⟦ y ∙ x ⟧
        ∎

------------------------------------------------------------------------
-- Structures with 2 binary operations & 1 element
------------------------------------------------------------------------

record IsSemiringWithoutAnnihilatingZeroHomomorphism : Set (a ⊔ ℓ) where
  -- FIXME: Not done

record IsSemiringHomomorphism : Set (a ⊔ ℓ) where
  -- FIXME: Not done

record IsCommutativeSemiringHomomorphism : Set (a ⊔ ℓ) where
  -- FIXME: Not done

record IsCancellativeCommutativeSemiringHomomorphism : Set (a ⊔ ℓ) where
  -- FIXME: Not done

record IsIdempotentSemiringHomomorphism : Set (a ⊔ ℓ) where
  -- FIXME: Not done

record IsKleeneAlgebraHomomorphism : Set (a ⊔ ℓ) where
  -- FIXME: Not done

record IsQuasiringHomomorphism : Set (a ⊔ ℓ) where
  -- FIXME: Not done

------------------------------------------------------------------------
-- Structures with 2 binary operations, 1 unary operation & 1 element
------------------------------------------------------------------------

record IsRingWithoutOneHomomorphism : Set (a ⊔ ℓ) where
  -- FIXME: Not done yet

------------------------------------------------------------------------
-- Structures with 2 binary operations, 1 unary operation & 2 elements
------------------------------------------------------------------------

record IsNonAssociativeRingHomomorphism
         ⦃ hasRingOpsA : HasRingOps A ⦄
         ⦃ hasRingOpsB : HasRingOps B ⦄
         ⦃ isRingB : FromRingOps IsRing hasRingOpsB ⦄ : Set (a ⊔ ℓ) where
  -- FIXME: Not done yet

record IsRingHomomorphism
         ⦃ hasRingOpsA : HasRingOps A ⦄
         ⦃ hasRingOpsB : HasRingOps B ⦄
         ⦃ isRingB : FromRingOps IsRing hasRingOpsB ⦄ : Set (a ⊔ ℓ) where
  open HasRingOps ⦃ … ⦄
  open IsRing ⦃ … ⦄

  instance
    _ : IsAbelianGroup {b} _≈_ _+_ 0# (-_)
    _ = +-isAbelianGroup
    _ : IsMonoid {b} _≈_ _*_ 1#
    _ = *-isMonoid

  field
    +-abelianIsGroupHomomorphism : IsAbelianGroupHomomorphism
    *-isMonoidHomomorphism : IsMonoidHomomorphism

  open IsAbelianGroupHomomorphism +-abelianIsGroupHomomorphism public
    renaming
    ( ∙-homo                   to +-homo
    ; ε-homo                   to 0#-homo
    ; ⁻¹-homo                  to [-]-homo -- TODO: Come up with a new name
    ; isMagmaHomomorphism      to +-isMagmaHomomorphism
    ; isSemigroupHomomorphism  to +-isSemigroupHomomorphism
    ; isMonoidHomomorphism     to +-isMonoidHomomorphism
    ; isMagma-trans            to +-isMagma-trans
    ; isSemigroup-trans        to +-isSemigroup-trans
    ; isMonoid-trans           to +-isMonoid-trans
    ; isGroup-trans            to +-isGroup-trans
    ; isAbelianGroup-trans     to +-isAbelianGroup-trans
    )
  open IsMonoidHomomorphism *-isMonoidHomomorphism public
    using ()
    renaming
    ( ∙-homo                   to *-homo
    ; ε-homo                   to 1#-homo
    ; isMagmaHomomorphism      to *-isMagmaHomomorphism
    ; isSemigroupHomomorphism  to *-isSemigroupHomomorphism
    ; isMagma-trans            to *-isMagma-trans
    ; isSemigroup-trans        to *-isSemigroup-trans
    ; isMonoid-trans           to *-isMonoid-trans
    )

  open IsMonoid *-isMonoid-trans -- not public
    using ()
    renaming
    ( ∙-cong                   to *-cong′
    ; assoc                    to *-assoc′
    ; identity                 to *-identity′
    )

  isRing-trans : FromRingOps IsRing hasRingOpsA
  isRing-trans =
    record
      { +-isAbelianGroup = +-isAbelianGroup-trans
      ; *-cong           = *-cong′
      ; *-assoc          = *-assoc′
      ; *-identity       = *-identity′
      ; distrib          = distributionˡ , distributionʳ
      ; zero             = zˡ , zʳ
      }
    where
      open import Relation.Binary.Reasoning.Setoid (setoid)


      isMonoid : IsMonoid _≈_ _*_ 1#
      isMonoid = *-isMonoid-trans

      distributionˡ : ∀ x y z → x * (y + z) ≈ x * y + x * z
      distributionˡ x y z =
        begin
            ⟦ x * (y + z) ⟧
          ≈⟨ *-homo x (y + z) ⟩
            ⟦ x ⟧ * ⟦ y + z ⟧
          ≈⟨ *-cong refl (+-homo y z) ⟩
            ⟦ x ⟧ * (⟦ y ⟧ + ⟦ z ⟧)
          ≈⟨  distribˡ  ⟦ x ⟧ ⟦ y ⟧ ⟦ z ⟧ ⟩
            ⟦ x ⟧ * ⟦ y ⟧ + ⟦ x ⟧ * ⟦ z ⟧
          ≈⟨ +-cong (sym (*-homo x y)) (sym (*-homo x z )) ⟩
            ⟦ x * y ⟧ + ⟦ x * z ⟧
          ≈⟨ sym (+-homo (x * y) (x * z)) ⟩
            ⟦ x * y + x * z ⟧
        ∎

      distributionʳ : ∀ x y z → (y + z) * x ≈ y * x + z * x
      distributionʳ x y z =
        begin
            ⟦ (y + z) * x ⟧
          ≈⟨ *-homo (y + z) x ⟩
            ⟦ y + z ⟧ * ⟦ x ⟧
          ≈⟨ *-cong (+-homo y z) refl ⟩
            (⟦ y ⟧ + ⟦ z ⟧) * ⟦ x ⟧
          ≈⟨  distribʳ  ⟦ x ⟧ ⟦ y ⟧ ⟦ z ⟧ ⟩
            ⟦ y ⟧ * ⟦ x ⟧ + ⟦ z ⟧ * ⟦ x ⟧
          ≈⟨ +-cong (sym (*-homo y x)) (sym (*-homo z x )) ⟩
            ⟦ y * x ⟧ + ⟦ z * x ⟧
          ≈⟨ sym (+-homo (y * x) (z * x)) ⟩
            ⟦ y * x + z * x ⟧
        ∎

      zˡ : ∀ x → 0# * x ≈ 0#
      zˡ x =
        begin
          ⟦ 0# * x ⟧
        ≈⟨ *-homo 0# x ⟩
          ⟦ 0# ⟧ * ⟦ x ⟧
        ≈⟨ *-cong 0#-homo refl ⟩
           0# * ⟦ x ⟧
        ≈⟨ zeroˡ ⟦ x ⟧ ⟩
           0#
        ≈⟨ sym 0#-homo ⟩
          ⟦ 0# ⟧
        ∎

      zʳ : ∀ x → x * 0# ≈ 0#
      zʳ x =
        begin
          ⟦ x * 0# ⟧
        ≈⟨ *-homo x 0# ⟩
          ⟦ x ⟧ * ⟦ 0# ⟧
        ≈⟨ *-cong refl 0#-homo ⟩
           ⟦ x ⟧ * 0#
        ≈⟨ zeroʳ ⟦ x ⟧ ⟩
           0#
        ≈⟨ sym 0#-homo ⟩
          ⟦ 0# ⟧
        ∎

record IsCommutativeRingHomomorphism
         ⦃ hasRingOpsA : HasRingOps A ⦄
         ⦃ hasRingOpsB : HasRingOps B ⦄
         ⦃ isRingB : FromRingOps IsRing hasRingOpsB ⦄ : Set (a ⊔ ℓ) where
  -- FIXME: Not done yet

------------------------------------------------------------------------
-- Structures with 3 binary operations
------------------------------------------------------------------------

record IsQuasigroupHomomorphism : Set (a ⊔ ℓ) where
  -- FIXME: Not done yet
