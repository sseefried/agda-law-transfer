module ParityExample where

open import Level using (0ℓ)
open import Function.Base using (id)
open import Data.Bool
open import Data.Bool.Properties using (∨-∧-booleanAlgebra)
-- open import Algebra.Bundles; open BooleanAlgebra hiding (refl)
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality; open ≡-Reasoning
open import Algebra.Properties.BooleanAlgebra ∨-∧-booleanAlgebra
open import Algebra.Structures

xor-def : ∀ x y → x xor y ≡ (x ∨ y) ∧ not (x ∧ y)
xor-def false false = refl
xor-def false true  = refl
xor-def true  false = refl
xor-def true  true  = refl

open XorRing _xor_ xor-def using (⊕-∧-isRing)

-- Tells us whether the number is odd or even
⟦_⟧ : ℕ → Bool
⟦ zero ⟧ = false
⟦ suc n ⟧ = not ⟦ n ⟧

false′ : ℕ
false′ = zero

true′ : ℕ
true′ = suc zero

⟦false′⟧ : ⟦ false′ ⟧ ≡ false
⟦false′⟧ = refl

⟦true′⟧ : ⟦ true′ ⟧ ≡ true
⟦true′⟧ = refl

not′ : ℕ → ℕ
not′ = suc

⟦not′⟧ : ∀ x → ⟦ not′ x ⟧ ≡ not ⟦ x ⟧
⟦not′⟧ zero = refl
⟦not′⟧ (suc _) = refl

⟦id′⟧ : ∀ x → ⟦ id x ⟧ ≡ id ⟦ x ⟧
⟦id′⟧ zero    = refl
⟦id′⟧ (suc _) = refl

_xor′_ : ℕ → ℕ → ℕ
x xor′ y = x + y

_⟦xor′⟧_ : ∀ x y → ⟦ x xor′ y ⟧ ≡ ⟦ x ⟧ xor ⟦ y ⟧
zero  ⟦xor′⟧ b = refl
suc n ⟦xor′⟧ b = begin
  ⟦ suc n xor′ b ⟧      ≡⟨⟩
  ⟦ suc n + b ⟧         ≡⟨⟩
  ⟦ suc (n + b) ⟧       ≡⟨⟩
  ⟦ suc (n xor′ b) ⟧    ≡⟨⟩
  ⟦ not′ (n xor′ b) ⟧   ≡⟨⟩
  not ⟦ n xor′ b ⟧      ≡⟨ cong not (n ⟦xor′⟧ b)⟩
  not (⟦ n ⟧ xor ⟦ b ⟧) ≡⟨ not-xor-1 ⟦ n ⟧ ⟦ b ⟧ ⟩
  (not ⟦ n ⟧) xor ⟦ b ⟧ ≡⟨⟩
  ⟦ suc n ⟧ xor ⟦ b ⟧
  ∎
  where
    not-xor-1 : ∀ x y → not (x xor y) ≡ not x xor y
    not-xor-1 false _    = refl
    not-xor-1 true true  = refl
    not-xor-1 true false = refl

_∧′_ : ℕ → ℕ → ℕ
x ∧′ y = x * y

_⟦∧′⟧_ : ∀ x y → ⟦ x ∧′ y ⟧ ≡ ⟦ x ⟧ ∧ ⟦ y ⟧
zero ⟦∧′⟧ _ = refl
suc n ⟦∧′⟧ b = begin
    ⟦ suc n ∧′ b ⟧
  ≡⟨⟩
    ⟦ suc n * b ⟧
  ≡⟨⟩
    ⟦ b + (n * b) ⟧
  ≡⟨⟩
    ⟦ b xor′ (n ∧′ b) ⟧
  ≡⟨ b ⟦xor′⟧ (n ∧′ b) ⟩
    ⟦ b ⟧ xor ⟦ n ∧′ b ⟧
  ≡⟨ cong (λ x → ⟦ b ⟧ xor x) (n ⟦∧′⟧ b) ⟩
    ⟦ b ⟧ xor (⟦ n ⟧ ∧ ⟦ b ⟧)
  ≡⟨ xor-∧-1 ⟦ n ⟧ ⟦ b ⟧ ⟩
   not ⟦ n ⟧ ∧ ⟦ b ⟧
  ≡⟨⟩
    ⟦ suc n ⟧ ∧ ⟦ b ⟧
  ∎
  where
    xor-∧-1 : ∀ x y → y xor (x ∧ y) ≡ not x ∧ y
    xor-∧-1 false false = refl
    xor-∧-1 false true  = refl
    xor-∧-1 true  false = refl
    xor-∧-1 true  true  = refl

--
-- Now for a use of LawTransfer
--

open import LawTransfer ⟦_⟧ _≡_

instance
  hasRingOpsℕ : HasRingOps ℕ
  hasRingOpsℕ = record { _+_ = _xor′_ ; _*_ = _∧′_ ; -_ = id; 0# = false′ ; 1# = true′ }
  hasRingOpsBool : HasRingOps Bool
  hasRingOpsBool = record { _+_ = _xor_ ; _*_ = _∧_ ; -_ = id; 0# = false ; 1# = true }
  _ : IsRing _≡_ _xor_ _∧_ id false true
  _ = ⊕-∧-isRing

ringLawTransfer : RingLawTransfer
ringLawTransfer =
  record
    { +-abelianGroupLawTransfer =
        record
          { groupLawTransfer =
              record
                 { monoidLawTransfer =
                     record
                       { semigroupLawTransfer =
                           record
                             { magmaLawTransfer = record { ∙-homo = _⟦xor′⟧_ } }

                       ; ε-homo = ⟦false′⟧
                       }
                 ; ⁻¹-homo = ⟦id′⟧
                 }
          }
    ; *-monoidLawTransfer =
          record
             { semigroupLawTransfer =
                  record
                    { magmaLawTransfer = record { ∙-homo = _⟦∧′⟧_ } }
             ; ε-homo = ⟦true′⟧
             }
    }


_≈ₛ_ : ℕ → ℕ → Set
a ≈ₛ b = ⟦ a ⟧ ≡ ⟦ b ⟧

parityIsRing : IsRing _≈ₛ_ _xor′_ _∧′_ id false′ true′
parityIsRing = RingLawTransfer.isRing-trans ringLawTransfer
