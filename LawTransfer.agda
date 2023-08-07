{-# OPTIONS --without-K --safe #-}

module LawTransfer
  {a b ℓ} {A : Set a} {B : Set b}
  where

open import Data.Product using (_,_)
open import Level using (Level ; _⊔_ ; suc)
open import Relation.Binary.Core using (Rel)

open import Algebra.Core using (Op₁ ; Op₂)

record Equiv {a} (A : Set a) : Set (a ⊔ suc ℓ) where
  infixr 20 _≈_
  field
    _≈_ : Rel A ℓ

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

record HasMonoidOps {a} (A : Set a) : Set a where
  field
    hasBinOp    : HasBinOp A
    hasIdentity : HasIdentity A
  open HasBinOp    hasBinOp    public
  open HasIdentity hasIdentity public

  instance -- methods must be named to be re-exported
    hasBinOpFromMonoid : HasBinOp A
    hasBinOpFromMonoid = hasBinOp

    hasIdentityFromMonoid : HasIdentity A
    hasIdentityFromMonoid = hasIdentity

record HasGroupOps {a} (A : Set a) : Set a where
  field
    hasMonoidOps : HasMonoidOps A
    hasInverse  : HasInverse A
  open HasMonoidOps hasMonoidOps public
  open HasInverse   hasInverse   public

  instance -- methods must be named to be re-exported
    hasMonoidOpsFromGroup : HasMonoidOps A
    hasMonoidOpsFromGroup = hasMonoidOps

    hasInverseFromGroup : HasInverse A
    hasInverseFromGroup = hasInverse

record HasRingOps {a} (A : Set a) : Set a where
  infixr 26 _+_
  infixr 27 _*_
  field
    _+_ : A → A → A
    _*_ : A → A → A
    -_ : A → A
    0# : A
    1# : A

  hasMonoidOps : HasMonoidOps A
  hasMonoidOps = record
          { hasBinOp    = record { _∙_ = _*_ }
          ; hasIdentity = record { ε = 1# }
          }
  hasGroupOps : HasGroupOps A
  hasGroupOps =
    record
      { hasMonoidOps =
          record
            { hasBinOp    = record { _∙_ = _+_ }
            ; hasIdentity = record { ε = 0# }
            }
      ; hasInverse = record { _⁻¹ = -_ }
      }
  instance
    hasMonoidOpsFromRing : HasMonoidOps A
    hasMonoidOpsFromRing = hasMonoidOps
    hasGroupOpsFromRing : HasGroupOps A
    hasGroupOpsFromRing = hasGroupOps

module LawTransfers (⟦_⟧ : A → B) (_≈′_ : Rel B ℓ) where
  open import Algebra.Definitions
  open import Algebra.Structures
  open Equiv        ⦃ … ⦄ public

  instance
    _ : Equiv B
    _ = record { _≈_ = _≈′_ }
    _ : Equiv A
    _ = record { _≈_ = _≈ₛ_ }
          where
            _≈ₛ_  : Rel A ℓ
            x ≈ₛ y = ⟦ x ⟧ ≈ ⟦ y ⟧

  --
  -- Helper functions
  --

  IsStructureFromHasBinOp : {x : _} {X : Set x} → ⦃ Equiv X ⦄
                          → (Rel X _ → Op₂ X → Set (x ⊔ ℓ)) → HasBinOp X → Set _
  IsStructureFromHasBinOp {x} f o = f _≈_ _∙_
    where open HasBinOp o

  IsMagmaFromOps : {x : _} {X : Set x} → ⦃ Equiv X ⦄ → HasBinOp X → Set _
  IsMagmaFromOps {x} = IsStructureFromHasBinOp IsMagma

  IsSemigroupFromOps : {x : _} {X : Set x} → ⦃ Equiv X ⦄ → HasBinOp X → Set _
  IsSemigroupFromOps {x} = IsStructureFromHasBinOp IsSemigroup

  IsMonoidFromOps : {x : _} {X : Set x} → ⦃ Equiv X ⦄
                   → HasMonoidOps X → Set _
  IsMonoidFromOps {x}  o = IsMonoid {x}  _≈_ _∙_ ε
    where open HasMonoidOps o

  IsRingFromOps : {x : Level} {X : Set x} → ⦃ Equiv X ⦄ → HasRingOps X → Set _
  IsRingFromOps {x} o = IsRing {x} _≈_ _+_ _*_ -_ 0#  1#
    where open HasRingOps o

  IsGroupFromOps : {a : Level} {A : Set a} → ⦃ Equiv A ⦄ → HasGroupOps A → Set _
  IsGroupFromOps {a} o = IsGroup {a} _≈_ _∙_ ε _⁻¹
    where
      open HasGroupOps o

  IsAbelianGroupFromOps : {a : Level} {A : Set a} → ⦃ Equiv A ⦄ → HasGroupOps A → Set _
  IsAbelianGroupFromOps {a} o = IsAbelianGroup {a} _≈_ _∙_ ε _⁻¹
    where
      open HasGroupOps o

  record MagmaLawTransfer
           ⦃ hasBinOpA : HasBinOp A ⦄
           ⦃ hasBinOpB : HasBinOp B ⦄
           ⦃ isMagmaB : IsMagmaFromOps hasBinOpB ⦄ : Set (a ⊔ ℓ) where

    open HasBinOp ⦃ … ⦄
    open IsMagma ⦃ … ⦄ -- brings into scope 'isEquivalence' and '∙-cong'

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

  record SemigroupLawTransfer
           ⦃ hasBinOpA : HasBinOp A ⦄
           ⦃ hasBinOpB : HasBinOp B ⦄
           ⦃ isSemigroupB : IsSemigroupFromOps hasBinOpB ⦄ : Set (a ⊔ ℓ) where

    open HasBinOp ⦃ … ⦄
    open IsSemigroup ⦃ … ⦄ -- brings into scope 'isMagma' and 'assoc'

    instance
      _ : IsMagma {b} _≈_ _∙_
      _ = isMagma

    field
      magmaLawTransfer : MagmaLawTransfer

    -- brings record fields '∙-homo' and 'isMagma-trans' into
    -- scope and re-exports them
    open MagmaLawTransfer magmaLawTransfer public

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

  record MonoidLawTransfer
           ⦃ hasMonoidOpsA : HasMonoidOps A ⦄
           ⦃ hasMonoidOpsB : HasMonoidOps B ⦄
           ⦃ isMonoidB : IsMonoidFromOps hasMonoidOpsB ⦄ : Set (a ⊔ ℓ) where

    open HasMonoidOps ⦃ … ⦄
    open IsMonoid ⦃ … ⦄

    instance
      _ : IsSemigroup {b} _≈_ _∙_
      _ = isSemigroup

    field
      semigroupLawTransfer : SemigroupLawTransfer
      ε-homo : ⟦ ε ⟧ ≈ ε

    -- Bring record fields into scope and re-export them
    open SemigroupLawTransfer semigroupLawTransfer public

    isMonoid-trans : IsMonoid {a} _≈_ _∙_ ε
    isMonoid-trans =
      record
        { isSemigroup = isSemigroup-trans
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

  record GroupLawTransfer
           ⦃ hasGroupOpsA : HasGroupOps A ⦄
           ⦃ hasGroupOpsB : HasGroupOps B ⦄
           ⦃ isGroupB : IsGroupFromOps hasGroupOpsB ⦄ : Set (a ⊔ ℓ) where

    open HasGroupOps ⦃ … ⦄
    open IsGroup ⦃ … ⦄

    instance
      _ : IsMonoid {b} _≈_ _∙_ ε
      _ = isMonoid

    field
      monoidLawTransfer : MonoidLawTransfer
      ⁻¹-homo : ∀ x → ⟦ x ⁻¹ ⟧ ≈ ⟦ x ⟧ ⁻¹

    open MonoidLawTransfer monoidLawTransfer public

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

  record AbelianGroupLawTransfer
           ⦃ hasGroupOpsA : HasGroupOps A ⦄
           ⦃ hasGroupOpsB : HasGroupOps B ⦄
           ⦃ isAbelianGroupB : IsAbelianGroupFromOps hasGroupOpsB ⦄ : Set (a ⊔ ℓ) where

    open HasGroupOps ⦃ … ⦄
    open IsAbelianGroup ⦃ … ⦄

    instance
      _ : IsGroup {b} _≈_ _∙_ ε _⁻¹
      _ = isGroup

    field
      groupLawTransfer : GroupLawTransfer

    open GroupLawTransfer groupLawTransfer public

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

  record RingLawTransfer
           ⦃ hasRingOpsA : HasRingOps A ⦄
           ⦃ hasRingOpsB : HasRingOps B ⦄
           ⦃ isRingB : IsRingFromOps hasRingOpsB ⦄ : Set (a ⊔ ℓ) where
    open HasRingOps ⦃ … ⦄
    open IsRing ⦃ … ⦄

    instance
      _ : IsAbelianGroup {b} _≈_ _+_ 0# (-_)
      _ = +-isAbelianGroup
      _ : IsMonoid {b} _≈_ _*_ 1#
      _ = *-isMonoid

    field
      +-abelianGroupLawTransfer : AbelianGroupLawTransfer
      *-monoidLawTransfer : MonoidLawTransfer

    open AbelianGroupLawTransfer +-abelianGroupLawTransfer public
      renaming
      ( ∙-homo                  to +-homo
      ; ε-homo                  to 0#-homo
      ; ⁻¹-homo                 to [-]-homo -- TODO: Come up with a new name
      ; magmaLawTransfer        to +-magmaLawTransfer
      ; semigroupLawTransfer    to +-semigroupLawTransfer
      ; monoidLawTransfer       to +-monoidLawTransfer
      ; isMagma-trans           to +-isMagma-trans
      ; isSemigroup-trans       to +-isSemigroup-trans
      ; isMonoid-trans          to +-isMonoid-trans
      ; isGroup-trans           to +-isGroup-trans
      ; isAbelianGroup-trans    to +-isAbelianGroup-trans
      )
    open MonoidLawTransfer *-monoidLawTransfer public
      renaming
      ( ∙-homo                  to *-homo
      ; ε-homo                  to 1#-homo
      ; magmaLawTransfer        to *-magmaLawTransfer
      ; semigroupLawTransfer    to *-semigroupLawTransfer
      ; isMagma-trans           to *-isMagma-trans
      ; isSemigroup-trans       to *-isSemigroup-trans
      ; isMonoid-trans          to *-isMonoid-trans
      )

    isRing-trans : IsRingFromOps hasRingOpsA
    isRing-trans =
      record
        { +-isAbelianGroup = +-isAbelianGroup-trans
        ; *-isMonoid       = *-isMonoid-trans
        ; distrib          = distributionˡ , distributionʳ
        ; zero             = zˡ , zʳ
        }
      where
        open import Relation.Binary.Reasoning.Setoid (setoid)

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
