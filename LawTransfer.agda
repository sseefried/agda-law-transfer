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

--record HasGroupOps {a} (A : Set a) : Set a where
--  open HasBinOp    public
--  open HasIdentity public
--  open HasInverse   public

record HasRingOps {a} (A : Set a) : Set a where
  infixr 26 _+_
  infixr 27 _*_
  field
    _+_ : A → A → A
    _*_ : A → A → A
    -_ : A → A
    0# : A
    1# : A

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
  IsRingFromOps {x} o  = IsRing {x} _≈_ _+_ _*_ -_ 0#  1#
    where
      open HasRingOps o

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
      _ : HasBinOp A
      _ = HasMonoidOps.hasBinOp hasMonoidOpsA
      _ : HasBinOp B
      _ = HasMonoidOps.hasBinOp hasMonoidOpsB
      _ : HasIdentity A
      _ = HasMonoidOps.hasIdentity hasMonoidOpsA
      _ : HasIdentity B
      _ = HasMonoidOps.hasIdentity hasMonoidOpsB
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
           (_∙₁_ : Op₂ A)
           (ε₁ : A)
           (_₁⁻¹ : Op₁ A)
           (_∙₂_ : Op₂ B)
           (ε₂ : B)
           (_₂⁻¹ : Op₁ B)
           ⦃ isGroupB : IsGroup {b} _≈_ _∙₂_ ε₂ _₂⁻¹ ⦄ : Set (a ⊔ ℓ) where

    open HasMonoidOps ⦃ … ⦄
    open HasInverse ⦃ … ⦄
    open IsGroup ⦃ … ⦄

    instance
      _ : HasMonoidOps A
      _ = record { hasBinOp = record { _∙_ = _∙₁_} ; hasIdentity = record { ε = ε₁} }
      _ : HasMonoidOps B
      _ = record { hasBinOp = record { _∙_ = _∙₂_} ; hasIdentity = record { ε = ε₂} }
      _ : HasInverse A
      _ = record { _⁻¹ = _₁⁻¹ }
      _ : HasInverse B
      _ = record { _⁻¹ = _₂⁻¹ }
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
           (_∙₁_ : Op₂ A)
           (ε₁ : A)
           (_₁⁻¹ : Op₁ A)
           (_∙₂_ : Op₂ B)
           (ε₂ : B)
           (_₂⁻¹ : Op₁ B)
           ⦃ isAbelianGroupB : IsAbelianGroup _≈_ _∙₂_ ε₂ _₂⁻¹ ⦄ : Set (a ⊔ ℓ) where

    open HasBinOp ⦃ … ⦄
    open HasIdentity ⦃ … ⦄
    open HasInverse ⦃ … ⦄
    open IsAbelianGroup ⦃ … ⦄

    instance
      _ : HasBinOp A
      _ = record { _∙_ = _∙₁_ }
      _ : HasIdentity A
      _ = record { ε = ε₁ }
      _ : HasInverse A
      _ = record { _⁻¹ = _₁⁻¹ }
      _ : HasBinOp B
      _ = record { _∙_ = _∙₂_ }
      _ : HasIdentity B
      _ = record { ε = ε₂ }
      _ : HasInverse B
      _ = record { _⁻¹ = _₂⁻¹ }
      _ : IsGroup {b} _≈_ _∙_ ε _⁻¹
      _ = isGroup

    field
      groupLawTransfer : GroupLawTransfer _∙₁_ ε₁ _₁⁻¹  _∙₂_ ε₂ _₂⁻¹

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
           (hasRingOpsA : HasRingOps A)
           (hasRingOpsB : HasRingOps B)
           ⦃ isRingB : IsRingFromOps hasRingOpsB ⦄ : Set (a ⊔ ℓ) where
    open HasRingOps ⦃ … ⦄
    open IsRing ⦃ … ⦄

    instance
      _ : HasRingOps A
      _ = hasRingOpsA
      _ : HasRingOps B
      _ = hasRingOpsB
      _ : HasMonoidOps A -- FIXME:
      _ = record { hasBinOp = record { _∙_ = _*_ } ; hasIdentity = record { ε = 1# } }
      _ : HasMonoidOps B -- FIXME:
      _ = record { hasBinOp = record { _∙_ = _*_ } ; hasIdentity = record { ε = 1# } }
      _ : IsAbelianGroup {b} _≈_ _+_ 0# (-_)
      _ = +-isAbelianGroup
      _ : IsMonoid {b} _≈_ _*_ 1#
      _ = *-isMonoid

    field
      +-abelianGroupLawTransfer : AbelianGroupLawTransfer (_+_) 0# (-_) _+_ 0# (-_)
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
