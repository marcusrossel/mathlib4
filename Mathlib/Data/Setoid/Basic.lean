/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Bryan Gin-ge Chen
-/
import Mathlib.Logic.Relation
import Mathlib.Order.GaloisConnection

#align_import data.setoid.basic from "leanprover-community/mathlib"@"bbeb185db4ccee8ed07dc48449414ebfa39cb821"

/-!
# Equivalence relations

This file defines the complete lattice of equivalence relations on a type, results about the
inductively defined equivalence closure of a binary relation, and the analogues of some isomorphism
theorems for quotients of arbitrary types.

## Implementation notes

The function `Rel` and lemmas ending in ' make it easier to talk about different
equivalence relations on the same type.

The complete lattice instance for equivalence relations could have been defined by lifting
the Galois insertion of equivalence relations on α into binary relations on α, and then using
`CompleteLattice.copy` to define a complete lattice instance with more appropriate
definitional equalities (a similar example is `Filter.CompleteLattice` in
`Order/Filter/Basic.lean`). This does not save space, however, and is less clear.

Partitions are not defined as a separate structure here; users are encouraged to
reason about them using the existing `Setoid` and its infrastructure.

## Tags

setoid, equivalence, iseqv, relation, equivalence relation
-/

variable {α : Type*} {β : Type*}

/-- A version of `Setoid.r` that takes the equivalence relation as an explicit argument. -/
def Setoid.Rel (r : Setoid α) : α → α → Prop :=
  @Setoid.r _ r
#align setoid.rel Setoid.Rel

instance Setoid.decidableRel (r : Setoid α) [h : DecidableRel r.r] : DecidableRel r.Rel :=
  h
#align setoid.decidable_rel Setoid.decidableRel

/-- A version of `Quotient.eq'` compatible with `Setoid.Rel`, to make rewriting possible. -/
theorem Quotient.eq_rel {r : Setoid α} {x y} :
    (Quotient.mk' x : Quotient r) = Quotient.mk' y ↔ r.Rel x y :=
  Quotient.eq
#align quotient.eq_rel Quotient.eq_rel

namespace Setoid

@[ext]
theorem ext' {r s : Setoid α} (H : ∀ a b, r.Rel a b ↔ s.Rel a b) : r = s :=
  ext H
#align setoid.ext' Setoid.ext'

theorem ext_iff {r s : Setoid α} : r = s ↔ ∀ a b, r.Rel a b ↔ s.Rel a b :=
  ⟨fun h _ _ => h ▸ Iff.rfl, ext'⟩
#align setoid.ext_iff Setoid.ext_iff

/-- Two equivalence relations are equal iff their underlying binary operations are equal. -/
theorem eq_iff_rel_eq {r₁ r₂ : Setoid α} : r₁ = r₂ ↔ r₁.Rel = r₂.Rel :=
  ⟨fun h => h ▸ rfl, fun h => Setoid.ext' fun _ _ => h ▸ Iff.rfl⟩
#align setoid.eq_iff_rel_eq Setoid.eq_iff_rel_eq

/-- Defining `≤` for equivalence relations. -/
instance : LE (Setoid α) :=
  ⟨fun r s => ∀ ⦃x y⦄, r.Rel x y → s.Rel x y⟩

theorem le_def {r s : Setoid α} : r ≤ s ↔ ∀ {x y}, r.Rel x y → s.Rel x y :=
  Iff.rfl
#align setoid.le_def Setoid.le_def

@[refl]
theorem refl' (r : Setoid α) (x) : r.Rel x x := r.iseqv.refl x
#align setoid.refl' Setoid.refl'

@[symm]
theorem symm' (r : Setoid α) : ∀ {x y}, r.Rel x y → r.Rel y x := r.iseqv.symm
#align setoid.symm' Setoid.symm'

@[trans]
theorem trans' (r : Setoid α) : ∀ {x y z}, r.Rel x y → r.Rel y z → r.Rel x z := r.iseqv.trans
#align setoid.trans' Setoid.trans'

theorem comm' (s : Setoid α) {x y} : s.Rel x y ↔ s.Rel y x :=
  ⟨s.symm', s.symm'⟩
#align setoid.comm' Setoid.comm'

/-- The kernel of a function is an equivalence relation. -/
def ker (f : α → β) : Setoid α :=
  ⟨(· = ·) on f, eq_equivalence.comap f⟩
#align setoid.ker Setoid.ker

/-- The kernel of the quotient map induced by an equivalence relation r equals r. -/
@[simp]
theorem ker_mk_eq (r : Setoid α) : ker (@Quotient.mk'' _ r) = r :=
  ext' fun _ _ => Quotient.eq
#align setoid.ker_mk_eq Setoid.ker_mk_eq

theorem ker_apply_mk_out {f : α → β} (a : α) : f (haveI := Setoid.ker f; ⟦a⟧.out) = f a :=
  @Quotient.mk_out _ (Setoid.ker f) a
#align setoid.ker_apply_mk_out Setoid.ker_apply_mk_out

theorem ker_apply_mk_out' {f : α → β} (a : α) :
    f (Quotient.mk _ a : Quotient <| Setoid.ker f).out' = f a :=
  @Quotient.mk_out' _ (Setoid.ker f) a
#align setoid.ker_apply_mk_out' Setoid.ker_apply_mk_out'

theorem ker_def {f : α → β} {x y : α} : (ker f).Rel x y ↔ f x = f y :=
  Iff.rfl
#align setoid.ker_def Setoid.ker_def

/-- Given types `α`, `β`, the product of two equivalence relations `r` on `α` and `s` on `β`:
    `(x₁, x₂), (y₁, y₂) ∈ α × β` are related by `r.prod s` iff `x₁` is related to `y₁`
    by `r` and `x₂` is related to `y₂` by `s`. -/
protected def prod (r : Setoid α) (s : Setoid β) :
    Setoid (α × β) where
  r x y := r.Rel x.1 y.1 ∧ s.Rel x.2 y.2
  iseqv :=
    ⟨fun x => ⟨r.refl' x.1, s.refl' x.2⟩, fun h => ⟨r.symm' h.1, s.symm' h.2⟩,
      fun h₁ h₂ => ⟨r.trans' h₁.1 h₂.1, s.trans' h₁.2 h₂.2⟩⟩
#align setoid.prod Setoid.prod

/-- The infimum of two equivalence relations. -/
instance : Inf (Setoid α) :=
  ⟨fun r s =>
    ⟨fun x y => r.Rel x y ∧ s.Rel x y,
      ⟨fun x => ⟨r.refl' x, s.refl' x⟩, fun h => ⟨r.symm' h.1, s.symm' h.2⟩, fun h1 h2 =>
        ⟨r.trans' h1.1 h2.1, s.trans' h1.2 h2.2⟩⟩⟩⟩

/-- The infimum of 2 equivalence relations r and s is the same relation as the infimum
    of the underlying binary operations. -/
theorem inf_def {r s : Setoid α} : (r ⊓ s).Rel = r.Rel ⊓ s.Rel :=
  rfl
#align setoid.inf_def Setoid.inf_def

theorem inf_iff_and {r s : Setoid α} {x y} : (r ⊓ s).Rel x y ↔ r.Rel x y ∧ s.Rel x y :=
  Iff.rfl
#align setoid.inf_iff_and Setoid.inf_iff_and

/-- The infimum of a set of equivalence relations. -/
instance : InfSet (Setoid α) :=
  ⟨fun S =>
    { r := fun x y => ∀ r ∈ S, r.Rel x y
      iseqv := ⟨fun x r _ => r.refl' x, fun h r hr => r.symm' <| h r hr, fun h1 h2 r hr =>
        r.trans' (h1 r hr) <| h2 r hr⟩ }⟩

/-- The underlying binary operation of the infimum of a set of equivalence relations
    is the infimum of the set's image under the map to the underlying binary operation. -/
theorem sInf_def {s : Set (Setoid α)} : (sInf s).Rel = sInf (Rel '' s) := by
  ext
  simp only [sInf_image, iInf_apply, iInf_Prop_eq]
  rfl
#align setoid.Inf_def Setoid.sInf_def

instance : PartialOrder (Setoid α) where
  le := (· ≤ ·)
  lt r s := r ≤ s ∧ ¬s ≤ r
  le_refl _ _ _ := id
  le_trans _ _ _ hr hs _ _ h := hs <| hr h
  lt_iff_le_not_le _ _ := Iff.rfl
  le_antisymm _ _ h1 h2 := Setoid.ext' fun _ _ => ⟨fun h => h1 h, fun h => h2 h⟩

/-- The complete lattice of equivalence relations on a type, with bottom element `=`
    and top element the trivial equivalence relation. -/
instance completeLattice : CompleteLattice (Setoid α) :=
  { (completeLatticeOfInf (Setoid α)) fun _ =>
      ⟨fun _ hr _ _ h => h _ hr, fun _ hr _ _ h _ hr' => hr hr' h⟩ with
    inf := Inf.inf
    inf_le_left := fun _ _ _ _ h => h.1
    inf_le_right := fun _ _ _ _ h => h.2
    le_inf := fun _ _ _ h1 h2 _ _ h => ⟨h1 h, h2 h⟩
    top := ⟨fun _ _ => True, ⟨fun _ => trivial, fun h => h, fun h1 _ => h1⟩⟩
    le_top := fun _ _ _ _ => trivial
    bot := ⟨(· = ·), ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩⟩
    bot_le := fun r x _ h => h ▸ r.2.1 x }
#align setoid.complete_lattice Setoid.completeLattice

@[simp]
theorem top_def : (⊤ : Setoid α).Rel = ⊤ :=
  rfl
#align setoid.top_def Setoid.top_def

@[simp]
theorem bot_def : (⊥ : Setoid α).Rel = (· = ·) :=
  rfl
#align setoid.bot_def Setoid.bot_def

theorem eq_top_iff {s : Setoid α} : s = (⊤ : Setoid α) ↔ ∀ x y : α, s.Rel x y := by
  rw [_root_.eq_top_iff, Setoid.le_def, Setoid.top_def]
  simp only [Pi.top_apply, Prop.top_eq_true, forall_true_left]
#align setoid.eq_top_iff Setoid.eq_top_iff

lemma sInf_equiv {S : Set (Setoid α)} {x y : α} :
    letI := sInf S
    x ≈ y ↔ ∀ s ∈ S, s.Rel x y := Iff.rfl

lemma quotient_mk_sInf_eq {S : Set (Setoid α)} {x y : α} :
    Quotient.mk (sInf S) x = Quotient.mk (sInf S) y ↔ ∀ s ∈ S, s.Rel x y := by
  simp
  rfl

/-- The map induced between quotients by a setoid inequality. -/
def map_of_le {s t : Setoid α} (h : s ≤ t) : Quotient s → Quotient t :=
  Quotient.map' id h

/-- The map from the quotient of the infimum of a set of setoids into the quotient
by an element of this set. -/
def map_sInf {S : Set (Setoid α)} {s : Setoid α} (h : s ∈ S) :
    Quotient (sInf S) → Quotient s :=
  Setoid.map_of_le fun _ _ a ↦ a s h

/-- The inductively defined equivalence closure of a binary relation r is the infimum
    of the set of all equivalence relations containing r. -/
theorem eqvGen_eq (r : α → α → Prop) :
    EqvGen.Setoid r = sInf { s : Setoid α | ∀ ⦃x y⦄, r x y → s.Rel x y } :=
  le_antisymm
    (fun _ _ H =>
      EqvGen.rec (fun _ _ h _ hs => hs h) (refl' _) (fun _ _ _ => symm' _)
        (fun _ _ _ _ _ => trans' _) H)
    (sInf_le fun _ _ h => EqvGen.rel _ _ h)
#align setoid.eqv_gen_eq Setoid.eqvGen_eq

/-- The supremum of two equivalence relations r and s is the equivalence closure of the binary
    relation `x is related to y by r or s`. -/
theorem sup_eq_eqvGen (r s : Setoid α) :
    r ⊔ s = EqvGen.Setoid fun x y => r.Rel x y ∨ s.Rel x y := by
  rw [eqvGen_eq]
  apply congr_arg sInf
  -- Egg: Stack overflow
  sorry -- simp only [le_def, or_imp, ← forall_and]
#align setoid.sup_eq_eqv_gen Setoid.sup_eq_eqvGen

/-- The supremum of 2 equivalence relations r and s is the equivalence closure of the
    supremum of the underlying binary operations. -/
theorem sup_def {r s : Setoid α} : r ⊔ s = EqvGen.Setoid (r.Rel ⊔ s.Rel) := by
  rw [sup_eq_eqvGen]; rfl
#align setoid.sup_def Setoid.sup_def

/-- The supremum of a set S of equivalence relations is the equivalence closure of the binary
    relation `there exists r ∈ S relating x and y`. -/
theorem sSup_eq_eqvGen (S : Set (Setoid α)) :
    sSup S = EqvGen.Setoid fun x y => ∃ r : Setoid α, r ∈ S ∧ r.Rel x y := by
  rw [eqvGen_eq]
  apply congr_arg sInf
  simp only [upperBounds, le_def, and_imp, exists_imp]
  ext
  exact ⟨fun H x y r hr => H hr, fun H r hr x y => H r hr⟩
#align setoid.Sup_eq_eqv_gen Setoid.sSup_eq_eqvGen

/-- The supremum of a set of equivalence relations is the equivalence closure of the
    supremum of the set's image under the map to the underlying binary operation. -/
theorem sSup_def {s : Set (Setoid α)} : sSup s = EqvGen.Setoid (sSup (Rel '' s)) := by
  rw [sSup_eq_eqvGen, sSup_image]
  congr with (x y)
  simp only [iSup_apply, iSup_Prop_eq, exists_prop]
#align setoid.Sup_def Setoid.sSup_def

/-- The equivalence closure of an equivalence relation r is r. -/
@[simp]
theorem eqvGen_of_setoid (r : Setoid α) : EqvGen.Setoid r.r = r :=
  le_antisymm (by rw [eqvGen_eq]; exact sInf_le fun _ _ => id) EqvGen.rel
#align setoid.eqv_gen_of_setoid Setoid.eqvGen_of_setoid

/-- Equivalence closure is idempotent. -/
@[simp]
theorem eqvGen_idem (r : α → α → Prop) : EqvGen.Setoid (EqvGen.Setoid r).Rel = EqvGen.Setoid r :=
  eqvGen_of_setoid _
#align setoid.eqv_gen_idem Setoid.eqvGen_idem

/-- The equivalence closure of a binary relation r is contained in any equivalence
    relation containing r. -/
theorem eqvGen_le {r : α → α → Prop} {s : Setoid α} (h : ∀ x y, r x y → s.Rel x y) :
    EqvGen.Setoid r ≤ s := by rw [eqvGen_eq]; exact sInf_le h
#align setoid.eqv_gen_le Setoid.eqvGen_le

/-- Equivalence closure of binary relations is monotone. -/
theorem eqvGen_mono {r s : α → α → Prop} (h : ∀ x y, r x y → s x y) :
    EqvGen.Setoid r ≤ EqvGen.Setoid s :=
  eqvGen_le fun _ _ hr => EqvGen.rel _ _ <| h _ _ hr
#align setoid.eqv_gen_mono Setoid.eqvGen_mono

/-- There is a Galois insertion of equivalence relations on α into binary relations
    on α, with equivalence closure the lower adjoint. -/
def gi : @GaloisInsertion (α → α → Prop) (Setoid α) _ _ EqvGen.Setoid Rel where
  choice r _ := EqvGen.Setoid r
  gc _ s := ⟨fun H _ _ h => H <| EqvGen.rel _ _ h, fun H => eqvGen_of_setoid s ▸ eqvGen_mono H⟩
  le_l_u x := (eqvGen_of_setoid x).symm ▸ le_refl x
  choice_eq _ _ := rfl
#align setoid.gi Setoid.gi

open Function

/-- A function from α to β is injective iff its kernel is the bottom element of the complete lattice
    of equivalence relations on α. -/
theorem injective_iff_ker_bot (f : α → β) : Injective f ↔ ker f = ⊥ :=
  (@eq_bot_iff (Setoid α) _ _ (ker f)).symm
#align setoid.injective_iff_ker_bot Setoid.injective_iff_ker_bot

/-- The elements related to x ∈ α by the kernel of f are those in the preimage of f(x) under f. -/
theorem ker_iff_mem_preimage {f : α → β} {x y} : (ker f).Rel x y ↔ x ∈ f ⁻¹' {f y} :=
  Iff.rfl
#align setoid.ker_iff_mem_preimage Setoid.ker_iff_mem_preimage

/-- Equivalence between functions `α → β` such that `r x y → f x = f y` and functions
`quotient r → β`. -/
def liftEquiv (r : Setoid α) : { f : α → β // r ≤ ker f } ≃ (Quotient r → β) where
  toFun f := Quotient.lift (f : α → β) f.2
  invFun f := ⟨f ∘ Quotient.mk'', fun x y h => by simp [ker_def, Quotient.sound' h]⟩
  left_inv := fun ⟨f, hf⟩ => Subtype.eq <| funext fun x => rfl
  right_inv f := funext fun x => Quotient.inductionOn' x fun x => rfl
#align setoid.lift_equiv Setoid.liftEquiv

/-- The uniqueness part of the universal property for quotients of an arbitrary type. -/
theorem lift_unique {r : Setoid α} {f : α → β} (H : r ≤ ker f) (g : Quotient r → β)
    (Hg : f = g ∘ Quotient.mk'') : Quotient.lift f H = g := by
  ext ⟨x⟩
  erw [Quotient.lift_mk f H, Hg]
  rfl
#align setoid.lift_unique Setoid.lift_unique

/-- Given a map f from α to β, the natural map from the quotient of α by the kernel of f is
    injective. -/
theorem ker_lift_injective (f : α → β) : Injective (@Quotient.lift _ _ (ker f) f fun _ _ h => h) :=
  fun x y => Quotient.inductionOn₂' x y fun _ _ h => Quotient.sound' h
#align setoid.ker_lift_injective Setoid.ker_lift_injective

/-- Given a map f from α to β, the kernel of f is the unique equivalence relation on α whose
    induced map from the quotient of α to β is injective. -/
theorem ker_eq_lift_of_injective {r : Setoid α} (f : α → β) (H : ∀ x y, r.Rel x y → f x = f y)
    (h : Injective (Quotient.lift f H)) : ker f = r :=
  le_antisymm
    (fun x y hk =>
      Quotient.exact <| h <| show Quotient.lift f H ⟦x⟧ = Quotient.lift f H ⟦y⟧ from hk)
    H
#align setoid.ker_eq_lift_of_injective Setoid.ker_eq_lift_of_injective

variable (r : Setoid α) (f : α → β)

/-- The first isomorphism theorem for sets: the quotient of α by the kernel of a function f
    bijects with f's image. -/
noncomputable def quotientKerEquivRange : Quotient (ker f) ≃ Set.range f :=
  Equiv.ofBijective
    ((@Quotient.lift _ (Set.range f) (ker f) fun x => ⟨f x, Set.mem_range_self x⟩) fun _ _ h =>
      Subtype.ext_val h)
    ⟨fun x y h => ker_lift_injective f <| by rcases x with ⟨⟩; rcases y with ⟨⟩; injections,
      fun ⟨w, z, hz⟩ =>
      ⟨@Quotient.mk'' _ (ker f) z, Subtype.ext_iff_val.2 hz⟩⟩
#align setoid.quotient_ker_equiv_range Setoid.quotientKerEquivRange

/-- If `f` has a computable right-inverse, then the quotient by its kernel is equivalent to its
domain. -/
@[simps]
def quotientKerEquivOfRightInverse (g : β → α) (hf : Function.RightInverse g f) :
    Quotient (ker f) ≃ β where
  toFun a := (Quotient.liftOn' a f) fun _ _ => id
  invFun b := Quotient.mk'' (g b)
  left_inv a := Quotient.inductionOn' a fun a => Quotient.sound' <| hf (f a)
  right_inv := hf
#align setoid.quotient_ker_equiv_of_right_inverse Setoid.quotientKerEquivOfRightInverse
#align setoid.quotient_ker_equiv_of_right_inverse_symm_apply Setoid.quotientKerEquivOfRightInverse_symm_apply
#align setoid.quotient_ker_equiv_of_right_inverse_apply Setoid.quotientKerEquivOfRightInverse_apply

/-- The quotient of α by the kernel of a surjective function f bijects with f's codomain.

If a specific right-inverse of `f` is known, `Setoid.quotientKerEquivOfRightInverse` can be
definitionally more useful. -/
noncomputable def quotientKerEquivOfSurjective (hf : Surjective f) : Quotient (ker f) ≃ β :=
  quotientKerEquivOfRightInverse _ (Function.surjInv hf) (rightInverse_surjInv hf)
#align setoid.quotient_ker_equiv_of_surjective Setoid.quotientKerEquivOfSurjective

variable {r f}

/-- Given a function `f : α → β` and equivalence relation `r` on `α`, the equivalence
    closure of the relation on `f`'s image defined by '`x ≈ y` iff the elements of `f⁻¹(x)` are
    related to the elements of `f⁻¹(y)` by `r`.' -/
def map (r : Setoid α) (f : α → β) : Setoid β :=
  EqvGen.Setoid fun x y => ∃ a b, f a = x ∧ f b = y ∧ r.Rel a b
#align setoid.map Setoid.map

/-- Given a surjective function f whose kernel is contained in an equivalence relation r, the
    equivalence relation on f's codomain defined by x ≈ y ↔ the elements of f⁻¹(x) are related to
    the elements of f⁻¹(y) by r. -/
def mapOfSurjective (r) (f : α → β) (h : ker f ≤ r) (hf : Surjective f) : Setoid β :=
  ⟨fun x y => ∃ a b, f a = x ∧ f b = y ∧ r.Rel a b,
    ⟨fun x =>
      let ⟨y, hy⟩ := hf x
      ⟨y, y, hy, hy, r.refl' y⟩,
      fun ⟨x, y, hx, hy, h⟩ => ⟨y, x, hy, hx, r.symm' h⟩,
      fun ⟨x, y, hx, hy, h₁⟩ ⟨y', z, hy', hz, h₂⟩ =>
      ⟨x, z, hx, hz, r.trans' h₁ <| r.trans' (h <| by rwa [← hy'] at hy) h₂⟩⟩⟩
#align setoid.map_of_surjective Setoid.mapOfSurjective

/-- A special case of the equivalence closure of an equivalence relation r equalling r. -/
theorem mapOfSurjective_eq_map (h : ker f ≤ r) (hf : Surjective f) :
    map r f = mapOfSurjective r f h hf := by
  rw [← eqvGen_of_setoid (mapOfSurjective r f h hf)]; rfl
#align setoid.map_of_surjective_eq_map Setoid.mapOfSurjective_eq_map

/-- Given a function `f : α → β`, an equivalence relation `r` on `β` induces an equivalence
relation on `α` defined by '`x ≈ y` iff `f(x)` is related to `f(y)` by `r`'.

See note [reducible non-instances]. -/
abbrev comap (f : α → β) (r : Setoid β) : Setoid α :=
  ⟨r.Rel on f, r.iseqv.comap _⟩
#align setoid.comap Setoid.comap

theorem comap_rel (f : α → β) (r : Setoid β) (x y : α) : (comap f r).Rel x y ↔ r.Rel (f x) (f y) :=
  Iff.rfl
#align setoid.comap_rel Setoid.comap_rel

/-- Given a map `f : N → M` and an equivalence relation `r` on `β`, the equivalence relation
    induced on `α` by `f` equals the kernel of `r`'s quotient map composed with `f`. -/
theorem comap_eq {f : α → β} {r : Setoid β} : comap f r = ker (@Quotient.mk'' _ r ∘ f) :=
  ext fun x y => show _ ↔ ⟦_⟧ = ⟦_⟧ by rw [Quotient.eq]; rfl
#align setoid.comap_eq Setoid.comap_eq

/-- The second isomorphism theorem for sets. -/
noncomputable def comapQuotientEquiv (f : α → β) (r : Setoid β) :
    Quotient (comap f r) ≃ Set.range (@Quotient.mk'' _ r ∘ f) :=
  (Quotient.congrRight <| ext_iff.1 comap_eq).trans <| quotientKerEquivRange <| Quotient.mk'' ∘ f
#align setoid.comap_quotient_equiv Setoid.comapQuotientEquiv

variable (r f)

/-- The third isomorphism theorem for sets. -/
def quotientQuotientEquivQuotient (s : Setoid α) (h : r ≤ s) :
    Quotient (ker (Quot.mapRight h)) ≃ Quotient s where
  toFun x :=
    (Quotient.liftOn' x fun w =>
        (Quotient.liftOn' w (@Quotient.mk'' _ s)) fun x y H => Quotient.sound <| h H)
      fun x y => Quotient.inductionOn₂' x y fun w z H => show @Quot.mk _ _ _ = @Quot.mk _ _ _ from H
  invFun x :=
    (Quotient.liftOn' x fun w => @Quotient.mk'' _ (ker <| Quot.mapRight h) <| @Quotient.mk'' _ r w)
      fun x y H => Quotient.sound' <| show @Quot.mk _ _ _ = @Quot.mk _ _ _ from Quotient.sound H
  left_inv x :=
    Quotient.inductionOn' x fun y => Quotient.inductionOn' y fun w => by show ⟦_⟧ = _; rfl
  right_inv x := Quotient.inductionOn' x fun y => by show ⟦_⟧ = _; rfl
#align setoid.quotient_quotient_equiv_quotient Setoid.quotientQuotientEquivQuotient

variable {r f}

open Quotient

/-- Given an equivalence relation `r` on `α`, the order-preserving bijection between the set of
equivalence relations containing `r` and the equivalence relations on the quotient of `α` by `r`. -/
def correspondence (r : Setoid α) : { s // r ≤ s } ≃o Setoid (Quotient r) where
  toFun s := ⟨Quotient.lift₂ s.1.1 fun _ _ _ _ h₁ h₂ ↦ Eq.propIntro
      (fun h ↦ s.1.trans' (s.1.trans' (s.1.symm' (s.2 h₁)) h) (s.2 h₂))
      (fun h ↦ s.1.trans' (s.1.trans' (s.2 h₁) h) (s.1.symm' (s.2 h₂))),
    ⟨Quotient.ind s.1.2.1, @fun x y ↦ Quotient.inductionOn₂ x y fun _ _ ↦ s.1.2.2,
      @fun x y z ↦ Quotient.inductionOn₃ x y z fun _ _ _ ↦ s.1.2.3⟩⟩
  invFun s := ⟨comap Quotient.mk' s, fun x y h => by rw [comap_rel, eq_rel.2 h]⟩
  left_inv s := rfl
  right_inv s := ext fun x y ↦ Quotient.inductionOn₂ x y fun _ _ ↦ Iff.rfl
  map_rel_iff' :=
    ⟨fun h x y hs ↦ @h ⟦x⟧ ⟦y⟧ hs, fun h x y ↦ Quotient.inductionOn₂ x y fun _ _ hs ↦ h hs⟩
#align setoid.correspondence Setoid.correspondence

/-- Given two equivalence relations with `r ≤ s`, a bijection between the sum of the quotients by
`r` on each equivalence class by `s` and the quotient by `r`. -/
def sigmaQuotientEquivOfLe {r s : Setoid α} (hle : r ≤ s) :
    (Σ q : Quotient s, Quotient (r.comap (Subtype.val : Quotient.mk s ⁻¹' {q} → α))) ≃
      Quotient r :=
  .trans (.symm <| .sigmaCongrRight fun _ ↦ .subtypeQuotientEquivQuotientSubtype
      (s₁ := r) (s₂ := r.comap Subtype.val) _ (fun _ ↦ Iff.rfl) fun _ _ ↦ Iff.rfl)
    (.sigmaFiberEquiv fun a ↦ a.lift (Quotient.mk s) fun _ _ h ↦ Quotient.sound <| hle h)

end Setoid

@[simp]
theorem Quotient.subsingleton_iff {s : Setoid α} : Subsingleton (Quotient s) ↔ s = ⊤ := by
  simp only [_root_.subsingleton_iff, eq_top_iff, Setoid.le_def, Setoid.top_def, Pi.top_apply,
    forall_const]
  refine (surjective_quotient_mk' _).forall.trans (forall_congr' fun a => ?_)
  refine (surjective_quotient_mk' _).forall.trans (forall_congr' fun b => ?_)
  simp_rw [Prop.top_eq_true, true_implies, Quotient.eq']
  rfl
#align quotient.subsingleton_iff Quotient.subsingleton_iff

theorem Quot.subsingleton_iff (r : α → α → Prop) : Subsingleton (Quot r) ↔ EqvGen r = ⊤ := by
  simp only [_root_.subsingleton_iff, _root_.eq_top_iff, Pi.le_def, Pi.top_apply, forall_const]
  refine (surjective_quot_mk _).forall.trans (forall_congr' fun a => ?_)
  refine (surjective_quot_mk _).forall.trans (forall_congr' fun b => ?_)
  rw [Quot.eq]
  simp only [forall_const, le_Prop_eq, Pi.top_apply, Prop.top_eq_true, true_implies]
#align quot.subsingleton_iff Quot.subsingleton_iff
