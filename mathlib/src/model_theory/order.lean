/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import model_theory.semantics

/-!
# Ordered First-Ordered Structures
This file defines ordered first-order languages and structures, as well as their theories.

## Main Definitions
* `first_order.language.order` is the language consisting of a single relation representing `≤`.
* `first_order.language.order_Structure` is the structure on an ordered type, assigning the symbol
representing `≤` to the actual relation `≤`.
* `first_order.language.is_ordered` points out a specific symbol in a language as representing `≤`.
* `first_order.language.is_ordered_structure` indicates that a structure over a
* `first_order.language.Theory.linear_order` and similar define the theories of preorders,
partial orders, and linear orders.
* `first_order.language.Theory.DLO` defines the theory of dense linear orders without endpoints, a
particularly useful example in model theory.


## Main Results
* `partial_order`s model the theory of partial orders, `linear_order`s model the theory of
linear orders, and dense linear orders without endpoints model `Theory.DLO`.

-/

universes u v w w'

namespace first_order
namespace language
open_locale first_order
open Structure

variables {L : language.{u v}} {α : Type w} {M : Type w'} {n : ℕ}

/-- The language consisting of a single relation representing `≤`. -/
protected def order : language :=
language.mk₂ empty empty empty empty unit

namespace order

instance Structure [has_le M] : language.order.Structure M :=
Structure.mk₂ empty.elim empty.elim empty.elim empty.elim (λ _, (≤))

instance : is_relational (language.order) := language.is_relational_mk₂

instance : subsingleton (language.order.relations n) :=
language.subsingleton_mk₂_relations

end order

/-- A language is ordered if it has a symbol representing `≤`. -/
class is_ordered (L : language.{u v}) := (le_symb : L.relations 2)

export is_ordered (le_symb)

section is_ordered

variables [is_ordered L]

/-- Joins two terms `t₁, t₂` in a formula representing `t₁ ≤ t₂`. -/
def term.le (t₁ t₂ : L.term (α ⊕ fin n)) : L.bounded_formula α n :=
le_symb.bounded_formula₂ t₁ t₂

/-- Joins two terms `t₁, t₂` in a formula representing `t₁ < t₂`. -/
def term.lt (t₁ t₂ : L.term (α ⊕ fin n)) : L.bounded_formula α n :=
(t₁.le t₂) ⊓ ∼ (t₂.le t₁)

variable (L)

/-- The language homomorphism sending the unique symbol `≤` of `language.order` to `≤` in an ordered
 language. -/
def order_Lhom : language.order →ᴸ L :=
Lhom.mk₂ empty.elim empty.elim empty.elim empty.elim (λ _, le_symb)

end is_ordered

instance : is_ordered language.order := ⟨unit.star⟩

@[simp] lemma order_Lhom_le_symb [L.is_ordered] :
  (order_Lhom L).on_relation le_symb = (le_symb : L.relations 2) := rfl

@[simp]
lemma order_Lhom_order : order_Lhom language.order = Lhom.id language.order :=
Lhom.funext (subsingleton.elim _ _) (subsingleton.elim _ _)

instance : is_ordered (L.sum language.order) := ⟨sum.inr is_ordered.le_symb⟩

/-- The theory of preorders. -/
protected def Theory.preorder : language.order.Theory :=
{le_symb.reflexive, le_symb.transitive}

/-- The theory of partial orders. -/
protected def Theory.partial_order : language.order.Theory :=
{le_symb.reflexive, le_symb.antisymmetric, le_symb.transitive}

/-- The theory of linear orders. -/
protected def Theory.linear_order : language.order.Theory :=
{le_symb.reflexive, le_symb.antisymmetric, le_symb.transitive, le_symb.total}

/-- A sentence indicating that an order has no top element:
$\forall x, \exists y, \neg y \le x$.   -/
protected def sentence.no_top_order : language.order.sentence := ∀' ∃' ∼ ((&1).le &0)

/-- A sentence indicating that an order has no bottom element:
$\forall x, \exists y, \neg x \le y$. -/
protected def sentence.no_bot_order : language.order.sentence := ∀' ∃' ∼ ((&0).le &1)

/-- A sentence indicating that an order is dense:
$\forall x, \forall y, x < y \to \exists z, x < z \wedge z < y$. -/
protected def sentence.densely_ordered : language.order.sentence :=
∀' ∀' (((&0).lt &1) ⟹ (∃' (((&0).lt &2) ⊓ ((&2).lt &1))))

/-- The theory of dense linear orders without endpoints. -/
protected def Theory.DLO : language.order.Theory :=
Theory.linear_order ∪ {sentence.no_top_order, sentence.no_bot_order, sentence.densely_ordered}

variables (L M)

/-- A structure is ordered if its language has a `≤` symbol whose interpretation is -/
abbreviation is_ordered_structure [is_ordered L] [has_le M] [L.Structure M] : Prop :=
Lhom.is_expansion_on (order_Lhom L) M

variables {L M}

@[simp] lemma is_ordered_structure_iff [is_ordered L] [has_le M] [L.Structure M] :
  L.is_ordered_structure M ↔ Lhom.is_expansion_on (order_Lhom L) M := iff.rfl

instance is_ordered_structure_has_le [has_le M] :
  is_ordered_structure language.order M :=
begin
  rw [is_ordered_structure_iff, order_Lhom_order],
  exact Lhom.id_is_expansion_on M,
end

instance model_preorder [preorder M] :
  M ⊨ Theory.preorder :=
begin
  simp only [Theory.preorder, Theory.model_iff, set.mem_insert_iff, set.mem_singleton_iff,
    forall_eq_or_imp, relations.realize_reflexive, rel_map_apply₂, forall_eq,
    relations.realize_transitive],
  exact ⟨le_refl, λ _ _ _, le_trans⟩
end

instance model_partial_order [partial_order M] :
  M ⊨ Theory.partial_order :=
begin
  simp only [Theory.partial_order, Theory.model_iff, set.mem_insert_iff, set.mem_singleton_iff,
    forall_eq_or_imp, relations.realize_reflexive, rel_map_apply₂, relations.realize_antisymmetric,
    forall_eq, relations.realize_transitive],
  exact ⟨le_refl, λ _ _, le_antisymm, λ _ _ _, le_trans⟩,
end

instance model_linear_order [linear_order M] :
  M ⊨ Theory.linear_order :=
begin
  simp only [Theory.linear_order, Theory.model_iff, set.mem_insert_iff, set.mem_singleton_iff,
    forall_eq_or_imp, relations.realize_reflexive, rel_map_apply₂, relations.realize_antisymmetric,
    relations.realize_transitive, forall_eq, relations.realize_total],
  exact ⟨le_refl, λ _ _, le_antisymm, λ _ _ _, le_trans, le_total⟩,
end

section is_ordered_structure
variables [is_ordered L] [L.Structure M]

@[simp] lemma rel_map_le_symb [has_le M] [L.is_ordered_structure M] {a b : M} :
  rel_map (le_symb : L.relations 2) ![a, b] ↔ a ≤ b :=
begin
  rw [← order_Lhom_le_symb, Lhom.is_expansion_on.map_on_relation],
  refl,
end

@[simp] lemma term.realize_le [has_le M] [L.is_ordered_structure M]
  {t₁ t₂ : L.term (α ⊕ fin n)} {v : α → M} {xs : fin n → M} :
  (t₁.le t₂).realize v xs ↔ t₁.realize (sum.elim v xs) ≤ t₂.realize (sum.elim v xs) :=
by simp [term.le]

@[simp] lemma term.realize_lt [preorder M] [L.is_ordered_structure M]
  {t₁ t₂ : L.term (α ⊕ fin n)} {v : α → M} {xs : fin n → M} :
  (t₁.lt t₂).realize v xs ↔ t₁.realize (sum.elim v xs) < t₂.realize (sum.elim v xs) :=
by simp [term.lt, lt_iff_le_not_le]

end is_ordered_structure

section has_le
variables [has_le M]

theorem realize_no_top_order_iff : M ⊨ sentence.no_top_order ↔ no_top_order M :=
begin
  simp only [sentence.no_top_order, sentence.realize, formula.realize, bounded_formula.realize_all,
    bounded_formula.realize_ex, bounded_formula.realize_not, realize, term.realize_le,
    sum.elim_inr],
  refine ⟨λ h, ⟨λ a, h a⟩, _⟩,
  introsI h a,
  exact exists_not_le a,
end

@[simp] lemma realize_no_top_order [h : no_top_order M] : M ⊨ sentence.no_top_order :=
realize_no_top_order_iff.2 h

theorem realize_no_bot_order_iff : M ⊨ sentence.no_bot_order ↔ no_bot_order M :=
begin
  simp only [sentence.no_bot_order, sentence.realize, formula.realize, bounded_formula.realize_all,
    bounded_formula.realize_ex, bounded_formula.realize_not, realize, term.realize_le,
    sum.elim_inr],
  refine ⟨λ h, ⟨λ a, h a⟩, _⟩,
  introsI h a,
  exact exists_not_ge a,
end

@[simp] lemma realize_no_bot_order [h : no_bot_order M] : M ⊨ sentence.no_bot_order :=
realize_no_bot_order_iff.2 h

end has_le

theorem realize_densely_ordered_iff [preorder M] :
  M ⊨ sentence.densely_ordered ↔ densely_ordered M :=
begin
  simp only [sentence.densely_ordered, sentence.realize, formula.realize,
    bounded_formula.realize_imp, bounded_formula.realize_all, realize, term.realize_lt,
    sum.elim_inr, bounded_formula.realize_ex, bounded_formula.realize_inf],
  refine ⟨λ h, ⟨λ a b ab, h a b ab⟩, _⟩,
  introsI h a b ab,
  exact exists_between ab,
end

@[simp] lemma realize_densely_ordered [preorder M] [h : densely_ordered M] :
  M ⊨ sentence.densely_ordered :=
realize_densely_ordered_iff.2 h

instance model_DLO [linear_order M] [densely_ordered M] [no_top_order M] [no_bot_order M] :
  M ⊨ Theory.DLO :=
begin
  simp only [Theory.DLO, set.union_insert, set.union_singleton, Theory.model_iff,
    set.mem_insert_iff, forall_eq_or_imp, realize_no_top_order, realize_no_bot_order,
    realize_densely_ordered, true_and],
  rw ← Theory.model_iff,
  apply_instance,
end

end language
end first_order
