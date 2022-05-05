/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
import data.list.prod_sigma
import logic.equiv.fin
import model_theory.language_map

/-!
# Basics on First-Order Syntax
This file defines first-order terms, formulas, sentences, and theories in a style inspired by the
[Flypitch project](https://flypitch.github.io/).

## Main Definitions
* A `first_order.language.term` is defined so that `L.term α` is the type of `L`-terms with free
  variables indexed by `α`.
* A `first_order.language.formula` is defined so that `L.formula α` is the type of `L`-formulas with
  free variables indexed by `α`.
* A `first_order.language.sentence` is a formula with no free variables.
* A `first_order.language.Theory` is a set of sentences.
* The variables of terms and formulas can be relabelled with `first_order.language.term.relabel`,
`first_order.language.bounded_formula.relabel`, and `first_order.language.formula.relabel`.
* `first_order.language.bounded_formula.cast_le` adds more `fin`-indexed variables.
* `first_order.language.bounded_formula.lift_at` raises the indexes of the `fin`-indexed variables
above a particular index.
* `first_order.language.term.subst` and `first_order.language.bounded_formula.subst` substitute
variables with given terms.
* Language maps can act on syntactic objects with functions such as
`first_order.language.Lhom.on_formula`.

## Implementation Notes
* Formulas use a modified version of de Bruijn variables. Specifically, a `L.bounded_formula α n`
is a formula with some variables indexed by a type `α`, which cannot be quantified over, and some
indexed by `fin n`, which can. For any `φ : L.bounded_formula α (n + 1)`, we define the formula
`∀' φ : L.bounded_formula α n` by universally quantifying over the variable indexed by
`n : fin (n + 1)`.

## References
For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
[flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
the continuum hypothesis*][flypitch_itp]

-/

universes u v w u' v'

namespace first_order
namespace language

variables (L : language.{u v}) {L' : language}
variables {M : Type w} {N P : Type*} [L.Structure M] [L.Structure N] [L.Structure P]
variables {α : Type u'} {β : Type v'}
open_locale first_order
open Structure fin

/-- A term on `α` is either a variable indexed by an element of `α`
  or a function symbol applied to simpler terms. -/
inductive term (α : Type u') : Type (max u u')
| var {} : ∀ (a : α), term
| func {} : ∀ {l : ℕ} (f : L.functions l) (ts : fin l → term), term
export term

variable {L}

namespace term

open finset

/-- The `finset` of variables used in a given term. -/
@[simp] def var_finset [decidable_eq α] : L.term α → finset α
| (var i) := {i}
| (func f ts) := univ.bUnion (λ i, (ts i).var_finset)

/-- The `finset` of variables from the left side of a sum used in a given term. -/
@[simp] def var_finset_left [decidable_eq α] : L.term (α ⊕ β) → finset α
| (var (sum.inl i)) := {i}
| (var (sum.inr i)) := ∅
| (func f ts) := univ.bUnion (λ i, (ts i).var_finset_left)

/-- Relabels a term's variables along a particular function. -/
@[simp] def relabel (g : α → β) : L.term α → L.term β
| (var i) := var (g i)
| (func f ts) := func f (λ i, (ts i).relabel)

/-- Restricts a term to use only a set of the given variables. -/
def restrict_var [decidable_eq α] : Π (t : L.term α) (f : t.var_finset → β), L.term β
| (var a) f := var (f ⟨a, mem_singleton_self a⟩)
| (func F ts) f := func F (λ i, (ts i).restrict_var
  (f ∘ (set.inclusion (subset_bUnion_of_mem _ (mem_univ i)))))

/-- Restricts a term to use only a set of the given variables on the left side of a sum. -/
def restrict_var_left [decidable_eq α] {γ : Type*} :
  Π (t : L.term (α ⊕ γ)) (f : t.var_finset_left → β), L.term (β ⊕ γ)
| (var (sum.inl a)) f := var (sum.inl (f ⟨a, mem_singleton_self a⟩))
| (var (sum.inr a)) f := var (sum.inr a)
| (func F ts) f := func F (λ i, (ts i).restrict_var_left
  (f ∘ (set.inclusion (subset_bUnion_of_mem _ (mem_univ i)))))

end term

/-- The representation of a constant symbol as a term. -/
def constants.term (c : L.constants) : (L.term α) :=
func c default

/-- Applies a unary function to a term. -/
def functions.apply₁ (f : L.functions 1) (t : L.term α) : L.term α := func f ![t]

/-- Applies a binary function to two terms. -/
def functions.apply₂ (f : L.functions 2) (t₁ t₂ : L.term α) : L.term α := func f ![t₁, t₂]

namespace term

instance inhabited_of_constant [inhabited L.constants] : inhabited (L.term α) :=
⟨(default : L.constants).term⟩

/-- Raises all of the `fin`-indexed variables of a term greater than or equal to `m` by `n'`. -/
def lift_at {n : ℕ} (n' m : ℕ) : L.term (α ⊕ fin n) → L.term (α ⊕ fin (n + n')) :=
relabel (sum.map id (λ i, if ↑i < m then fin.cast_add n' i else fin.add_nat n' i))

/-- Substitutes the variables in a given term with terms. -/
@[simp] def subst : L.term α → (α → L.term β) → L.term β
| (var a) tf := tf a
| (func f ts) tf := (func f (λ i, (ts i).subst tf))

end term

localized "prefix `&`:max := first_order.language.term.var ∘ sum.inr" in first_order

namespace Lhom

/-- Maps a term's symbols along a language map. -/
@[simp] def on_term (φ : L →ᴸ L') : L.term α → L'.term α
| (var i) := var i
| (func f ts) := func (φ.on_function f) (λ i, on_term (ts i))

@[simp] lemma id_on_term :
  ((Lhom.id L).on_term : L.term α → L.term α) = id :=
begin
  ext t,
  induction t with _ _ _ _ ih,
  { refl },
  { simp_rw [on_term, ih],
    refl, },
end

@[simp] lemma comp_on_term {L'' : language} (φ : L' →ᴸ L'') (ψ : L →ᴸ L') :
  ((φ.comp ψ).on_term : L.term α → L''.term α) = φ.on_term ∘ ψ.on_term :=
begin
  ext t,
  induction t with _ _ _ _ ih,
  { refl },
  { simp_rw [on_term, ih],
    refl, },
end

end Lhom

/-- Maps a term's symbols along a language equivalence. -/
@[simps] def Lequiv.on_term (φ : L ≃ᴸ L') : L.term α ≃ L'.term α :=
{ to_fun := φ.to_Lhom.on_term,
  inv_fun := φ.inv_Lhom.on_term,
  left_inv := by rw [function.left_inverse_iff_comp, ← Lhom.comp_on_term, φ.left_inv,
    Lhom.id_on_term],
  right_inv := by rw [function.right_inverse_iff_comp, ← Lhom.comp_on_term, φ.right_inv,
    Lhom.id_on_term] }

variables (L) (α)
/-- `bounded_formula α n` is the type of formulas with free variables indexed by `α` and up to `n`
  additional free variables. -/
inductive bounded_formula : ℕ → Type (max u v u')
| falsum {} {n} : bounded_formula n
| equal {n} (t₁ t₂ : L.term (α ⊕ fin n)) : bounded_formula n
| rel {n l : ℕ} (R : L.relations l) (ts : fin l → L.term (α ⊕ fin n)) : bounded_formula n
| imp {n} (f₁ f₂ : bounded_formula n) : bounded_formula n
| all {n} (f : bounded_formula (n+1)) : bounded_formula n

/-- `formula α` is the type of formulas with all free variables indexed by `α`. -/
@[reducible] def formula := L.bounded_formula α 0

/-- A sentence is a formula with no free variables. -/
@[reducible] def sentence := L.formula empty

/-- A theory is a set of sentences. -/
@[reducible] def Theory := set L.sentence

variables {L} {α} {n : ℕ}

/-- Applies a relation to terms as a bounded formula. -/
def relations.bounded_formula {l : ℕ} (R : L.relations n) (ts : fin n → L.term (α ⊕ fin l)) :
  L.bounded_formula α l := bounded_formula.rel R ts

/-- Applies a unary relation to a term as a bounded formula. -/
def relations.bounded_formula₁ (r : L.relations 1) (t : L.term (α ⊕ fin n)) :
  L.bounded_formula α n :=
r.bounded_formula ![t]

/-- Applies a binary relation to two terms as a bounded formula. -/
def relations.bounded_formula₂ (r : L.relations 2) (t₁ t₂ : L.term (α ⊕ fin n)) :
  L.bounded_formula α n :=
r.bounded_formula ![t₁, t₂]

/-- The equality of two terms as a bounded formula. -/
def term.bd_equal (t₁ t₂ : L.term (α ⊕ fin n)) : (L.bounded_formula α n) :=
bounded_formula.equal t₁ t₂

/-- Applies a relation to terms as a bounded formula. -/
def relations.formula (R : L.relations n) (ts : fin n → L.term α) :
  L.formula α := R.bounded_formula (λ i, (ts i).relabel sum.inl)

/-- Applies a unary relation to a term as a formula. -/
def relations.formula₁ (r : L.relations 1) (t : L.term α) :
  L.formula α :=
r.formula ![t]

/-- Applies a binary relation to two terms as a formula. -/
def relations.formula₂ (r : L.relations 2) (t₁ t₂ : L.term α) :
  L.formula α :=
r.formula ![t₁, t₂]

/-- The equality of two terms as a first-order formula. -/
def term.equal (t₁ t₂ : L.term α) : (L.formula α) :=
(t₁.relabel sum.inl).bd_equal (t₂.relabel sum.inl)

namespace bounded_formula

instance : inhabited (L.bounded_formula α n) :=
⟨falsum⟩

instance : has_bot (L.bounded_formula α n) := ⟨falsum⟩

/-- The negation of a bounded formula is also a bounded formula. -/
@[pattern] protected def not (φ : L.bounded_formula α n) : L.bounded_formula α n := φ.imp ⊥

/-- Puts an `∃` quantifier on a bounded formula. -/
@[pattern] protected def ex (φ : L.bounded_formula α (n + 1)) : L.bounded_formula α n :=
  φ.not.all.not

instance : has_top (L.bounded_formula α n) := ⟨bounded_formula.not ⊥⟩

instance : has_inf (L.bounded_formula α n) := ⟨λ f g, (f.imp g.not).not⟩

instance : has_sup (L.bounded_formula α n) := ⟨λ f g, f.not.imp g⟩

/-- The biimplication between two bounded formulas. -/
protected def iff (φ ψ : L.bounded_formula α n) := φ.imp ψ ⊓ ψ.imp φ

open finset

/-- The `finset` of variables used in a given formula. -/
@[simp] def free_var_finset [decidable_eq α] :
  ∀ {n}, L.bounded_formula α n → finset α
| n falsum := ∅
| n (equal t₁ t₂) := t₁.var_finset_left ∪ t₂.var_finset_left
| n (rel R ts) := univ.bUnion (λ i, (ts i).var_finset_left)
| n (imp f₁ f₂) := f₁.free_var_finset ∪ f₂.free_var_finset
| n (all f) := f.free_var_finset

/-- Casts `L.bounded_formula α m` as `L.bounded_formula α n`, where `m ≤ n`. -/
def cast_le : ∀ {m n : ℕ} (h : m ≤ n), L.bounded_formula α m → L.bounded_formula α n
| m n h falsum := falsum
| m n h (equal t₁ t₂) := (t₁.relabel (sum.map id (fin.cast_le h))).bd_equal
    (t₂.relabel (sum.map id (fin.cast_le h)))
| m n h (rel R ts) := R.bounded_formula (term.relabel (sum.map id (fin.cast_le h)) ∘ ts)
| m n h (imp f₁ f₂) := (f₁.cast_le h).imp (f₂.cast_le h)
| m n h (all f) := (f.cast_le (add_le_add_right h 1)).all

/-- A function to help relabel the variables in bounded formulas. -/
def relabel_aux (g : α → (β ⊕ fin n)) (k : ℕ) :
  α ⊕ fin k → β ⊕ fin (n + k) :=
(sum.map id fin_sum_fin_equiv) ∘ (equiv.sum_assoc _ _ _) ∘ (sum.map g id)

@[simp] lemma sum_elim_comp_relabel_aux {m : ℕ} {g : α → (β ⊕ fin n)}
  {v : β → M} {xs : fin (n + m) → M} :
  sum.elim v xs ∘ relabel_aux g m =
    sum.elim (sum.elim v (xs ∘ cast_add m) ∘ g) (xs ∘ nat_add n) :=
begin
  ext x,
  cases x,
  { simp only [bounded_formula.relabel_aux, function.comp_app, sum.map_inl, sum.elim_inl],
    cases g x with l r;
    simp },
  { simp [bounded_formula.relabel_aux] }
end

/-- Relabels a bounded formula's variables along a particular function. -/
def relabel (g : α → (β ⊕ fin n)) :
  ∀ {k : ℕ}, L.bounded_formula α k → L.bounded_formula β (n + k)
| k falsum := falsum
| k (equal t₁ t₂) := (t₁.relabel (relabel_aux g k)).bd_equal (t₂.relabel (relabel_aux g k))
| k (rel R ts) := R.bounded_formula (term.relabel (relabel_aux g k) ∘ ts)
| k (imp f₁ f₂) := f₁.relabel.imp f₂.relabel
| k (all f) := f.relabel.all

/-- Restricts a bounded formula to only use a particular set of free variables. -/
def restrict_free_var [decidable_eq α] : Π {n : ℕ} (φ : L.bounded_formula α n)
  (f : φ.free_var_finset → β), L.bounded_formula β n
| n falsum f := falsum
| n (equal t₁ t₂) f := equal
  (t₁.restrict_var_left (f ∘ (set.inclusion (subset_union_left _ _))))
  (t₂.restrict_var_left (f ∘ (set.inclusion (subset_union_right _ _))))
| n (rel R ts) f := rel R (λ i, (ts i).restrict_var_left
  (f ∘ set.inclusion (subset_bUnion_of_mem _ (mem_univ i))))
| n (imp φ₁ φ₂) f :=
  (φ₁.restrict_free_var (f ∘ (set.inclusion (subset_union_left _ _)))).imp
  (φ₂.restrict_free_var (f ∘ (set.inclusion (subset_union_right _ _))))
| n (all φ) f := (φ.restrict_free_var f).all

/-- Places universal quantifiers on all extra variables of a bounded formula. -/
def alls : ∀ {n}, L.bounded_formula α n → L.formula α
| 0 φ := φ
| (n + 1) φ := φ.all.alls

/-- Places existential quantifiers on all extra variables of a bounded formula. -/
def exs : ∀ {n}, L.bounded_formula α n → L.formula α
| 0 φ := φ
| (n + 1) φ := φ.ex.exs

/-- Raises all of the `fin`-indexed variables of a formula greater than or equal to `m` by `n'`. -/
def lift_at : ∀ {n : ℕ} (n' m : ℕ), L.bounded_formula α n → L.bounded_formula α (n + n')
| n n' m falsum := falsum
| n n' m (equal t₁ t₂) := (t₁.lift_at n' m).bd_equal (t₂.lift_at n' m)
| n n' m (rel R ts) := R.bounded_formula (term.lift_at n' m ∘ ts)
| n n' m (imp f₁ f₂) := (f₁.lift_at n' m).imp (f₂.lift_at n' m)
| n n' m (all f) := ((f.lift_at n' m).cast_le (by rw [add_assoc, add_comm 1, ← add_assoc])).all

/-- Substitutes the variables in a given formula with terms. -/
@[simp] def subst : ∀ {n : ℕ}, L.bounded_formula α n → (α → L.term β) → L.bounded_formula β n
| n falsum tf := falsum
| n (equal t₁ t₂) tf := equal (t₁.subst (sum.elim (term.relabel sum.inl ∘ tf) (var ∘ sum.inr)))
  (t₂.subst (sum.elim (term.relabel sum.inl ∘ tf) (var ∘ sum.inr)))
| n (rel R ts) tf := rel R
  (λ i, (ts i).subst (sum.elim (term.relabel sum.inl ∘ tf) (var ∘ sum.inr)))
| n (imp φ₁ φ₂) tf := (φ₁.subst tf).imp (φ₂.subst tf)
| n (all φ) tf := (φ.subst tf).all

variables {l : ℕ} {φ ψ : L.bounded_formula α l} {θ : L.bounded_formula α l.succ}
variables {v : α → M} {xs : fin l → M}

/-- An atomic formula is either equality or a relation symbol applied to terms.
  Note that `⊥` and `⊤` are not considered atomic in this convention. -/
inductive is_atomic : L.bounded_formula α n → Prop
| equal (t₁ t₂ : L.term (α ⊕ fin n)) : is_atomic (bd_equal t₁ t₂)
| rel {l : ℕ} (R : L.relations l) (ts : fin l → L.term (α ⊕ fin n)) :
    is_atomic (R.bounded_formula ts)

lemma not_all_is_atomic (φ : L.bounded_formula α (n + 1)) :
  ¬ φ.all.is_atomic :=
λ con, by cases con

lemma not_ex_is_atomic (φ : L.bounded_formula α (n + 1)) :
  ¬ φ.ex.is_atomic :=
λ con, by cases con

lemma is_atomic.relabel {m : ℕ} {φ : L.bounded_formula α m} (h : φ.is_atomic)
  (f : α → β ⊕ (fin n)) :
  (φ.relabel f).is_atomic :=
is_atomic.rec_on h (λ _ _, is_atomic.equal _ _) (λ _ _ _, is_atomic.rel _ _)

lemma is_atomic.lift_at {k m : ℕ} (h : is_atomic φ) : (φ.lift_at k m).is_atomic :=
is_atomic.rec_on h (λ _ _, is_atomic.equal _ _) (λ _ _ _, is_atomic.rel _ _)

lemma is_atomic.cast_le {h : l ≤ n} (hφ : is_atomic φ) :
  (φ.cast_le h).is_atomic :=
is_atomic.rec_on hφ (λ _ _, is_atomic.equal _ _) (λ _ _ _, is_atomic.rel _ _)

/-- A quantifier-free formula is a formula defined without quantifiers. These are all equivalent
to boolean combinations of atomic formulas. -/
inductive is_qf : L.bounded_formula α n → Prop
| falsum : is_qf falsum
| of_is_atomic {φ} (h : is_atomic φ) : is_qf φ
| imp {φ₁ φ₂} (h₁ : is_qf φ₁) (h₂ : is_qf φ₂) : is_qf (φ₁.imp φ₂)

lemma is_atomic.is_qf {φ : L.bounded_formula α n} : is_atomic φ → is_qf φ :=
is_qf.of_is_atomic

lemma is_qf_bot : is_qf (⊥ : L.bounded_formula α n) :=
is_qf.falsum

lemma is_qf.not {φ : L.bounded_formula α n} (h : is_qf φ) :
  is_qf φ.not :=
h.imp is_qf_bot

lemma is_qf.relabel {m : ℕ} {φ : L.bounded_formula α m} (h : φ.is_qf)
  (f : α → β ⊕ (fin n)) :
  (φ.relabel f).is_qf :=
is_qf.rec_on h is_qf_bot (λ _ h, (h.relabel f).is_qf) (λ _ _ _ _ h1 h2, h1.imp h2)

lemma is_qf.lift_at {k m : ℕ} (h : is_qf φ) : (φ.lift_at k m).is_qf :=
is_qf.rec_on h is_qf_bot (λ _ ih, ih.lift_at.is_qf) (λ _ _ _ _ ih1 ih2, ih1.imp ih2)

lemma is_qf.cast_le {h : l ≤ n} (hφ : is_qf φ) :
  (φ.cast_le h).is_qf :=
is_qf.rec_on hφ is_qf_bot (λ _ ih, ih.cast_le.is_qf) (λ _ _ _ _ ih1 ih2, ih1.imp ih2)

lemma not_all_is_qf (φ : L.bounded_formula α (n + 1)) :
  ¬ φ.all.is_qf :=
λ con, begin
  cases con with _ con,
  exact (φ.not_all_is_atomic con),
end

lemma not_ex_is_qf (φ : L.bounded_formula α (n + 1)) :
  ¬ φ.ex.is_qf :=
λ con, begin
  cases con with _ con _ _ con,
  { exact (φ.not_ex_is_atomic con) },
  { exact not_all_is_qf _ con }
end

/-- Indicates that a bounded formula is in prenex normal form - that is, it consists of quantifiers
  applied to a quantifier-free formula. -/
inductive is_prenex : ∀ {n}, L.bounded_formula α n → Prop
| of_is_qf {n} {φ : L.bounded_formula α n} (h : is_qf φ) : is_prenex φ
| all {n} {φ : L.bounded_formula α (n + 1)} (h : is_prenex φ) : is_prenex φ.all
| ex {n} {φ : L.bounded_formula α (n + 1)} (h : is_prenex φ) : is_prenex φ.ex

lemma is_qf.is_prenex {φ : L.bounded_formula α n} : is_qf φ → is_prenex φ :=
is_prenex.of_is_qf

lemma is_atomic.is_prenex {φ : L.bounded_formula α n} (h : is_atomic φ) : is_prenex φ :=
h.is_qf.is_prenex

lemma is_prenex.induction_on_all_not {P : ∀ {n}, L.bounded_formula α n → Prop}
  {φ : L.bounded_formula α n}
  (h : is_prenex φ)
  (hq : ∀ {m} {ψ : L.bounded_formula α m}, ψ.is_qf → P ψ)
  (ha : ∀ {m} {ψ : L.bounded_formula α (m + 1)}, P ψ → P ψ.all)
  (hn : ∀ {m} {ψ : L.bounded_formula α m}, P ψ → P ψ.not) :
  P φ :=
is_prenex.rec_on h (λ _ _, hq) (λ _ _ _, ha) (λ _ _ _ ih, hn (ha (hn ih)))

lemma is_prenex.relabel {m : ℕ} {φ : L.bounded_formula α m} (h : φ.is_prenex)
  (f : α → β ⊕ (fin n)) :
  (φ.relabel f).is_prenex :=
is_prenex.rec_on h (λ _ _ h, (h.relabel f).is_prenex) (λ _ _ _ h, h.all) (λ _ _ _ h, h.ex)

lemma is_prenex.cast_le (hφ : is_prenex φ) :
  ∀ {n} {h : l ≤ n}, (φ.cast_le h).is_prenex :=
is_prenex.rec_on hφ
  (λ _ _ ih _ _, ih.cast_le.is_prenex)
  (λ _ _ _ ih _ _, ih.all)
  (λ _ _ _ ih _ _, ih.ex)

lemma is_prenex.lift_at {k m : ℕ} (h : is_prenex φ) : (φ.lift_at k m).is_prenex :=
is_prenex.rec_on h
  (λ _ _ ih, ih.lift_at.is_prenex)
  (λ _ _ _ ih, ih.cast_le.all)
  (λ _ _ _ ih, ih.cast_le.ex)

/-- An auxiliary operation to `first_order.language.bounded_formula.to_prenex`.
  If `φ` is quantifier-free and `ψ` is in prenex normal form, then `φ.to_prenex_imp_right ψ`
  is a prenex normal form for `φ.imp ψ`. -/
def to_prenex_imp_right :
  ∀ {n}, L.bounded_formula α n → L.bounded_formula α n → L.bounded_formula α n
| n φ (bounded_formula.ex ψ) := ((φ.lift_at 1 n).to_prenex_imp_right ψ).ex
| n φ (all ψ) := ((φ.lift_at 1 n).to_prenex_imp_right ψ).all
| n φ ψ := φ.imp ψ

lemma is_qf.to_prenex_imp_right {φ : L.bounded_formula α n} :
  Π {ψ : L.bounded_formula α n}, is_qf ψ → (φ.to_prenex_imp_right ψ = φ.imp ψ)
| _ is_qf.falsum := rfl
| _ (is_qf.of_is_atomic (is_atomic.equal _ _)) := rfl
| _ (is_qf.of_is_atomic (is_atomic.rel _ _)) := rfl
| _ (is_qf.imp is_qf.falsum _) := rfl
| _ (is_qf.imp (is_qf.of_is_atomic (is_atomic.equal _ _)) _) := rfl
| _ (is_qf.imp (is_qf.of_is_atomic (is_atomic.rel _ _)) _) := rfl
| _ (is_qf.imp (is_qf.imp _ _) _) := rfl

lemma is_prenex_to_prenex_imp_right {φ ψ : L.bounded_formula α n}
  (hφ : is_qf φ) (hψ : is_prenex ψ) :
  is_prenex (φ.to_prenex_imp_right ψ) :=
begin
  induction hψ with _ _ hψ _ _ _ ih1 _ _ _ ih2,
  { rw hψ.to_prenex_imp_right,
    exact (hφ.imp hψ).is_prenex },
  { exact (ih1 hφ.lift_at).all },
  { exact (ih2 hφ.lift_at).ex }
end

/-- An auxiliary operation to `first_order.language.bounded_formula.to_prenex`.
  If `φ` and `ψ` are in prenex normal form, then `φ.to_prenex_imp ψ`
  is a prenex normal form for `φ.imp ψ`. -/
def to_prenex_imp :
  ∀ {n}, L.bounded_formula α n → L.bounded_formula α n → L.bounded_formula α n
| n (bounded_formula.ex φ) ψ := (φ.to_prenex_imp (ψ.lift_at 1 n)).all
| n (all φ) ψ := (φ.to_prenex_imp (ψ.lift_at 1 n)).ex
| _ φ ψ := φ.to_prenex_imp_right ψ

lemma is_qf.to_prenex_imp : Π {φ ψ : L.bounded_formula α n}, φ.is_qf →
  φ.to_prenex_imp ψ = φ.to_prenex_imp_right ψ
| _ _ is_qf.falsum := rfl
| _ _ (is_qf.of_is_atomic (is_atomic.equal _ _)) := rfl
| _ _ (is_qf.of_is_atomic (is_atomic.rel _ _)) := rfl
| _ _ (is_qf.imp is_qf.falsum _) := rfl
| _ _ (is_qf.imp (is_qf.of_is_atomic (is_atomic.equal _ _)) _) := rfl
| _ _ (is_qf.imp (is_qf.of_is_atomic (is_atomic.rel _ _)) _) := rfl
| _ _ (is_qf.imp (is_qf.imp _ _) _) := rfl

lemma is_prenex_to_prenex_imp {φ ψ : L.bounded_formula α n}
  (hφ : is_prenex φ) (hψ : is_prenex ψ) :
  is_prenex (φ.to_prenex_imp ψ) :=
begin
  induction hφ with _ _ hφ _ _ _ ih1 _ _ _ ih2,
  { rw hφ.to_prenex_imp,
    exact is_prenex_to_prenex_imp_right hφ hψ },
  { exact (ih1 hψ.lift_at).ex },
  { exact (ih2 hψ.lift_at).all }
end

/-- For any bounded formula `φ`, `φ.to_prenex` is a semantically-equivalent formula in prenex normal
  form. -/
def to_prenex : ∀ {n}, L.bounded_formula α n → L.bounded_formula α n
| _ falsum        := ⊥
| _ (equal t₁ t₂) := t₁.bd_equal t₂
| _ (rel R ts)    := rel R ts
| _ (imp f₁ f₂)   := f₁.to_prenex.to_prenex_imp f₂.to_prenex
| _ (all f)       := f.to_prenex.all

lemma to_prenex_is_prenex (φ : L.bounded_formula α n) :
  φ.to_prenex.is_prenex :=
bounded_formula.rec_on φ
  (λ _, is_qf_bot.is_prenex)
  (λ _ _ _, (is_atomic.equal _ _).is_prenex)
  (λ _ _ _ _, (is_atomic.rel _ _).is_prenex)
  (λ _ _ _ h1 h2, is_prenex_to_prenex_imp h1 h2)
  (λ _ _, is_prenex.all)

end bounded_formula

namespace Lhom
open bounded_formula

/-- Maps a bounded formula's symbols along a language map. -/
@[simp] def on_bounded_formula (g : L →ᴸ L') :
  ∀ {k : ℕ}, L.bounded_formula α k → L'.bounded_formula α k
| k falsum := falsum
| k (equal t₁ t₂) := (g.on_term t₁).bd_equal (g.on_term t₂)
| k (rel R ts) := (g.on_relation R).bounded_formula (g.on_term ∘ ts)
| k (imp f₁ f₂) := (on_bounded_formula f₁).imp (on_bounded_formula f₂)
| k (all f) := (on_bounded_formula f).all

@[simp] lemma id_on_bounded_formula :
  ((Lhom.id L).on_bounded_formula : L.bounded_formula α n → L.bounded_formula α n) = id :=
begin
  ext f,
  induction f with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3,
  { refl },
  { rw [on_bounded_formula, Lhom.id_on_term, id.def, id.def, id.def, bd_equal] },
  { rw [on_bounded_formula, Lhom.id_on_term],
    refl, },
  { rw [on_bounded_formula, ih1, ih2, id.def, id.def, id.def] },
  { rw [on_bounded_formula, ih3, id.def, id.def] }
end

@[simp] lemma comp_on_bounded_formula {L'' : language} (φ : L' →ᴸ L'') (ψ : L →ᴸ L') :
  ((φ.comp ψ).on_bounded_formula : L.bounded_formula α n → L''.bounded_formula α n) =
    φ.on_bounded_formula ∘ ψ.on_bounded_formula :=
begin
  ext f,
  induction f with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3,
  { refl },
  { simp only [on_bounded_formula, comp_on_term, function.comp_app],
    refl, },
  { simp only [on_bounded_formula, comp_on_relation, comp_on_term, function.comp_app],
    refl },
  { simp only [on_bounded_formula, function.comp_app, ih1, ih2, eq_self_iff_true, and_self], },
  { simp only [ih3, on_bounded_formula, function.comp_app] }
end

/-- Maps a formula's symbols along a language map. -/
def on_formula (g : L →ᴸ L') : L.formula α → L'.formula α :=
g.on_bounded_formula

/-- Maps a sentence's symbols along a language map. -/
def on_sentence (g : L →ᴸ L') : L.sentence → L'.sentence :=
g.on_formula

/-- Maps a theory's symbols along a language map. -/
def on_Theory (g : L →ᴸ L') (T : L.Theory) : L'.Theory :=
g.on_sentence '' T

@[simp] lemma mem_on_Theory {g : L →ᴸ L'} {T : L.Theory} {φ : L'.sentence} :
  φ ∈ g.on_Theory T ↔ ∃ φ₀, φ₀ ∈ T ∧ g.on_sentence φ₀ = φ :=
set.mem_image _ _ _

end Lhom

namespace Lequiv

/-- Maps a bounded formula's symbols along a language equivalence. -/
@[simps] def on_bounded_formula (φ : L ≃ᴸ L') :
  L.bounded_formula α n ≃ L'.bounded_formula α n :=
{ to_fun := φ.to_Lhom.on_bounded_formula,
  inv_fun := φ.inv_Lhom.on_bounded_formula,
  left_inv := by rw [function.left_inverse_iff_comp, ← Lhom.comp_on_bounded_formula, φ.left_inv,
    Lhom.id_on_bounded_formula],
  right_inv := by rw [function.right_inverse_iff_comp, ← Lhom.comp_on_bounded_formula, φ.right_inv,
    Lhom.id_on_bounded_formula] }

lemma on_bounded_formula_symm (φ : L ≃ᴸ L') :
  (φ.on_bounded_formula.symm : L'.bounded_formula α n ≃ L.bounded_formula α n) =
    φ.symm.on_bounded_formula :=
rfl

/-- Maps a formula's symbols along a language equivalence. -/
def on_formula (φ : L ≃ᴸ L') :
  L.formula α ≃ L'.formula α :=
φ.on_bounded_formula

@[simp] lemma on_formula_apply (φ : L ≃ᴸ L') :
  (φ.on_formula : L.formula α → L'.formula α) = φ.to_Lhom.on_formula :=
rfl

@[simp] lemma on_formula_symm (φ : L ≃ᴸ L') :
  (φ.on_formula.symm : L'.formula α ≃ L.formula α) = φ.symm.on_formula :=
rfl

/-- Maps a sentence's symbols along a language equivalence. -/
@[simps] def on_sentence (φ : L ≃ᴸ L') :
  L.sentence ≃ L'.sentence :=
φ.on_formula

end Lequiv

localized "infix ` =' `:88 := first_order.language.term.bd_equal" in first_order
  -- input \~- or \simeq
localized "infixr ` ⟹ `:62 := first_order.language.bounded_formula.imp" in first_order
  -- input \==>
localized "prefix `∀'`:110 := first_order.language.bounded_formula.all" in first_order
localized "prefix `∼`:max := first_order.language.bounded_formula.not" in first_order
  -- input \~, the ASCII character ~ has too low precedence
localized "infix ` ⇔ `:61 := first_order.language.bounded_formula.iff" in first_order -- input \<=>
localized "prefix `∃'`:110 := first_order.language.bounded_formula.ex" in first_order -- input \ex

namespace formula

/-- Relabels a formula's variables along a particular function. -/
def relabel (g : α → β) : L.formula α → L.formula β :=
@bounded_formula.relabel _ _ _ 0 (sum.inl ∘ g) 0

/-- The graph of a function as a first-order formula. -/
def graph (f : L.functions n) : L.formula (fin (n + 1)) :=
equal (var 0) (func f (λ i, var i.succ))

/-- The negation of a formula. -/
protected def not (φ : L.formula α) : L.formula α := φ.not

/-- The implication between formulas, as a formula. -/
protected def imp : L.formula α → L.formula α → L.formula α := bounded_formula.imp

/-- The biimplication between formulas, as a formula. -/
protected def iff (φ ψ : L.formula α) : L.formula α := φ.iff ψ

lemma is_atomic_graph (f : L.functions n) : (graph f).is_atomic :=
bounded_formula.is_atomic.equal _ _

end formula

namespace relations

variable (r : L.relations 2)

/-- The sentence indicating that a basic relation symbol is reflexive. -/
protected def reflexive : L.sentence := ∀' r.bounded_formula₂ &0 &0

/-- The sentence indicating that a basic relation symbol is irreflexive. -/
protected def irreflexive : L.sentence := ∀' ∼ (r.bounded_formula₂ &0 &0)

/-- The sentence indicating that a basic relation symbol is symmetric. -/
protected def symmetric : L.sentence := ∀' ∀' (r.bounded_formula₂ &0 &1 ⟹ r.bounded_formula₂ &1 &0)

/-- The sentence indicating that a basic relation symbol is antisymmetric. -/
protected def antisymmetric : L.sentence :=
  ∀' ∀' (r.bounded_formula₂ &0 &1 ⟹ (r.bounded_formula₂ &1 &0 ⟹ term.bd_equal &0 &1))

/-- The sentence indicating that a basic relation symbol is transitive. -/
protected def transitive : L.sentence :=
  ∀' ∀' ∀' (r.bounded_formula₂ &0 &1 ⟹ r.bounded_formula₂ &1 &2 ⟹ r.bounded_formula₂ &0 &2)

/-- The sentence indicating that a basic relation symbol is total. -/
protected def total : L.sentence :=
  ∀' ∀' (r.bounded_formula₂ &0 &1 ⊔ r.bounded_formula₂ &1 &0)

end relations

section cardinality

variable (L)

/-- A sentence indicating that a structure has `n` distinct elements. -/
protected def sentence.card_ge (n) : L.sentence :=
(((((list.fin_range n).product (list.fin_range n)).filter (λ ij : _ × _, ij.1 ≠ ij.2)).map
  (λ (ij : _ × _), ∼ ((& ij.1).bd_equal (& ij.2)))).foldr (⊓) ⊤).exs

/-- A theory indicating that a structure is infinite. -/
def infinite_theory : L.Theory := set.range (sentence.card_ge L)

/-- A theory that indicates a structure is nonempty. -/
def nonempty_theory : L.Theory := {sentence.card_ge L 1}

end cardinality

end language
end first_order
