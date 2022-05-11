import data.real.basic

open_locale classical

/-
Theoretical negations.

This file is for people interested in logic who want to fully understand
negations.

Here we don't use `contrapose` or `push_neg`. The goal is to prove lemmas
that are used by those tactics. Of course we can use
`exfalso`, `by_contradiction` and `by_cases`.

If this doesn't sound like fun then skip ahead to the next file.
-/

section negation_prop

variables P Q : Prop

-- 0055
example : (P → Q) ↔ (¬ Q → ¬ P) :=
begin
  split, intro h, intro j, by_contradiction hyp, exact j (h hyp),
  intro h, intro p, by_contradiction qn, exact h qn p,
end

-- 0056
lemma non_imp (P Q : Prop) : ¬ (P → Q) ↔ P ∧ ¬ Q :=
begin
  split, intro h, split, by_contradiction np,
  have k : P → Q, intro p, exfalso, exact np p, exact h k,
  intro q, have k : P → Q, intro p, exact q, exact h k,
  intro h, cases h with p qn, intro j, exact qn (j p),
end

-- In the next one, let's use the axiom
-- propext {P Q : Prop} : (P ↔ Q) → P = Q

-- 0057
example (P : Prop) : ¬ P ↔ P = false :=
begin
  split, intro h, apply propext, split, intro j, exact h j, intro p, exfalso, exact p,
  intro h, intro j, rw h at j, exact j,
end

end negation_prop

section negation_quantifiers
variables (X : Type) (P : X → Prop)

-- 0058
example : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x :=
begin
  split, intro h, by_contradiction hyp, apply h, intro x, by_contradiction j, exact hyp ⟨x,j⟩,
  intro h, intro hyp, cases h with x hx, exact hx (hyp x),
end

-- 0059
example : ¬ (∃ x, P x) ↔ ∀ x, ¬ P x :=
begin
  split, intros h x hx, exact h ⟨x, hx⟩,
  intros h j, cases j with x hx, exact h x hx, 
end

-- 0060
example (P : ℝ → Prop) : ¬ (∃ ε > 0, P ε) ↔ ∀ ε > 0, ¬ P ε :=
begin
  split, intros h ε ε_pos hε, apply h, use [ε,ε_pos,hε],
  intros h j, rcases j with ⟨ε,ε_pos,hε⟩, exact h ε ε_pos hε,  
end

-- 0061
example (P : ℝ → Prop) : ¬ (∀ x > 0, P x) ↔ ∃ x > 0, ¬ P x :=
begin
  split, intro h, by_contradiction hyp, apply h, intros x x_pos, by_contradiction hp,
  apply hyp, use [x,x_pos,hp],
  intros h j, rcases h with ⟨x,hx,px⟩, exact px (j x hx), 
end

end negation_quantifiers

