import tuto_lib

set_option pp.beta true
set_option pp.coercions false

/-
This is the final file in the series. Here we use everything covered
in previous files to prove a couple of famous theorems from 
elementary real analysis. Of course they all have more general versions
in mathlib.

As usual, keep in mind the following:

  abs_le {x y : ℝ} : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y

  ge_max_iff (p q r) : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q

  le_max_left p q : p ≤ max p q

  le_max_right p q : q ≤ max p q

as well as a lemma from the previous file:

  le_of_le_add_all : (∀ ε > 0, y ≤ x + ε) →  y ≤ x

Let's start with a variation on a known exercise.
-/

-- 0071
lemma le_lim {x y : ℝ} {u : ℕ → ℝ} (hu : seq_limit u x)
  (ineg : ∃ N, ∀ n ≥ N, y ≤ u n) : y ≤ x :=
begin
  apply le_of_le_add_all, intros ε ε_pos,
  cases ineg with N hN, cases hu ε ε_pos with N' hN',
  specialize hN  (max N N') (le_max_left _ _),
  specialize hN' (max N N') (le_max_right _ _), rw abs_le at hN', linarith,
end

/-
Let's now return to the result proved in the `00_` file of this series, 
and prove again the sequential characterization of upper bounds (with a slighly
different proof).

For this, and other exercises below, we'll need many things that we proved in previous files,
and a couple of extras.

From the 5th file:

  limit_const (x : ℝ) : seq_limit (λ n, x) x


  squeeze (lim_u : seq_limit u l) (lim_w : seq_limit w l)
    (hu : ∀ n, u n ≤ v n) (hw : ∀ n, v n ≤ w n)  : seq_limit v l

From the 8th:

  def upper_bound (A : set ℝ) (x : ℝ) := ∀ a ∈ A, a ≤ x

  def is_sup (A : set ℝ) (x : ℝ) := upper_bound A x ∧ ∀ y, upper_bound A y → x ≤ y

  lt_sup (hx : is_sup A x) : ∀ y, y < x → ∃ a ∈ A, y < a :=

You can also use:

  nat.one_div_pos_of_nat {n : ℕ} : 0 < 1 / (n + 1 : ℝ)

  inv_succ_le_all :  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, 1/(n + 1 : ℝ) ≤ ε

and their easy consequences:

  limit_of_sub_le_inv_succ (h : ∀ n, |u n - x| ≤ 1/(n+1)) : seq_limit u x

  limit_const_add_inv_succ (x : ℝ) : seq_limit (λ n, x + 1/(n+1)) x

  limit_const_sub_inv_succ (x : ℝ) : seq_limit (λ n, x - 1/(n+1)) x

The structure of the proof is offered. It features a new tactic: 
`choose` which invokes the axiom of choice (observing the tactic state before and
after using it should be enough to understand everything). 
-/

-- 0072
lemma is_sup_iff (A : set ℝ) (x : ℝ) :
(is_sup A x) ↔ (upper_bound A x ∧ ∃ u : ℕ → ℝ, seq_limit u x ∧ ∀ n, u n ∈ A ) :=
begin
  split,
  { intro h,
    split,
    {
      exact h.1,
    },
    { have : ∀ n : ℕ, ∃ a ∈ A, x - 1/(n+1) < a,
      { intros n,
        have : 1/(n+1 : ℝ) > 0,
          exact nat.one_div_pos_of_nat,
        apply lt_sup h, linarith,
      },
      choose u hu using this,
      use u, split, apply limit_of_sub_le_inv_succ, intro n, rw abs_le,
      split; linarith[(hu n).2, h.1 (u n) (hu n).1],
      intro n, exact (hu n).1,
  } },
  { rintro ⟨maj, u, limu, u_in⟩, 
    split, exact maj, intros y hy, apply lim_le limu, intro n, exact hy (u n) (u_in n),
  },
end

/-- Continuity of a function at a point  -/
def continuous_at_pt (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

variables {f : ℝ → ℝ} {x₀ : ℝ} {u : ℕ → ℝ}

-- 0073
lemma seq_continuous_of_continuous (hf : continuous_at_pt f x₀)
  (hu : seq_limit u x₀) : seq_limit (f ∘ u) (f x₀) :=
begin
  intros ε ε_pos, rcases hf ε ε_pos with ⟨δ, δ_pos, hδ⟩,
  rcases hu δ δ_pos with ⟨N,hN⟩, use N, intros n hn,
  exact hδ (u n) (hN n hn),
end

-- 0074
example :
  (∀ u : ℕ → ℝ, seq_limit u x₀ → seq_limit (f ∘ u) (f x₀)) →
  continuous_at_pt f x₀ :=
begin
  intro h, by_contradiction hyp, unfold continuous_at_pt at hyp, push_neg at hyp,
  rcases hyp with ⟨ε,ε_pos,hyp⟩,
  have j : ∀ (n : ℕ), ∃ (x : ℝ), |x - x₀| ≤ (1/(n+1)) ∧ ε < |f x - f x₀|,
  intros n, exact hyp (1/(n+1)) (nat.one_div_pos_of_nat), clear hyp,
  choose u hu using j, have k := h u,
  have lim : seq_limit u x₀, {apply limit_of_sub_le_inv_succ, intro n, exact (hu n).left},
  have limf := k lim, rcases limf ε ε_pos with ⟨N,hN⟩,
  specialize hN N (by linarith), specialize hu N, linarith,
end

/-
Recall from the 6th file:


  def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m

  def cluster_point (u : ℕ → ℝ) (a : ℝ) :=
    ∃ φ, extraction φ ∧ seq_limit (u ∘ φ) a


  id_le_extraction : extraction φ → ∀ n, n ≤ φ n

and from the 8th file:

  def tendsto_infinity (u : ℕ → ℝ) := ∀ A, ∃ N, ∀ n ≥ N, u n ≥ A

  not_seq_limit_of_tendstoinfinity : tendsto_infinity u → ∀ l, ¬ seq_limit u l
-/

variables {φ : ℕ → ℕ}


-- 0075
lemma subseq_tendstoinfinity
  (h : tendsto_infinity u) (hφ : extraction φ) :
tendsto_infinity (u ∘ φ) :=
begin
  intro A, cases h A with N hN, use N, intros n hn, apply hN,
  by_cases j : (n = N), rw j, exact id_le_extraction hφ N, unfold extraction at hφ,
  change n≠N at j, have k : n > N, exact (ne.symm j).lt_of_le hn,
  have l := hφ N n (by linarith),
  linarith [id_le_extraction hφ N],
end

-- 0076
lemma squeeze_infinity {u v : ℕ → ℝ} (hu : tendsto_infinity u)
(huv : ∀ n, u n ≤ v n) : tendsto_infinity v :=
begin
  intro A, rcases hu A with ⟨N, hN⟩, use N, intros n hn,
  specialize hN n hn, specialize huv n, linarith,
end

/-
We will use segments: Icc a b := { x | a ≤ x ∧ x ≤ b }
The notation stands for Interval-closed-closed. Variations exist with
o or i instead of c, where o stands for open and i for infinity.

We will use the following version of Bolzano-Weierstrass

  bolzano_weierstrass (h : ∀ n, u n ∈ [a, b]) :
    ∃ c ∈ [a, b], cluster_point u c

as well as the obvious

  seq_limit_id : tendsto_infinity (λ n, n)
-/
open set


-- 0077
lemma bdd_above_segment {f : ℝ → ℝ} {a b : ℝ} (hf : ∀ x ∈ Icc a b, continuous_at_pt f x) :
∃ M, ∀ x ∈ Icc a b, f x ≤ M :=
begin
  by_contradiction hyp, push_neg at hyp,
  have j : ∀ (n : ℕ), ∃ (x : ℝ), x ∈ Icc a b ∧ ↑n < f x,
  intro n, exact hyp n, clear hyp,
  choose u hu using j,
  have h : ∀ n, u n ∈ Icc a b, intro n, exact (hu n).left,
  have k : ∀ n, ↑n ≤ f(u n), intro n, linarith[(hu n).right], clear hu,
  have j := bolzano_weierstrass h, clear h,
  rcases j with ⟨c, cin, hc⟩,
  rcases hc with ⟨φ, hφ, hlim⟩,
  change seq_limit (u ∘ φ) c at hlim,
  have j : seq_limit (f ∘ u ∘ φ) (f c), 
  from seq_continuous_of_continuous (hf c cin) (hlim),
  clear hlim cin hf,
  have jj := squeeze_infinity seq_limit_id k,
  have l := subseq_tendstoinfinity jj hφ,
  exact not_seq_limit_of_tendstoinfinity l (f c) j,
end

/-
In the next exercise, we can use:

  abs_neg x : |-x| = |x|
-/

-- 0078
lemma continuous_opposite {f : ℝ → ℝ} {x₀ : ℝ} (h : continuous_at_pt f x₀) :
  continuous_at_pt (λ x, -f x) x₀ :=
begin
  intros ε ε_pos,
  rcases h ε ε_pos with ⟨δ, δ_pos, hδ⟩,
  use [δ, δ_pos], intros x hx, specialize hδ x hx,
  rw ← abs_neg, ring_nf, exact hδ,
end

/-
Now let's combine the two exercises above
-/

-- 0079
lemma bdd_below_segment {f : ℝ → ℝ} {a b : ℝ} (hf : ∀ x ∈ Icc a b, continuous_at_pt f x) :
∃ m, ∀ x ∈ Icc a b, m ≤ f x :=
begin
  have j : ∀ x ∈ Icc a b, continuous_at_pt (-f) x,
  {intros x H, exact continuous_opposite (hf x H)},
  clear hf,
  have k := bdd_above_segment j, clear j,
  rcases k with ⟨M,h⟩,
  use (-M), intros x H, specialize h x H, change - (f x) ≤ M at h,  linarith,
end

/-
Remember from the 5th file:

 unique_limit : seq_limit u l → seq_limit u l' → l = l'

and from the 6th one:

  subseq_tendsto_of_tendsto (h : seq_limit u l) (hφ : extraction φ) :
    seq_limit (u ∘ φ) l

We now admit the following version of the least upper bound theorem
(that cannot be proved without discussing the construction of real numbers
or admitting another strong theorem).

sup_segment {a b : ℝ} {A : set ℝ} (hnonvide : ∃ x, x ∈ A) (h : A ⊆ Icc a b) :
  ∃ x ∈ Icc a b, is_sup A x

In the next exercise, it can be useful to prove inclusions of sets of real number.
By definition, A ⊆ B means : ∀ x, x ∈ A → x ∈ B.
Hence one can start a proof of A ⊆ B by `intros x x_in`,
which brings `x : ℝ` and `x_in : x ∈ A` in the local context,
and then prove `x ∈ B`.

Note also the use of 
  {x | P x}
which denotes the set of x satisfying predicate P.

Hence `x' ∈ { x | P x} ↔ P x'`, by definition.
-/

-- 0080
example {a b : ℝ} (hab : a ≤ b) (hf : ∀ x ∈ Icc a b, continuous_at_pt f x) :
∃ x₀ ∈ Icc a b, ∀ x ∈ Icc a b, f x ≤ f x₀ :=
begin
  cases bdd_above_segment hf with M hM,
  cases bdd_below_segment hf with m hm,
  let A := { (f x) | x ∈ Icc a b},
  have hnonvide : ∃ x, x ∈ A, use (f a), use a, split,
  split; linarith, linarith,
  have h : A ⊆ Icc m M, intros y y_in, rcases y_in with ⟨x, hx, hxx⟩, split,
  rw ← hxx, apply (hm x hx), rw ← hxx, apply (hM x hx),
  have j := sup_segment hnonvide h,
  rcases j with ⟨y,yin,hy⟩,
  have k := (is_sup_iff A y).1 hy, clear hM hm h yin hy hnonvide,
  cases k with up seq, rcases seq with ⟨u,ulim,hu⟩,
  choose v hv using hu,
  have vin : ∀ n, v n ∈ Icc a b, intro n, exact (hv n).1,
  have fv  : ∀ n, f (v n) = u n, intro n, exact (hv n).2,
  clear hv,
  have vlim := bolzano_weierstrass vin,
  rcases vlim with ⟨c, cin, hc⟩,
  use [c,cin], intro x, rcases hc with ⟨φ, φ_ext, φlim⟩,
  have j : ∀ n, f(v (φ n)) = u (φ n), intro n, exact fv (φ n),
  have limit : seq_limit (u ∘ φ) (f c),
  clear M m,
  have kk := seq_continuous_of_continuous (hf c cin) φlim,
  have leq : ∀ n, f(v(φ n)) ≤ u(φ n), intro n, linarith[j n],
  have geq : ∀ n, f(v(φ n)) ≥ u(φ n), intro n, linarith[j n],
  have kkk := squeeze kk kk leq geq, exact kkk,
  have kkkk := subseq_tendsto_of_tendsto ulim φ_ext,
  have kkkkk := unique_limit kkkk limit,
  rw ← kkkkk,
  intro hh,
  apply up, use x, split, exact hh, refl,
end

lemma stupid {a b x : ℝ} (h : x ∈ Icc a b) (h' : x ≠ b) : x < b :=
lt_of_le_of_ne h.right h'

/-
And now the final boss...
-/

def I := (Icc 0 1 : set ℝ) -- the type ascription makes sure 0 and 1 are real numbers here

-- 0081
example (f : ℝ → ℝ) (hf : ∀ x, continuous_at_pt f x) (h₀ : f 0 < 0) (h₁ : f 1 > 0) :
∃ x₀ ∈ I, f x₀ = 0 :=
begin
  let A := { x | x ∈ I ∧ f x < 0},
  have ex_x₀ : ∃ x₀ ∈ I, is_sup A x₀,
  {
    have h : ∀ x ∈ I, continuous_at_pt f x, intros x xi, exact hf x,
    cases bdd_above_segment h with M jM, cases bdd_below_segment h with m jm,
    apply sup_segment,
    use 0, split, split; linarith, from h₀, intros x hx,cases hx with h1 h2, exact h1,

  },
  rcases ex_x₀ with ⟨x₀, x₀_in, x₀_sup⟩,
  use [x₀, x₀_in],
  have : f x₀ ≤ 0,
  {
    rw is_sup_iff at x₀_sup,
    cases x₀_sup with up lim,
    rcases lim with ⟨u, limu, inc⟩,
    have j : ∀ n, f (u n) < 0, intro n, exact (inc n).2,
    by_contradiction hyp, push_neg at hyp,
    have limf : seq_limit (f ∘ u) (f x₀), exact seq_continuous_of_continuous (hf x₀) limu,
    specialize limf (f x₀) hyp, cases limf with N hN, specialize hN N (by linarith),
    rw abs_le at hN, linarith[j N],
  },
  have x₀_1: x₀ < 1,
  {
    have j : x₀ ≠ 1, intro j, rw ← j at h₁, linarith, exact stupid x₀_in j,
  },
  have : f x₀ ≥ 0,
  { have in_I : ∃ N : ℕ, ∀ n ≥ N, x₀ + 1/(n+1) ∈ I,
    { have : ∃ N : ℕ, ∀ n≥ N, 1/(n+1 : ℝ) ≤ 1-x₀,
      {
        have j := limit_const_add_inv_succ x₀, specialize j ((1-x₀)) (by linarith),
        cases j with N hN, use N, intros n hn, specialize hN n hn, rw abs_le at hN,
        cases hN with h1 h2, simp at h2, simp, exact h2,
      },
      cases this with N hN, use N, intros n hn, specialize hN n hn, split,
      cases x₀_in with above below,
      have k : 0 < 1 / ((n + 1):ℝ), from nat.one_div_pos_of_nat,
      linarith, linarith,
    },
    have not_in : ∀ n : ℕ, x₀ + 1/(n+1) ∉ A,
    -- By definition, x ∉ A means ¬ (x ∈ A).
    {
      intro n, by_contradiction hyp,
      have k : 0 < 1 / ((n + 1):ℝ), from nat.one_div_pos_of_nat,
      have ineq : x₀ < x₀ + 1/(n+1), linarith, linarith[x₀_sup.1 (x₀ + 1 / (n + 1)) hyp],
    },
    dsimp [A] at not_in, 
    have j : ∃ N : ℕ, ∀ n ≥ N, f (x₀ + 1 / (n + 1)) ≥ 0,
    {
      cases in_I with N hN, use N,
      intros n hn, specialize hN n hn, specialize not_in n,
      push_neg at not_in, linarith[not_in hN],
    },
    have k := seq_continuous_of_continuous (hf x₀) (limit_const_add_inv_succ x₀),
    apply le_lim k, exact j,
  },
  linarith,
end

