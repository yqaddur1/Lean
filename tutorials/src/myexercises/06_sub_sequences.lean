import tuto_lib
/-
This file continues the elementary study of limits of sequences. 
It can be skipped if the previous file was too easy, it won't introduce
any new tactic or trick.

Remember useful lemmas:

abs_le {x y : ℝ} : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y

abs_add (x y : ℝ) : |x + y| ≤ |x| + |y|

abs_sub_comm (x y : ℝ) : |x - y| = |y - x|

ge_max_iff (p q r) : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q

le_max_left p q : p ≤ max p q

le_max_right p q : q ≤ max p q

and the definition:

def seq_limit (u : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

You can also use a property proved in the previous file:

unique_limit : seq_limit u l → seq_limit u l' → l = l'

def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m
-/


variable { φ : ℕ → ℕ}

/-
The next lemma is proved by an easy induction, but we haven't seen induction
in this tutorial. If you did the natural number game then you can delete 
the proof below and try to reconstruct it.
-/
/-- An extraction is greater than id -/
lemma id_le_extraction' : extraction φ → ∀ n, n ≤ φ n :=
begin
  intros hyp n,
  induction n with n hn,
  { exact nat.zero_le _ },
  { exact nat.succ_le_of_lt (by linarith [hyp n (n+1) (by linarith)]) },
end

/-- Extractions take arbitrarily large values for arbitrarily large 
inputs. -/
-- 0039
lemma extraction_ge : extraction φ → ∀ N N', ∃ n ≥ N', φ n ≥ N :=
begin
  intros hyp N N',
  induction N' with N' hN',
  induction N with d hd,
  use 0, split, linarith, exact nat.zero_le _,
  cases hd with n hn,
  cases hn with H hn, use (n+1),
  split, linarith, have key := hyp n (n+1) (by linarith), 
  rw (show nat.succ d = d+1, by refl), linarith,
  cases hN' with K hN',
  cases hN' with H hN',
  use (K+1), split, rw (show nat.succ N' = N'+1, by refl),
  linarith,
  have key := hyp (K) (K+1) (by linarith),
  linarith,
end

/-- A real number `a` is a cluster point of a sequence `u` 
if `u` has a subsequence converging to `a`. 

def cluster_point (u : ℕ → ℝ) (a : ℝ) :=
∃ φ, extraction φ ∧ seq_limit (u ∘ φ) a
-/

variables {u : ℕ → ℝ} {a l : ℝ}

/-
In the exercise, we use `∃ n ≥ N, ...` which is the abbreviation of
`∃ n, n ≥ N ∧ ...`.
Lean can read this abbreviation, but displays it as the confusing:
`∃ (n : ℕ) (H : n ≥ N)`
One gets used to it. Alternatively, one can get rid of it using the lemma
  exists_prop {p q : Prop} : (∃ (h : p), q) ↔ p ∧ q
-/

/-- If `a` is a cluster point of `u` then there are values of
`u` arbitrarily close to `a` for arbitrarily large input. -/
-- 0040
lemma near_cluster :
  cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε :=
begin
  intro h, cases h with φ h, cases h with h h',
  intros ε ε_pos N,
  specialize h' ε ε_pos, cases h' with N' hN',
  have j := extraction_ge h N N', cases j with n j, cases j with H j,
  use φ n, split, exact j, specialize hN' n H, exact hN',
end

/-
The above exercice can be done in five lines. 
Hint: you can use the anonymous constructor syntax when proving
existential statements.
-/

/-- If `u` tends to `l` then its subsequences tend to `l`. -/
-- 0041
lemma subseq_tendsto_of_tendsto' (h : seq_limit u l) (hφ : extraction φ) :
seq_limit (u ∘ φ) l :=
begin
  intros ε ε_pos,
  cases h ε ε_pos with N hN,
  use N, intros n H,
  exact hN (φ n) (by linarith[id_le_extraction hφ n]),
end

/-- If `u` tends to `l` all its cluster points are equal to `l`. -/
-- 0042
lemma cluster_limit (hl : seq_limit u l) (ha : cluster_point u a) : a = l :=
begin
  cases ha with φ ha,
  cases ha with hext hlim,
  have j := subseq_tendsto_of_tendsto' hl hext,
  exact unique_limit hlim j,
end

/-- Cauchy_sequence sequence -/
def cauchy_sequence (u : ℕ → ℝ) := ∀ ε > 0, ∃ N, ∀ p q, p ≥ N → q ≥ N → |u p - u q| ≤ ε

-- 0043
example : (∃ l, seq_limit u l) → cauchy_sequence u :=
begin
  intros h ε ε_pos, cases h with l h, specialize h (ε/2) (by linarith),
  cases h with N hN, use N, intros p q pN qN,
  have pin := hN p pN, have qin := hN q qN, rw abs_sub_comm (u q) l at qin,
  calc |u p - u q| = |(u p - l) + (l - u q)|   : by ring_nf
               ... ≤ |u p - l| + |l - u q| : by apply abs_add
               ... ≤ ε                     : by linarith,
end


/- 
In the next exercise, you can reuse
 near_cluster : cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε
-/
-- 0044
example (hu : cauchy_sequence u) (hl : cluster_point u l) : seq_limit u l :=
begin
  intros ε ε_pos, have j:= near_cluster hl, specialize j (ε/2) (by linarith),
  specialize hu (ε/2) (by linarith), cases hu with N hu, specialize j N,
  cases j with N' H, cases H with H j, use N', intros n hn,
  specialize hu n N' (by linarith) (by linarith),
  calc |u n - l| = |(u n - u N') + (u N' - l)| : by ring_nf
             ... ≤ |u n - u N'| + |u N' - l|   : by apply abs_add
             ... ≤ ε                           : by linarith,
end

