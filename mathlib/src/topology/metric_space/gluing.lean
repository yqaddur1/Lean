/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import topology.metric_space.isometry

/-!
# Metric space gluing

Gluing two metric spaces along a common subset. Formally, we are given

```
     Φ
  Z ---> X
  |
  |Ψ
  v
  Y
```
where `hΦ : isometry Φ` and `hΨ : isometry Ψ`.
We want to complete the square by a space `glue_space hΦ hΨ` and two isometries
`to_glue_l hΦ hΨ` and `to_glue_r hΦ hΨ` that make the square commute.
We start by defining a predistance on the disjoint union `X ⊕ Y`, for which
points `Φ p` and `Ψ p` are at distance 0. The (quotient) metric space associated
to this predistance is the desired space.

This is an instance of a more general construction, where `Φ` and `Ψ` do not have to be isometries,
but the distances in the image almost coincide, up to `2ε` say. Then one can almost glue the two
spaces so that the images of a point under `Φ` and `Ψ` are `ε`-close. If `ε > 0`, this yields a
metric space structure on `X ⊕ Y`, without the need to take a quotient. In particular,
this gives a natural metric space structure on `X ⊕ Y`, where the basepoints
are at distance 1, say, and the distances between other points are obtained by going through the two
basepoints.
(We also register the same metric space structure on a general disjoint union `Σ i, E i`).

We also define the inductive limit of metric spaces. Given
```
     f 0        f 1        f 2        f 3
X 0 -----> X 1 -----> X 2 -----> X 3 -----> ...
```
where the `X n` are metric spaces and `f n` isometric embeddings, we define the inductive
limit of the `X n`, also known as the increasing union of the `X n` in this context, if we
identify `X n` and `X (n+1)` through `f n`. This is a metric space in which all `X n` embed
isometrically and in a way compatible with `f n`.

-/

noncomputable theory

universes u v w
open function set
open_locale uniformity

namespace metric
section approx_gluing

variables {X : Type u} {Y : Type v} {Z : Type w}

variables [metric_space X] [metric_space Y]
          {Φ : Z → X} {Ψ : Z → Y} {ε : ℝ}
open _root_.sum (inl inr)

/-- Define a predistance on `X ⊕ Y`, for which `Φ p` and `Ψ p` are at distance `ε` -/
def glue_dist (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) : X ⊕ Y → X ⊕ Y → ℝ
| (inl x) (inl y) := dist x y
| (inr x) (inr y) := dist x y
| (inl x) (inr y) := (⨅ p, dist x (Φ p) + dist y (Ψ p)) + ε
| (inr x) (inl y) := (⨅ p, dist y (Φ p) + dist x (Ψ p)) + ε

private lemma glue_dist_self (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) : ∀ x, glue_dist Φ Ψ ε x x = 0
| (inl x) := dist_self _
| (inr x) := dist_self _

lemma glue_dist_glued_points [nonempty Z] (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) (p : Z) :
  glue_dist Φ Ψ ε (inl (Φ p)) (inr (Ψ p)) = ε :=
begin
  have : (⨅ q, dist (Φ p) (Φ q) + dist (Ψ p) (Ψ q)) = 0,
  { have A : ∀ q, 0 ≤ dist (Φ p) (Φ q) + dist (Ψ p) (Ψ q) :=
      λq, by rw ← add_zero (0 : ℝ); exact add_le_add dist_nonneg dist_nonneg,
    refine le_antisymm _ (le_cinfi A),
    have : 0 = dist (Φ p) (Φ p) + dist (Ψ p) (Ψ p), by simp,
    rw this,
    exact cinfi_le ⟨0, forall_range_iff.2 A⟩ p },
  rw [glue_dist, this, zero_add]
end

private lemma glue_dist_comm (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) :
  ∀ x y, glue_dist Φ Ψ ε x y = glue_dist Φ Ψ ε y x
| (inl x) (inl y) := dist_comm _ _
| (inr x) (inr y) := dist_comm _ _
| (inl x) (inr y) := rfl
| (inr x) (inl y) := rfl

variable [nonempty Z]

private lemma glue_dist_triangle (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ)
  (H : ∀ p q, |dist (Φ p) (Φ q) - dist (Ψ p) (Ψ q)| ≤ 2 * ε) :
  ∀ x y z, glue_dist Φ Ψ ε x z ≤ glue_dist Φ Ψ ε x y + glue_dist Φ Ψ ε y z
| (inl x) (inl y) (inl z) := dist_triangle _ _ _
| (inr x) (inr y) (inr z) := dist_triangle _ _ _
| (inr x) (inl y) (inl z) := begin
    have B : ∀ a b, bdd_below (range (λ (p : Z), dist a (Φ p) + dist b (Ψ p))) :=
      λa b, ⟨0, forall_range_iff.2 (λp, add_nonneg dist_nonneg dist_nonneg)⟩,
    unfold glue_dist,
    have : (⨅ p, dist z (Φ p) + dist x (Ψ p)) ≤ (⨅ p, dist y (Φ p) + dist x (Ψ p)) + dist y z,
    { have : (⨅ p, dist y (Φ p) + dist x (Ψ p)) + dist y z =
            infi ((λt, t + dist y z) ∘ (λp, dist y (Φ p) + dist x (Ψ p))),
      { refine map_cinfi_of_continuous_at_of_monotone (continuous_at_id.add continuous_at_const) _
          (B _ _),
        intros x y hx, simpa },
      rw [this, comp],
      refine cinfi_mono (B _ _) (λp, _),
      calc
        dist z (Φ p) + dist x (Ψ p) ≤ (dist y z + dist y (Φ p)) + dist x (Ψ p) :
          add_le_add (dist_triangle_left _ _ _) le_rfl
        ... = dist y (Φ p) + dist x (Ψ p) + dist y z : by ring },
    linarith
  end
| (inr x) (inr y) (inl z) := begin
    have B : ∀ a b, bdd_below (range (λ (p : Z), dist a (Φ p) + dist b (Ψ p))) :=
      λa b, ⟨0, forall_range_iff.2 (λp, add_nonneg dist_nonneg dist_nonneg)⟩,
    unfold glue_dist,
    have : (⨅ p, dist z (Φ p) + dist x (Ψ p)) ≤ dist x y + ⨅ p, dist z (Φ p) + dist y (Ψ p),
    { have : dist x y + (⨅ p, dist z (Φ p) + dist y (Ψ p)) =
            infi ((λt, dist x y + t) ∘ (λp, dist z (Φ p) + dist y (Ψ p))),
      { refine map_cinfi_of_continuous_at_of_monotone (continuous_at_const.add continuous_at_id) _
          (B _ _),
        intros x y hx, simpa },
      rw [this, comp],
      refine cinfi_mono (B _ _) (λp, _),
      calc
        dist z (Φ p) + dist x (Ψ p) ≤ dist z (Φ p) + (dist x y + dist y (Ψ p)) :
          add_le_add le_rfl (dist_triangle _ _ _)
        ... = dist x y + (dist z (Φ p) + dist y (Ψ p)) : by ring },
    linarith
  end
| (inl x) (inl y) (inr z) := begin
    have B : ∀ a b, bdd_below (range (λ (p : Z), dist a (Φ p) + dist b (Ψ p))) :=
      λa b, ⟨0, forall_range_iff.2 (λp, add_nonneg dist_nonneg dist_nonneg)⟩,
    unfold glue_dist,
    have : (⨅ p, dist x (Φ p) + dist z (Ψ p)) ≤ dist x y + ⨅ p, dist y (Φ p) + dist z (Ψ p),
    { have : dist x y + (⨅ p, dist y (Φ p) + dist z (Ψ p)) =
            infi ((λt, dist x y + t) ∘ (λp, dist y (Φ p) + dist z (Ψ p))),
      { refine map_cinfi_of_continuous_at_of_monotone (continuous_at_const.add continuous_at_id) _
          (B _ _),
        intros x y hx, simpa },
      rw [this, comp],
      refine cinfi_mono (B _ _) (λp, _),
      calc
        dist x (Φ p) + dist z (Ψ p) ≤ (dist x y + dist y (Φ p)) + dist z (Ψ p) :
          add_le_add (dist_triangle _ _ _) le_rfl
        ... = dist x y + (dist y (Φ p) + dist z (Ψ p)) : by ring },
    linarith
  end
| (inl x) (inr y) (inr z) := begin
    have B : ∀ a b, bdd_below (range (λ (p : Z), dist a (Φ p) + dist b (Ψ p))) :=
      λa b, ⟨0, forall_range_iff.2 (λp, add_nonneg dist_nonneg dist_nonneg)⟩,
    unfold glue_dist,
    have : (⨅ p, dist x (Φ p) + dist z (Ψ p)) ≤ (⨅ p, dist x (Φ p) + dist y (Ψ p)) + dist y z,
    { have : (⨅ p, dist x (Φ p) + dist y (Ψ p)) + dist y z =
            infi ((λt, t + dist y z) ∘ (λp, dist x (Φ p) + dist y (Ψ p))),
      { refine map_cinfi_of_continuous_at_of_monotone (continuous_at_id.add continuous_at_const) _
          (B _ _),
        intros x y hx, simpa },
      rw [this, comp],
      refine cinfi_mono (B _ _) (λp, _),
      calc
        dist x (Φ p) + dist z (Ψ p) ≤ dist x (Φ p) + (dist y z + dist y (Ψ p)) :
          add_le_add le_rfl (dist_triangle_left _ _ _)
        ... = dist x (Φ p) + dist y (Ψ p) + dist y z : by ring },
    linarith
  end
| (inl x) (inr y) (inl z) := le_of_forall_pos_le_add $ λδ δpos, begin
    obtain ⟨p, hp⟩ : ∃ p, dist x (Φ p) + dist y (Ψ p) < (⨅ p, dist x (Φ p) + dist y (Ψ p)) + δ / 2,
      from exists_lt_of_cinfi_lt (by linarith),
    obtain ⟨q, hq⟩ : ∃ q, dist z (Φ q) + dist y (Ψ q) < (⨅ p, dist z (Φ p) + dist y (Ψ p)) + δ / 2,
      from exists_lt_of_cinfi_lt (by linarith),
    have : dist (Φ p) (Φ q) ≤ dist (Ψ p) (Ψ q) + 2 * ε,
      { have := le_trans (le_abs_self _) (H p q), by linarith },
    calc dist x z ≤ dist x (Φ p) + dist (Φ p) (Φ q) + dist (Φ q) z : dist_triangle4 _ _ _ _
      ... ≤ dist x (Φ p) + dist (Ψ p) (Ψ q) + dist z (Φ q) + 2 * ε : by rw [dist_comm z]; linarith
      ... ≤ dist x (Φ p) + (dist y (Ψ p) + dist y (Ψ q)) + dist z (Φ q) + 2 * ε :
        add_le_add (add_le_add (add_le_add le_rfl (dist_triangle_left _ _ _)) le_rfl) le_rfl
      ... ≤ ((⨅ p, dist x (Φ p) + dist y (Ψ p)) + ε) +
            ((⨅ p, dist z (Φ p) + dist y (Ψ p)) + ε) + δ : by linarith
  end
| (inr x) (inl y) (inr z) := le_of_forall_pos_le_add $ λδ δpos, begin
    obtain ⟨p, hp⟩ : ∃ p, dist y (Φ p) + dist x (Ψ p) < (⨅ p, dist y (Φ p) + dist x (Ψ p)) + δ / 2,
      from exists_lt_of_cinfi_lt (by linarith),
    obtain ⟨q, hq⟩ : ∃ q, dist y (Φ q) + dist z (Ψ q) < (⨅ p, dist y (Φ p) + dist z (Ψ p)) + δ / 2,
      from exists_lt_of_cinfi_lt (by linarith),
    have : dist (Ψ p) (Ψ q) ≤ dist (Φ p) (Φ q) + 2 * ε,
      { have := le_trans (neg_le_abs_self _) (H p q), by linarith },
    calc dist x z ≤ dist x (Ψ p) + dist (Ψ p) (Ψ q) + dist (Ψ q) z : dist_triangle4 _ _ _ _
      ... ≤ dist x (Ψ p) + dist (Φ p) (Φ q) + dist z (Ψ q) + 2 * ε : by rw [dist_comm z]; linarith
      ... ≤ dist x (Ψ p) + (dist y (Φ p) + dist y (Φ q)) + dist z (Ψ q) + 2 * ε :
        add_le_add (add_le_add (add_le_add le_rfl (dist_triangle_left _ _ _)) le_rfl) le_rfl
      ... ≤ ((⨅ p, dist y (Φ p) + dist x (Ψ p)) + ε) +
            ((⨅ p, dist y (Φ p) + dist z (Ψ p)) + ε) + δ : by linarith
  end

private lemma glue_eq_of_dist_eq_zero (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) (ε0 : 0 < ε) :
  ∀ p q : X ⊕ Y, glue_dist Φ Ψ ε p q = 0 → p = q
| (inl x) (inl y) h := by rw eq_of_dist_eq_zero h
| (inl x) (inr y) h := begin
    have : 0 ≤ (⨅ p, dist x (Φ p) + dist y (Ψ p)) :=
      le_cinfi (λp, by simpa using add_le_add (@dist_nonneg _ _ x _) (@dist_nonneg _ _ y _)),
    have : 0 + ε ≤ glue_dist Φ Ψ ε (inl x) (inr y) := add_le_add this (le_refl ε),
    exfalso,
    linarith
  end
| (inr x) (inl y) h := begin
    have : 0 ≤ ⨅ p, dist y (Φ p) + dist x (Ψ p) :=
      le_cinfi (λp, by simpa [add_comm]
                         using add_le_add (@dist_nonneg _ _ x _) (@dist_nonneg _ _ y _)),
    have : 0 + ε ≤ glue_dist Φ Ψ ε (inr x) (inl y) := add_le_add this (le_refl ε),
    exfalso,
    linarith
  end
| (inr x) (inr y) h := by rw eq_of_dist_eq_zero h

/-- Given two maps `Φ` and `Ψ` intro metric spaces `X` and `Y` such that the distances between
`Φ p` and `Φ q`, and between `Ψ p` and `Ψ q`, coincide up to `2 ε` where `ε > 0`, one can almost
glue the two spaces `X` and `Y` along the images of `Φ` and `Ψ`, so that `Φ p` and `Ψ p` are
at distance `ε`. -/
def glue_metric_approx (Φ : Z → X) (Ψ : Z → Y) (ε : ℝ) (ε0 : 0 < ε)
  (H : ∀ p q, |dist (Φ p) (Φ q) - dist (Ψ p) (Ψ q)| ≤ 2 * ε) : metric_space (X ⊕ Y) :=
{ dist               := glue_dist Φ Ψ ε,
  dist_self          := glue_dist_self Φ Ψ ε,
  dist_comm          := glue_dist_comm Φ Ψ ε,
  dist_triangle      := glue_dist_triangle Φ Ψ ε H,
  eq_of_dist_eq_zero := glue_eq_of_dist_eq_zero Φ Ψ ε ε0 }

end approx_gluing

section sum
/- A particular case of the previous construction is when one uses basepoints in `X` and `Y` and one
glues only along the basepoints, putting them at distance 1. We give a direct definition of
the distance, without infi, as it is easier to use in applications, and show that it is equal to
the gluing distance defined above to take advantage of the lemmas we have already proved. -/

variables {X : Type u} {Y : Type v} {Z : Type w}
variables [metric_space X] [metric_space Y]
open sum (inl inr)

/-- Distance on a disjoint union. There are many (noncanonical) ways to put a distance compatible
with each factor.
If the two spaces are bounded, one can say for instance that each point in the first is at distance
`diam X + diam Y + 1` of each point in the second.
Instead, we choose a construction that works for unbounded spaces, but requires basepoints,
chosen arbitrarily.
We embed isometrically each factor, set the basepoints at distance 1,
arbitrarily, and say that the distance from `a` to `b` is the sum of the distances of `a` and `b` to
their respective basepoints, plus the distance 1 between the basepoints.
Since there is an arbitrary choice in this construction, it is not an instance by default. -/
def sum.dist : X ⊕ Y → X ⊕ Y → ℝ
| (inl a) (inl a') := dist a a'
| (inr b) (inr b') := dist b b'
| (inl a) (inr b)  := dist a (nonempty.some ⟨a⟩) + 1 + dist (nonempty.some ⟨b⟩) b
| (inr b) (inl a)  := dist b (nonempty.some ⟨b⟩) + 1 + dist (nonempty.some ⟨a⟩) a

lemma sum.dist_eq_glue_dist {p q : X ⊕ Y} (x : X) (y : Y) :
  sum.dist p q = glue_dist (λ _ : unit, nonempty.some ⟨x⟩) (λ _ : unit, nonempty.some ⟨y⟩) 1 p q :=
by cases p; cases q; refl <|> simp [sum.dist, glue_dist, dist_comm, add_comm, add_left_comm]

private lemma sum.dist_comm (x y : X ⊕ Y) : sum.dist x y = sum.dist y x :=
by cases x; cases y; simp only [sum.dist, dist_comm, add_comm, add_left_comm]

lemma sum.one_dist_le {x : X} {y : Y} : 1 ≤ sum.dist (inl x) (inr y) :=
le_trans (le_add_of_nonneg_right dist_nonneg) $
add_le_add_right (le_add_of_nonneg_left dist_nonneg) _

lemma sum.one_dist_le' {x : X} {y : Y} : 1 ≤ sum.dist (inr y) (inl x) :=
by rw sum.dist_comm; exact sum.one_dist_le

private lemma sum.mem_uniformity (s : set ((X ⊕ Y) × (X ⊕ Y))) :
  s ∈ 𝓤 (X ⊕ Y) ↔ ∃ ε > 0, ∀ a b, sum.dist a b < ε → (a, b) ∈ s :=
begin
  split,
  { rintro ⟨hsX, hsY⟩,
    rcases mem_uniformity_dist.1 hsX with ⟨εX, εX0, hX⟩,
    rcases mem_uniformity_dist.1 hsY with ⟨εY, εY0, hY⟩,
    refine ⟨min (min εX εY) 1, lt_min (lt_min εX0 εY0) zero_lt_one, _⟩,
    rintro (a|a) (b|b) h,
    { exact hX (lt_of_lt_of_le h (le_trans (min_le_left _ _) (min_le_left _ _))) },
    { cases not_le_of_lt (lt_of_lt_of_le h (min_le_right _ _)) sum.one_dist_le },
    { cases not_le_of_lt (lt_of_lt_of_le h (min_le_right _ _)) sum.one_dist_le' },
    { exact hY (lt_of_lt_of_le h (le_trans (min_le_left _ _) (min_le_right _ _))) } },
  { rintro ⟨ε, ε0, H⟩,
    split; rw [filter.mem_sets, filter.mem_map, mem_uniformity_dist];
      exact ⟨ε, ε0, λ x y h, H _ _ (by exact h)⟩ }
end

/-- The distance on the disjoint union indeed defines a metric space. All the distance properties
follow from our choice of the distance. The harder work is to show that the uniform structure
defined by the distance coincides with the disjoint union uniform structure. -/
def metric_space_sum : metric_space (X ⊕ Y) :=
{ dist               := sum.dist,
  dist_self          := λx, by cases x; simp only [sum.dist, dist_self],
  dist_comm          := sum.dist_comm,
  dist_triangle      := λ p q r,
  begin
    cases p; cases q; cases r,
    { exact dist_triangle _ _ _ },
    { simp only [dist, sum.dist_eq_glue_dist p r],
      exact glue_dist_triangle _ _ _ (by norm_num) _ _ _ },
    { simp only [dist, sum.dist_eq_glue_dist p q],
      exact glue_dist_triangle _ _ _ (by norm_num) _ _ _ },
    { simp only [dist, sum.dist_eq_glue_dist p q],
      exact glue_dist_triangle _ _ _ (by norm_num) _ _ _ },
    { simp only [dist, sum.dist_eq_glue_dist q p],
      exact glue_dist_triangle _ _ _ (by norm_num) _ _ _ },
    { simp only [dist, sum.dist_eq_glue_dist q p],
      exact glue_dist_triangle _ _ _ (by norm_num) _ _ _ },
    { simp only [dist, sum.dist_eq_glue_dist r p],
      exact glue_dist_triangle _ _ _ (by norm_num) _ _ _ },
    { exact dist_triangle _ _ _ },
  end,
  eq_of_dist_eq_zero := λ p q,
  begin
    cases p; cases q,
    { simp only [sum.dist, dist_eq_zero, imp_self] },
    { assume h,
      simp only [dist, sum.dist_eq_glue_dist p q] at h,
      exact glue_eq_of_dist_eq_zero _ _ _ zero_lt_one _ _ h },
    { assume h,
      simp only [dist, sum.dist_eq_glue_dist q p] at h,
      exact glue_eq_of_dist_eq_zero _ _ _ zero_lt_one _ _ h },
    { simp only [sum.dist, dist_eq_zero, imp_self] },
  end,
  to_uniform_space   := sum.uniform_space,
  uniformity_dist    := uniformity_dist_of_mem_uniformity _ _ sum.mem_uniformity }

local attribute [instance] metric_space_sum

lemma sum.dist_eq {x y : X ⊕ Y} : dist x y = sum.dist x y := rfl

/-- The left injection of a space in a disjoint union is an isometry -/
lemma isometry_inl : isometry (sum.inl : X → (X ⊕ Y)) :=
isometry_emetric_iff_metric.2 $ λx y, rfl

/-- The right injection of a space in a disjoint union is an isometry -/
lemma isometry_inr : isometry (sum.inr : Y → (X ⊕ Y)) :=
isometry_emetric_iff_metric.2 $ λx y, rfl

end sum

namespace sigma
/- Copy of the previous paragraph, but for arbitrary disjoint unions instead of the disjoint union
of two spaces. I.e., work with sigma types instead of sum types. -/

variables {ι : Type*} {E : ι → Type*} [∀ i, metric_space (E i)]

open_locale classical

/-- Distance on a disjoint union. There are many (noncanonical) ways to put a distance compatible
with each factor.
We choose a construction that works for unbounded spaces, but requires basepoints,
chosen arbitrarily.
We embed isometrically each factor, set the basepoints at distance 1, arbitrarily,
and say that the distance from `a` to `b` is the sum of the distances of `a` and `b` to
their respective basepoints, plus the distance 1 between the basepoints.
Since there is an arbitrary choice in this construction, it is not an instance by default. -/
protected def dist : (Σ i, E i) → (Σ i, E i) → ℝ
| ⟨i, x⟩ ⟨j, y⟩ :=
    if h : i = j then by { have : E j = E i, by rw h, exact has_dist.dist x (cast this y) }
    else has_dist.dist x (nonempty.some ⟨x⟩) + 1 + has_dist.dist (nonempty.some ⟨y⟩) y

/-- A `has_dist` instance on the disjoint union `Σ i, E i`.
We embed isometrically each factor, set the basepoints at distance 1, arbitrarily,
and say that the distance from `a` to `b` is the sum of the distances of `a` and `b` to
their respective basepoints, plus the distance 1 between the basepoints.
Since there is an arbitrary choice in this construction, it is not an instance by default. -/
def has_dist : has_dist (Σ i, E i) :=
⟨sigma.dist⟩

local attribute [instance] sigma.has_dist

@[simp] lemma dist_same (i : ι) (x : E i) (y : E i) :
  dist (⟨i, x⟩ : Σ j, E j) ⟨i, y⟩ = dist x y :=
by simp [has_dist.dist, sigma.dist]

@[simp] lemma dist_ne {i j : ι} (h : i ≠ j) (x : E i) (y : E j) :
  dist (⟨i, x⟩ : Σ k, E k) ⟨j, y⟩ = dist x (nonempty.some ⟨x⟩) + 1 + dist (nonempty.some ⟨y⟩) y :=
by simp [has_dist.dist, sigma.dist, h]

lemma one_le_dist_of_ne {i j : ι} (h : i ≠ j) (x : E i) (y : E j) :
  1 ≤ dist (⟨i, x⟩ : Σ k, E k) ⟨j, y⟩ :=
begin
  rw sigma.dist_ne h x y,
  linarith [@dist_nonneg _ _ x (nonempty.some ⟨x⟩), @dist_nonneg _ _ (nonempty.some ⟨y⟩) y]
end

lemma fst_eq_of_dist_lt_one (x y : Σ i, E i) (h : dist x y < 1) :
  x.1 = y.1 :=
begin
  cases x, cases y,
  contrapose! h,
  apply one_le_dist_of_ne h,
end

protected lemma dist_triangle (x y z : Σ i, E i) :
  dist x z ≤ dist x y + dist y z :=
begin
  rcases x with ⟨i, x⟩, rcases y with ⟨j, y⟩, rcases z with ⟨k, z⟩,
  rcases eq_or_ne i k with rfl|hik,
  { rcases eq_or_ne i j with rfl|hij,
    { simpa using dist_triangle x y z },
    { simp only [hij, hij.symm, sigma.dist_same, sigma.dist_ne, ne.def, not_false_iff],
      calc dist x z ≤ dist x (nonempty.some ⟨x⟩) + 0 + 0 + (0 + 0 + dist (nonempty.some ⟨z⟩) z) :
        by simpa only [zero_add, add_zero] using dist_triangle _ _ _
      ... ≤ _ : by apply_rules [add_le_add, le_rfl, dist_nonneg, zero_le_one] } },
  { rcases eq_or_ne i j with rfl|hij,
    { simp only [hik, sigma.dist_ne, ne.def, not_false_iff, sigma.dist_same],
      calc dist x (nonempty.some ⟨x⟩) + 1 + dist (nonempty.some ⟨z⟩) z ≤
        (dist x y + dist y (nonempty.some ⟨y⟩) + 1 + dist (nonempty.some ⟨z⟩) z) :
          by apply_rules [add_le_add, le_rfl, dist_triangle]
      ... = _ : by abel },
    { rcases eq_or_ne j k with rfl|hjk,
      { simp only [hij, sigma.dist_ne, ne.def, not_false_iff, sigma.dist_same],
        calc dist x (nonempty.some ⟨x⟩) + 1 + dist (nonempty.some ⟨z⟩) z ≤
          dist x (nonempty.some ⟨x⟩) + 1 + (dist (nonempty.some ⟨z⟩) y + dist y z) :
            by apply_rules [add_le_add, le_rfl, dist_triangle]
        ... = _ : by abel },
      { simp only [hik, hij, hjk, sigma.dist_ne, ne.def, not_false_iff],
        calc dist x (nonempty.some ⟨x⟩) + 1 + dist (nonempty.some ⟨z⟩) z
          = dist x (nonempty.some ⟨x⟩) + 1 + 0 + (0 + 0 + dist (nonempty.some ⟨z⟩) z) :
            by simp only [add_zero, zero_add]
        ... ≤ _ :
          by apply_rules [add_le_add, zero_le_one, dist_nonneg, le_rfl] } } }
end

protected lemma is_open_iff (s : set (Σ i, E i)) :
  is_open s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, dist x y < ε → y ∈ s :=
begin
  split,
  { rintros hs ⟨i, x⟩ hx,
    obtain ⟨ε, εpos, hε⟩ : ∃ (ε : ℝ) (H : ε > 0), ball x ε ⊆ sigma.mk i ⁻¹' s :=
      metric.is_open_iff.1 (is_open_sigma_iff.1 hs i) x hx,
    refine ⟨min ε 1, lt_min εpos zero_lt_one, _⟩,
    rintros ⟨j, y⟩ hy,
    rcases eq_or_ne i j with rfl|hij,
    { simp only [sigma.dist_same, lt_min_iff] at hy,
      exact hε (mem_ball'.2 hy.1) },
    { apply (lt_irrefl (1 : ℝ) _).elim,
      calc 1 ≤ sigma.dist ⟨i, x⟩ ⟨j, y⟩ : sigma.one_le_dist_of_ne hij _ _
      ... < 1 : hy.trans_le (min_le_right _ _) } },
  { assume H,
    apply is_open_sigma_iff.2 (λ i, _),
    apply metric.is_open_iff.2 (λ x hx, _),
    obtain ⟨ε, εpos, hε⟩ : ∃ (ε : ℝ) (H : ε > 0), ∀ y, dist (⟨i, x⟩ : Σ j, E j) y < ε → y ∈ s :=
      H ⟨i, x⟩ hx,
    refine ⟨ε, εpos, λ y hy, _⟩,
    apply hε ⟨i, y⟩,
    rw sigma.dist_same,
    exact mem_ball'.1 hy }
end

/-- A metric space structure on the disjoint union `Σ i, E i`.
We embed isometrically each factor, set the basepoints at distance 1, arbitrarily,
and say that the distance from `a` to `b` is the sum of the distances of `a` and `b` to
their respective basepoints, plus the distance 1 between the basepoints.
Since there is an arbitrary choice in this construction, it is not an instance by default. -/
protected def metric_space : metric_space (Σ i, E i) :=
begin
  refine metric_space.of_metrizable sigma.dist _ _ sigma.dist_triangle
    sigma.is_open_iff _,
  { rintros ⟨i, x⟩, simp [sigma.dist] },
  { rintros ⟨i, x⟩ ⟨j, y⟩,
    rcases eq_or_ne i j with rfl|h,
    { simp [sigma.dist, dist_comm] },
    { simp only [sigma.dist, dist_comm, h, h.symm, not_false_iff, dif_neg], abel } },
  { rintros ⟨i, x⟩ ⟨j, y⟩,
    rcases eq_or_ne i j with rfl|hij,
    { simp [sigma.dist] },
    { assume h,
      apply (lt_irrefl (1 : ℝ) _).elim,
      calc 1 ≤ sigma.dist (⟨i, x⟩ : Σ k, E k) ⟨j, y⟩ : sigma.one_le_dist_of_ne hij _ _
      ... < 1 : by { rw h, exact zero_lt_one } } }
end

local attribute [instance] sigma.metric_space

open_locale topological_space
open filter

/-- The injection of a space in a disjoint union is an isometry -/
lemma isometry_mk (i : ι) : isometry (sigma.mk i : E i → Σ k, E k) :=
isometry_emetric_iff_metric.2 (by simp)

/-- A disjoint union of complete metric spaces is complete. -/
protected lemma complete_space [∀ i, complete_space (E i)] : complete_space (Σ i, E i) :=
begin
  set s : ι → set (Σ i, E i) := λ i, (sigma.fst ⁻¹' {i}),
  set U := {p : (Σ k, E k) × (Σ k, E k) | dist p.1 p.2 < 1},
  have hc : ∀ i, is_complete (s i),
  { intro i,
    simp only [s, ← range_sigma_mk],
    exact (isometry_mk i).uniform_inducing.is_complete_range },
  have hd : ∀ i j (x ∈ s i) (y ∈ s j), (x, y) ∈ U → i = j,
    from λ i j x hx y hy hxy, (eq.symm hx).trans ((fst_eq_of_dist_lt_one _ _ hxy).trans hy),
  refine complete_space_of_is_complete_univ _,
  convert is_complete_Union_separated hc (dist_mem_uniformity zero_lt_one) hd,
  simp [s, ← preimage_Union]
end

end sigma

section gluing
/- Exact gluing of two metric spaces along isometric subsets. -/

variables {X : Type u} {Y : Type v} {Z : Type w}
variables [nonempty Z] [metric_space Z] [metric_space X] [metric_space Y]
          {Φ : Z → X} {Ψ : Z → Y} {ε : ℝ}
open _root_.sum (inl inr)
local attribute [instance] pseudo_metric.dist_setoid

/-- Given two isometric embeddings `Φ : Z → X` and `Ψ : Z → Y`, we define a pseudo metric space
structure on `X ⊕ Y` by declaring that `Φ x` and `Ψ x` are at distance `0`. -/
def glue_premetric (hΦ : isometry Φ) (hΨ : isometry Ψ) : pseudo_metric_space (X ⊕ Y) :=
{ dist          := glue_dist Φ Ψ 0,
  dist_self     := glue_dist_self Φ Ψ 0,
  dist_comm     := glue_dist_comm Φ Ψ 0,
  dist_triangle := glue_dist_triangle Φ Ψ 0 $ λp q, by rw [hΦ.dist_eq, hΨ.dist_eq]; simp }

/-- Given two isometric embeddings `Φ : Z → X` and `Ψ : Z → Y`, we define a
space  `glue_space hΦ hΨ` by identifying in `X ⊕ Y` the points `Φ x` and `Ψ x`. -/
def glue_space (hΦ : isometry Φ) (hΨ : isometry Ψ) : Type* :=
@pseudo_metric_quot _ (glue_premetric hΦ hΨ)

instance metric_space_glue_space (hΦ : isometry Φ) (hΨ : isometry Ψ) :
  metric_space (glue_space hΦ hΨ) :=
@metric_space_quot _ (glue_premetric hΦ hΨ)

/-- The canonical map from `X` to the space obtained by gluing isometric subsets in `X` and `Y`. -/
def to_glue_l (hΦ : isometry Φ) (hΨ : isometry Ψ) (x : X) : glue_space hΦ hΨ :=
by letI : pseudo_metric_space (X ⊕ Y) := glue_premetric hΦ hΨ; exact ⟦inl x⟧

/-- The canonical map from `Y` to the space obtained by gluing isometric subsets in `X` and `Y`. -/
def to_glue_r (hΦ : isometry Φ) (hΨ : isometry Ψ) (y : Y) : glue_space hΦ hΨ :=
by letI : pseudo_metric_space (X ⊕ Y) := glue_premetric hΦ hΨ; exact ⟦inr y⟧

instance inhabited_left (hΦ : isometry Φ) (hΨ : isometry Ψ) [inhabited X] :
  inhabited (glue_space hΦ hΨ) :=
⟨to_glue_l _ _ default⟩

instance inhabited_right (hΦ : isometry Φ) (hΨ : isometry Ψ) [inhabited Y] :
  inhabited (glue_space hΦ hΨ) :=
⟨to_glue_r _ _ default⟩

lemma to_glue_commute (hΦ : isometry Φ) (hΨ : isometry Ψ) :
  (to_glue_l hΦ hΨ) ∘ Φ = (to_glue_r hΦ hΨ) ∘ Ψ :=
begin
  letI : pseudo_metric_space (X ⊕ Y) := glue_premetric hΦ hΨ,
  funext,
  simp only [comp, to_glue_l, to_glue_r, quotient.eq],
  exact glue_dist_glued_points Φ Ψ 0 x
end

lemma to_glue_l_isometry (hΦ : isometry Φ) (hΨ : isometry Ψ) : isometry (to_glue_l hΦ hΨ) :=
isometry_emetric_iff_metric.2 $ λ_ _, rfl

lemma to_glue_r_isometry (hΦ : isometry Φ) (hΨ : isometry Ψ) : isometry (to_glue_r hΦ hΨ) :=
isometry_emetric_iff_metric.2 $ λ_ _, rfl

end gluing --section

section inductive_limit
/- In this section, we define the inductive limit of
     f 0        f 1        f 2        f 3
X 0 -----> X 1 -----> X 2 -----> X 3 -----> ...
where the X n are metric spaces and f n isometric embeddings. We do it by defining a premetric
space structure on Σ n, X n, where the predistance dist x y is obtained by pushing x and y in a
common X k using composition by the f n, and taking the distance there. This does not depend on
the choice of k as the f n are isometries. The metric space associated to this premetric space
is the desired inductive limit.-/
open nat

variables {X : ℕ → Type u} [∀ n, metric_space (X n)] {f : Π n, X n → X (n+1)}

/-- Predistance on the disjoint union `Σ n, X n`. -/
def inductive_limit_dist (f : Π n, X n → X (n+1)) (x y : Σ n, X n) : ℝ :=
dist (le_rec_on (le_max_left  x.1 y.1) f x.2 : X (max x.1 y.1))
     (le_rec_on (le_max_right x.1 y.1) f y.2 : X (max x.1 y.1))

/-- The predistance on the disjoint union `Σ n, X n` can be computed in any `X k` for large
enough `k`. -/
lemma inductive_limit_dist_eq_dist (I : ∀ n, isometry (f n))
  (x y : Σ n, X n) (m : ℕ) : ∀ hx : x.1 ≤ m, ∀ hy : y.1 ≤ m,
  inductive_limit_dist f x y = dist (le_rec_on hx f x.2 : X m) (le_rec_on hy f y.2 : X m) :=
begin
  induction m with m hm,
  { assume hx hy,
    have A : max x.1 y.1 = 0, { rw [nonpos_iff_eq_zero.1 hx, nonpos_iff_eq_zero.1 hy], simp },
    unfold inductive_limit_dist,
    congr; simp only [A] },
  { assume hx hy,
    by_cases h : max x.1 y.1 = m.succ,
    { unfold inductive_limit_dist,
      congr; simp only [h] },
    { have : max x.1 y.1 ≤ succ m := by simp [hx, hy],
      have : max x.1 y.1 ≤ m := by simpa [h] using of_le_succ this,
      have xm : x.1 ≤ m := le_trans (le_max_left _ _) this,
      have ym : y.1 ≤ m := le_trans (le_max_right _ _) this,
      rw [le_rec_on_succ xm, le_rec_on_succ ym, (I m).dist_eq],
      exact hm xm ym }}
end

/-- Premetric space structure on `Σ n, X n`.-/
def inductive_premetric (I : ∀ n, isometry (f n)) :
  pseudo_metric_space (Σ n, X n) :=
{ dist          := inductive_limit_dist f,
  dist_self     := λx, by simp [dist, inductive_limit_dist],
  dist_comm     := λx y, begin
    let m := max x.1 y.1,
    have hx : x.1 ≤ m := le_max_left _ _,
    have hy : y.1 ≤ m := le_max_right _ _,
    unfold dist,
    rw [inductive_limit_dist_eq_dist I x y m hx hy, inductive_limit_dist_eq_dist I y x m hy hx,
        dist_comm]
  end,
  dist_triangle := λx y z, begin
    let m := max (max x.1 y.1) z.1,
    have hx : x.1 ≤ m := le_trans (le_max_left _ _) (le_max_left _ _),
    have hy : y.1 ≤ m := le_trans (le_max_right _ _) (le_max_left _ _),
    have hz : z.1 ≤ m := le_max_right _ _,
    calc inductive_limit_dist f x z
      = dist (le_rec_on hx f x.2 : X m) (le_rec_on hz f z.2 : X m) :
        inductive_limit_dist_eq_dist I x z m hx hz
      ... ≤ dist (le_rec_on hx f x.2 : X m) (le_rec_on hy f y.2 : X m)
          + dist (le_rec_on hy f y.2 : X m) (le_rec_on hz f z.2 : X m) :
        dist_triangle _ _ _
      ... = inductive_limit_dist f x y + inductive_limit_dist f y z :
         by rw [inductive_limit_dist_eq_dist I x y m hx hy,
                inductive_limit_dist_eq_dist I y z m hy hz]
  end }

local attribute [instance] inductive_premetric pseudo_metric.dist_setoid

/-- The type giving the inductive limit in a metric space context. -/
def inductive_limit (I : ∀ n, isometry (f n)) : Type* :=
@pseudo_metric_quot _ (inductive_premetric I)

/-- Metric space structure on the inductive limit. -/
instance metric_space_inductive_limit (I : ∀ n, isometry (f n)) :
  metric_space (inductive_limit I) :=
@metric_space_quot _ (inductive_premetric I)

/-- Mapping each `X n` to the inductive limit. -/
def to_inductive_limit (I : ∀ n, isometry (f n)) (n : ℕ) (x : X n) : metric.inductive_limit I :=
by letI : pseudo_metric_space (Σ n, X n) := inductive_premetric I; exact ⟦sigma.mk n x⟧

instance (I : ∀ n, isometry (f n)) [inhabited (X 0)] : inhabited (inductive_limit I) :=
⟨to_inductive_limit _ 0 default⟩

/-- The map `to_inductive_limit n` mapping `X n` to the inductive limit is an isometry. -/
lemma to_inductive_limit_isometry (I : ∀ n, isometry (f n)) (n : ℕ) :
  isometry (to_inductive_limit I n) := isometry_emetric_iff_metric.2 $ λx y,
begin
  change inductive_limit_dist f ⟨n, x⟩ ⟨n, y⟩ = dist x y,
  rw [inductive_limit_dist_eq_dist I ⟨n, x⟩ ⟨n, y⟩ n (le_refl n) (le_refl n),
      le_rec_on_self, le_rec_on_self]
end

/-- The maps `to_inductive_limit n` are compatible with the maps `f n`. -/
lemma to_inductive_limit_commute (I : ∀ n, isometry (f n)) (n : ℕ) :
  (to_inductive_limit I n.succ) ∘ (f n) = to_inductive_limit I n :=
begin
  funext,
  simp only [comp, to_inductive_limit, quotient.eq],
  show inductive_limit_dist f ⟨n.succ, f n x⟩ ⟨n, x⟩ = 0,
  { rw [inductive_limit_dist_eq_dist I ⟨n.succ, f n x⟩ ⟨n, x⟩ n.succ,
        le_rec_on_self, le_rec_on_succ, le_rec_on_self, dist_self],
    exact le_rfl,
    exact le_rfl,
    exact le_succ _ }
end

end inductive_limit --section
end metric --namespace
