/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Yaël Dillies
-/
import linear_algebra.ray
import analysis.normed_space.basic

/-!
# Rays in a real normed vector space

In this file we prove some lemmas about the `same_ray` predicate in case of a real normed space. In
this case, for two vectors `x y` in the same ray, the norm of their sum is equal to the sum of their
norms and `∥y∥ • x = ∥x∥ • y`.
-/

open real

variables {E : Type*} [semi_normed_group E] [normed_space ℝ E]
  {F : Type*} [normed_group F] [normed_space ℝ F]

namespace same_ray

variables {x y : E}

/-- If `x` and `y` are on the same ray, then the triangle inequality becomes the equality: the norm
of `x + y` is the sum of the norms of `x` and `y`. The converse is true for a strictly convex
space. -/
lemma norm_add (h : same_ray ℝ x y) : ∥x + y∥ = ∥x∥ + ∥y∥ :=
begin
  rcases h.exists_eq_smul with ⟨u, a, b, ha, hb, -, rfl, rfl⟩,
  rw [← add_smul, norm_smul_of_nonneg (add_nonneg ha hb), norm_smul_of_nonneg ha,
    norm_smul_of_nonneg hb, add_mul]
end

lemma norm_sub (h : same_ray ℝ x y) : ∥x - y∥ = |∥x∥ - ∥y∥| :=
begin
  rcases h.exists_eq_smul with ⟨u, a, b, ha, hb, -, rfl, rfl⟩,
  wlog hab : b ≤ a := le_total b a using [a b, b a] tactic.skip,
  { rw ← sub_nonneg at hab,
    rw [← sub_smul, norm_smul_of_nonneg hab, norm_smul_of_nonneg ha,
      norm_smul_of_nonneg hb, ← sub_mul, abs_of_nonneg (mul_nonneg hab (norm_nonneg _))] },
  { intros ha hb hab,
    rw [norm_sub_rev, this hb ha hab.symm, abs_sub_comm] }
end

lemma norm_smul_eq (h : same_ray ℝ x y) : ∥x∥ • y = ∥y∥ • x :=
begin
  rcases h.exists_eq_smul with ⟨u, a, b, ha, hb, -, rfl, rfl⟩,
  simp only [norm_smul_of_nonneg, *, mul_smul, smul_comm (∥u∥)],
  apply smul_comm
end

end same_ray

variables {x y : F}

lemma norm_inj_on_ray_left (hx : x ≠ 0) : {y | same_ray ℝ x y}.inj_on norm :=
begin
  rintro y hy z hz h,
  rcases hy.exists_nonneg_left hx with ⟨r, hr, rfl⟩,
  rcases hz.exists_nonneg_left hx with ⟨s, hs, rfl⟩,
  rw [norm_smul, norm_smul, mul_left_inj' (norm_ne_zero_iff.2 hx), norm_of_nonneg hr,
    norm_of_nonneg hs] at h,
  rw h
end

lemma norm_inj_on_ray_right (hy : y ≠ 0) : {x | same_ray ℝ x y}.inj_on norm :=
by simpa only [same_ray_comm] using norm_inj_on_ray_left hy

lemma same_ray_iff_norm_smul_eq : same_ray ℝ x y ↔ ∥x∥ • y = ∥y∥ • x :=
⟨same_ray.norm_smul_eq, λ h, or_iff_not_imp_left.2 $ λ hx, or_iff_not_imp_left.2 $ λ hy,
  ⟨∥y∥, ∥x∥, norm_pos_iff.2 hy, norm_pos_iff.2 hx, h.symm⟩⟩

/-- Two nonzero vectors `x y` in a real normed space are on the same ray if and only if the unit
vectors `∥x∥⁻¹ • x` and `∥y∥⁻¹ • y` are equal. -/
lemma same_ray_iff_inv_norm_smul_eq_of_ne (hx : x ≠ 0) (hy : y ≠ 0) :
  same_ray ℝ x y ↔ ∥x∥⁻¹ • x = ∥y∥⁻¹ • y :=
by rw [inv_smul_eq_iff₀, smul_comm, eq_comm, inv_smul_eq_iff₀, same_ray_iff_norm_smul_eq];
    rwa norm_ne_zero_iff

alias same_ray_iff_inv_norm_smul_eq_of_ne ↔ same_ray.inv_norm_smul_eq _

/-- Two vectors `x y` in a real normed space are on the ray if and only if one of them is zero or
the unit vectors `∥x∥⁻¹ • x` and `∥y∥⁻¹ • y` are equal. -/
lemma same_ray_iff_inv_norm_smul_eq : same_ray ℝ x y ↔ x = 0 ∨ y = 0 ∨ ∥x∥⁻¹ • x = ∥y∥⁻¹ • y :=
begin
  rcases eq_or_ne x 0 with rfl|hx, { simp [same_ray.zero_left] },
  rcases eq_or_ne y 0 with rfl|hy, { simp [same_ray.zero_right] },
  simp only [same_ray_iff_inv_norm_smul_eq_of_ne hx hy, *, false_or]
end

lemma same_ray_iff_of_norm_eq (h : ∥x∥ = ∥y∥) : same_ray ℝ x y ↔ x = y :=
begin
  obtain rfl | hy := eq_or_ne y 0,
  { rw [norm_zero, norm_eq_zero] at h,
    exact iff_of_true (same_ray.zero_right _) h },
  { exact ⟨λ hxy, norm_inj_on_ray_right hy hxy same_ray.rfl h, λ hxy, hxy ▸ same_ray.rfl⟩ }
end

lemma not_same_ray_iff_of_norm_eq (h : ∥x∥ = ∥y∥) : ¬ same_ray ℝ x y ↔ x ≠ y :=
(same_ray_iff_of_norm_eq h).not
