/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Michael Stoll
-/
import number_theory.legendre_symbol.gauss_eisenstein_lemmas
import number_theory.legendre_symbol.quadratic_char

/-!
# Legendre symbol and quadratic reciprocity.

This file contains results about quadratic residues modulo a prime number.

We define the Legendre symbol `(a / p)` as `legendre_sym p a`.
Note the order of arguments! The advantage of this form is that then `legendre_sym p`
is a multiplicative map.

The main results are the law of quadratic reciprocity, `quadratic_reciprocity`, as well as the
interpretations in terms of existence of square roots depending on the congruence mod 4,
`exists_sq_eq_prime_iff_of_mod_four_eq_one`, and
`exists_sq_eq_prime_iff_of_mod_four_eq_three`.

Also proven are conditions for `-1` and `2` to be a square modulo a prime,
`exists_sq_eq_neg_one_iff` and
`exists_sq_eq_two_iff`

## Implementation notes

The proof of quadratic reciprocity implemented uses Gauss' lemma and Eisenstein's lemma
-/

open finset nat char

namespace zmod

variables (p q : ℕ) [fact p.prime] [fact q.prime]

/-- Euler's Criterion: A unit `x` of `zmod p` is a square if and only if `x ^ (p / 2) = 1`. -/
lemma euler_criterion_units (x : (zmod p)ˣ) :
  (∃ y : (zmod p)ˣ, y ^ 2 = x) ↔ x ^ (p / 2) = 1 :=
begin
  by_cases hc : p = 2,
  { substI hc,
    simp only [eq_iff_true_of_subsingleton, exists_const], },
  { have h₀ := finite_field.unit_is_square_iff (by rwa ring_char_zmod_n) x,
    have hs : (∃ y : (zmod p)ˣ, y ^ 2 = x) ↔ is_square(x) :=
    by { rw is_square_iff_exists_sq x,
         simp_rw eq_comm, },
    rw hs,
    rwa card p at h₀, },
end

/-- Euler's Criterion: a nonzero `a : zmod p` is a square if and only if `x ^ (p / 2) = 1`. -/
lemma euler_criterion {a : zmod p} (ha : a ≠ 0) :
  (∃ y : zmod p, y ^ 2 = a) ↔ a ^ (p / 2) = 1 :=
begin
  apply (iff_congr _ (by simp [units.ext_iff])).mp (euler_criterion_units p (units.mk0 a ha)),
  simp only [units.ext_iff, sq, units.coe_mk0, units.coe_mul],
  split, { rintro ⟨y, hy⟩, exact ⟨y, hy⟩ },
  { rintro ⟨y, rfl⟩,
    have hy : y ≠ 0, { rintro rfl, simpa [zero_pow] using ha, },
    refine ⟨units.mk0 y hy, _⟩, simp, }
end

-- The following is used by number_theory/zsqrtd/gaussian_int.lean and archive/imo/imo2008_q3.lean
lemma exists_sq_eq_neg_one_iff :
  (∃ y : zmod p, y ^ 2 = -1) ↔ p % 4 ≠ 3 :=
begin
  cases nat.prime.eq_two_or_odd (fact.out p.prime) with hp2 hp_odd,
  { substI p, exact dec_trivial },
  haveI := fact.mk hp_odd,
  have neg_one_ne_zero : (-1 : zmod p) ≠ 0, from mt neg_eq_zero.1 one_ne_zero,
  rw [euler_criterion p neg_one_ne_zero, neg_one_pow_eq_pow_mod_two],
  cases mod_two_eq_zero_or_one (p / 2) with p_half_even p_half_odd,
  { rw [p_half_even, pow_zero, eq_self_iff_true, true_iff],
    contrapose! p_half_even with hp,
    rw [← nat.mod_mul_right_div_self, show 2 * 2 = 4, from rfl, hp],
    exact dec_trivial },
  { rw [p_half_odd, pow_one,
        iff_false_intro (ne_neg_self p one_ne_zero).symm, false_iff, not_not],
    rw [← nat.mod_mul_right_div_self, show 2 * 2 = 4, from rfl] at p_half_odd,
    rw [← nat.mod_mul_left_mod _ 2, show 2 * 2 = 4, from rfl] at hp_odd,
    have hp : p % 4 < 4, from nat.mod_lt _ dec_trivial,
    revert hp hp_odd p_half_odd,
    generalize : p % 4 = k, dec_trivial! }
end

lemma mod_four_ne_three_of_sq_eq_neg_one {y : zmod p} (hy : y ^ 2 = -1) : p % 4 ≠ 3 :=
(exists_sq_eq_neg_one_iff p).1 ⟨y, hy⟩

lemma mod_four_ne_three_of_sq_eq_neg_sq' {x y : zmod p} (hy : y ≠ 0) (hxy : x ^ 2 = - y ^ 2) :
  p % 4 ≠ 3 :=
@mod_four_ne_three_of_sq_eq_neg_one p _ (x / y) begin
  apply_fun (λ z, z / y ^ 2) at hxy,
  rwa [neg_div, ←div_pow, ←div_pow, div_self hy, one_pow] at hxy
end

lemma mod_four_ne_three_of_sq_eq_neg_sq {x y : zmod p} (hx : x ≠ 0) (hxy : x ^ 2 = - y ^ 2) :
  p % 4 ≠ 3 :=
begin
  apply_fun (λ x, -x) at hxy,
  rw neg_neg at hxy,
  exact mod_four_ne_three_of_sq_eq_neg_sq' p hx hxy.symm
end

lemma pow_div_two_eq_neg_one_or_one {a : zmod p} (ha : a ≠ 0) :
  a ^ (p / 2) = 1 ∨ a ^ (p / 2) = -1 :=
begin
  cases nat.prime.eq_two_or_odd (fact.out p.prime) with hp2 hp_odd,
  { substI p, revert a ha, dec_trivial },
  rw [← mul_self_eq_one_iff, ← pow_add, ← two_mul, two_mul_odd_div_two hp_odd],
  exact pow_card_sub_one_eq_one ha
end

/-- The Legendre symbol of `a : ℤ` and a prime `p`, `legendre_sym p a`,
is an integer defined as

* `0` if `a` is `0` modulo `p`;
* `1` if `a` is a square modulo `p`
* `-1` otherwise.

Note the order of the arguments! The advantage of the order chosen here is
that `legendre_sym p` is a multiplicative function `ℤ → ℤ`.
-/
def legendre_sym (p : ℕ) [fact p.prime] (a : ℤ) : ℤ := quadratic_char (zmod p) a

/-- We have the congruence `legendre_sym p a ≡ a ^ (p / 2) mod p`. -/
lemma legendre_sym_eq_pow (p : ℕ) (a : ℤ) [hp : fact p.prime] :
  (legendre_sym p a : zmod p) = (a ^ (p / 2)) :=
begin
  rw legendre_sym,
  by_cases ha : (a : zmod p) = 0,
  { simp only [ha, zero_pow (nat.div_pos (hp.1.two_le) (succ_pos 1)), quadratic_char_zero,
               int.cast_zero], },
  by_cases hp₁ : p = 2,
  { substI p,
    generalize : (a : (zmod 2)) = b, revert b, dec_trivial, },
  { have h₁ := quadratic_char_eq_pow_of_char_ne_two (by rwa ring_char_zmod_n p) ha,
    rw card p at h₁,
    rw h₁,
    have h₂ := finite_field.neg_one_ne_one_of_char_ne_two (by rwa ring_char_zmod_n p),
    cases pow_div_two_eq_neg_one_or_one p ha with h h,
    { rw [if_pos h, h, int.cast_one], },
    { rw [h, if_neg h₂, int.cast_neg, int.cast_one], } }
end

/-- If `p ∤ a`, then `legendre_sym p a` is `1` or `-1`. -/
lemma legendre_sym_eq_one_or_neg_one (p : ℕ) [fact p.prime] (a : ℤ) (ha : (a : zmod p) ≠ 0) :
  legendre_sym p a = 1 ∨ legendre_sym p a = -1 :=
quadratic_char_dichotomy ha

lemma legendre_sym_eq_neg_one_iff_not_one {a : ℤ} (ha : (a : zmod p) ≠ 0) :
  legendre_sym p a = -1 ↔ ¬ legendre_sym p a = 1 :=
quadratic_char_eq_neg_one_iff_not_one ha

/-- The Legendre symbol of `p` and `a` is zero iff `p ∣ a`. -/
lemma legendre_sym_eq_zero_iff (p : ℕ) [fact p.prime] (a : ℤ) :
  legendre_sym p a = 0 ↔ (a : zmod p) = 0 :=
quadratic_char_eq_zero_iff a

@[simp] lemma legendre_sym_zero (p : ℕ) [fact p.prime] : legendre_sym p 0 = 0 :=
begin
  rw legendre_sym,
  exact quadratic_char_zero,
end

@[simp] lemma legendre_sym_one (p : ℕ) [fact p.prime] : legendre_sym p 1 = 1 :=
begin
  rw [legendre_sym, (by norm_cast : ((1 : ℤ) : zmod p) = 1)],
  exact quadratic_char_one,
end

/-- The Legendre symbol is multiplicative in `a` for `p` fixed. -/
lemma legendre_sym_mul (p : ℕ) [fact p.prime] (a b : ℤ) :
  legendre_sym p (a * b) = legendre_sym p a * legendre_sym p b :=
begin
  rw [legendre_sym, legendre_sym, legendre_sym],
  push_cast,
  exact quadratic_char_mul (a : zmod p) b,
end

/-- The Legendre symbol is a homomorphism of monoids with zero. -/
@[simps] def legendre_sym_hom (p : ℕ) [fact p.prime] : ℤ →*₀ ℤ :=
{ to_fun := legendre_sym p,
  map_zero' := legendre_sym_zero p,
  map_one' := legendre_sym_one p,
  map_mul' := legendre_sym_mul p }

/-- The square of the symbol is 1 if `p ∤ a`. -/
theorem legendre_sym_sq_one (p : ℕ) [fact p.prime] (a : ℤ) (ha : (a : zmod p) ≠ 0) :
  (legendre_sym p a)^2 = 1 :=
quadratic_char_sq_one ha

/-- The Legendre symbol of `a^2` at `p` is 1 if `p ∤ a`. -/
theorem legendre_sym_sq_one'  (p : ℕ) [fact p.prime] (a : ℤ) (ha : (a : zmod p) ≠ 0) :
  legendre_sym p (a ^ 2) = 1 :=
begin
  rw [legendre_sym],
  push_cast,
  exact quadratic_char_sq_one' ha,
end

/-- The Legendre symbol depends only on `a` mod `p`. -/
theorem legendre_sym_mod (p : ℕ) [fact p.prime] (a : ℤ) :
  legendre_sym p a = legendre_sym p (a % p) :=
by simp only [legendre_sym, int_cast_mod]


/-- Gauss' lemma. The legendre symbol can be computed by considering the number of naturals less
  than `p/2` such that `(a * x) % p > p / 2` -/
lemma gauss_lemma {a : ℤ} (hp : p ≠ 2) (ha0 : (a : zmod p) ≠ 0) :
  legendre_sym p a = (-1) ^ ((Ico 1 (p / 2).succ).filter
    (λ x : ℕ, p / 2 < (a * x : zmod p).val)).card :=
begin
  haveI hp' : fact (p % 2 = 1) := ⟨nat.prime.mod_two_eq_one_iff_ne_two.mpr hp⟩,
  have : (legendre_sym p a : zmod p) = (((-1)^((Ico 1 (p / 2).succ).filter
    (λ x : ℕ, p / 2 < (a * x : zmod p).val)).card : ℤ) : zmod p) :=
    by { rw [legendre_sym_eq_pow, legendre_symbol.gauss_lemma_aux p ha0]; simp },
  cases legendre_sym_eq_one_or_neg_one p a ha0;
  cases neg_one_pow_eq_or ℤ ((Ico 1 (p / 2).succ).filter
    (λ x : ℕ, p / 2 < (a * x : zmod p).val)).card;
  simp [*, ne_neg_self p one_ne_zero, (ne_neg_self p one_ne_zero).symm] at *
end

/-- When `p ∤ a`, then `legendre_sym p a = 1` iff `a` is a square mod `p`. -/
lemma legendre_sym_eq_one_iff {a : ℤ} (ha0 : (a : zmod p) ≠ 0) :
  legendre_sym p a = 1 ↔ is_square (a : zmod p) :=
quadratic_char_one_iff_is_square ha0

/-- `legendre_sym p a = -1` iff`a` is a nonsquare mod `p`. -/
lemma legendre_sym_eq_neg_one_iff {a : ℤ} :
  legendre_sym p a = -1 ↔ ¬ is_square (a : zmod p) :=
quadratic_char_neg_one_iff_not_is_square

/-- The number of square roots of `a` modulo `p` is determined by the Legendre symbol. -/
lemma legendre_sym_card_sqrts (hp : p ≠ 2) (a : ℤ) :
  ↑{x : zmod p | x^2 = a}.to_finset.card = legendre_sym p a + 1 :=
begin
  have h : ring_char (zmod p) ≠ 2 := by { rw ring_char_zmod_n, exact hp, },
  exact quadratic_char_card_sqrts h a,
end

open_locale big_operators

lemma eisenstein_lemma (hp : p ≠ 2) {a : ℕ} (ha1 : a % 2 = 1) (ha0 : (a : zmod p) ≠ 0) :
  legendre_sym p a = (-1)^∑ x in Ico 1 (p / 2).succ, (x * a) / p :=
begin
  haveI hp' : fact (p % 2 = 1) := ⟨nat.prime.mod_two_eq_one_iff_ne_two.mpr hp⟩,
  have ha0' : ((a : ℤ) : zmod p) ≠ 0 := by { norm_cast, exact ha0 },
  rw [neg_one_pow_eq_pow_mod_two, gauss_lemma p hp ha0', neg_one_pow_eq_pow_mod_two,
      (by norm_cast : ((a : ℤ) : zmod p) = (a : zmod p)),
      show _ = _, from legendre_symbol.eisenstein_lemma_aux p ha1 ha0]
end

/-- **Quadratic reciprocity theorem** -/
theorem quadratic_reciprocity (hp1 : p ≠ 2) (hq1 : q ≠ 2) (hpq : p ≠ q) :
  legendre_sym q p * legendre_sym p q = (-1) ^ ((p / 2) * (q / 2)) :=
have hpq0 : (p : zmod q) ≠ 0, from prime_ne_zero q p hpq.symm,
have hqp0 : (q : zmod p) ≠ 0, from prime_ne_zero p q hpq,
by rw [eisenstein_lemma q hq1 (nat.prime.mod_two_eq_one_iff_ne_two.mpr hp1) hpq0,
       eisenstein_lemma p hp1 (nat.prime.mod_two_eq_one_iff_ne_two.mpr hq1) hqp0,
  ← pow_add, legendre_symbol.sum_mul_div_add_sum_mul_div_eq_mul q p hpq0, mul_comm]

lemma legendre_sym_two (hp2 : p ≠ 2) : legendre_sym p 2 = (-1) ^ (p / 4 + p / 2) :=
begin
  have hp1 := nat.prime.mod_two_eq_one_iff_ne_two.mpr hp2,
  have hp22 : p / 2 / 2 = _ := legendre_symbol.div_eq_filter_card (show 0 < 2, from dec_trivial)
    (nat.div_le_self (p / 2) 2),
  have hcard : (Ico 1 (p / 2).succ).card = p / 2, by simp,
  have hx2 : ∀ x ∈ Ico 1 (p / 2).succ, (2 * x : zmod p).val = 2 * x,
    from λ x hx, have h2xp : 2 * x < p,
        from calc 2 * x ≤ 2 * (p / 2) : mul_le_mul_of_nonneg_left
          (le_of_lt_succ $ (mem_Ico.mp hx).2) dec_trivial
        ... < _ : by conv_rhs {rw [← div_add_mod p 2, hp1]}; exact lt_succ_self _,
      by rw [← nat.cast_two, ← nat.cast_mul, val_cast_of_lt h2xp],
  have hdisj : disjoint
      ((Ico 1 (p / 2).succ).filter (λ x, p / 2 < ((2 : ℕ) * x : zmod p).val))
      ((Ico 1 (p / 2).succ).filter (λ x, x * 2 ≤ p / 2)),
    from disjoint_filter.2 (λ x hx, by simp [hx2 _ hx, mul_comm]),
  have hunion :
      ((Ico 1 (p / 2).succ).filter (λ x, p / 2 < ((2 : ℕ) * x : zmod p).val)) ∪
      ((Ico 1 (p / 2).succ).filter (λ x, x * 2 ≤ p / 2)) =
      Ico 1 (p / 2).succ,
    begin
      rw [filter_union_right],
      conv_rhs {rw [← @filter_true _ (Ico 1 (p / 2).succ)]},
      exact filter_congr (λ x hx, by simp [hx2 _ hx, lt_or_le, mul_comm])
    end,
  have hp2' := prime_ne_zero p 2 hp2,
  rw (by norm_cast : ((2 : ℕ) : zmod p) = (2 : ℤ)) at *,
  erw [gauss_lemma p hp2 hp2',
      neg_one_pow_eq_pow_mod_two, @neg_one_pow_eq_pow_mod_two _ _ (p / 4 + p / 2)],
  refine congr_arg2 _ rfl ((eq_iff_modeq_nat 2).1 _),
  rw [show 4 = 2 * 2, from rfl, ← nat.div_div_eq_div_mul, hp22, nat.cast_add,
      ← sub_eq_iff_eq_add', sub_eq_add_neg, neg_eq_self_mod_two,
      ← nat.cast_add, ← card_disjoint_union hdisj, hunion, hcard]
end

lemma exists_sq_eq_two_iff (hp1 : p ≠ 2) :
  is_square (2 : zmod p) ↔ p % 8 = 1 ∨ p % 8 = 7 :=
begin
  have hp2 : ((2 : ℤ) : zmod p) ≠ 0,
    from prime_ne_zero p 2 (λ h, by simpa [h] using hp1),
  have hpm4 : p % 4 = p % 8 % 4, from (nat.mod_mul_left_mod p 2 4).symm,
  have hpm2 : p % 2 = p % 8 % 2, from (nat.mod_mul_left_mod p 4 2).symm,
  rw [show (2 : zmod p) = (2 : ℤ), by simp, ← legendre_sym_eq_one_iff p hp2],
  erw [legendre_sym_two p hp1, neg_one_pow_eq_one_iff_even (show (-1 : ℤ) ≠ 1, from dec_trivial),
    even_add, even_div, even_div],
  have := nat.mod_lt p (show 0 < 8, from dec_trivial),
  have hp := nat.prime.mod_two_eq_one_iff_ne_two.mpr hp1,
  revert this hp,
  erw [hpm4, hpm2],
  generalize hm : p % 8 = m, unfreezingI {clear_dependent p},
  dec_trivial!,
end

lemma exists_sq_eq_prime_iff_of_mod_four_eq_one (hp1 : p % 4 = 1) (hq1 : q ≠ 2) :
  is_square (q : zmod p) ↔ is_square (p : zmod q) :=
if hpq : p = q then by substI hpq else
have h1 : ((p / 2) * (q / 2)) % 2 = 0,
  from (dvd_iff_mod_eq_zero _ _).1
    (dvd_mul_of_dvd_left ((dvd_iff_mod_eq_zero _ _).2 $
    by rw [← mod_mul_right_div_self, show 2 * 2 = 4, from rfl, hp1]; refl) _),
begin
  have hp_odd : p ≠ 2 := by { by_contra, simp [h] at hp1, norm_num at hp1, },
  have hpq0 : ((p : ℤ) : zmod q) ≠ 0 := prime_ne_zero q p (ne.symm hpq),
  have hqp0 : ((q : ℤ) : zmod p) ≠ 0 := prime_ne_zero p q hpq,
  have := quadratic_reciprocity p q hp_odd hq1 hpq,
  rw [neg_one_pow_eq_pow_mod_two, h1, pow_zero] at this,
  rw [(by norm_cast : (p : zmod q) = (p : ℤ)), (by norm_cast : (q : zmod p) = (q : ℤ)),
       ← legendre_sym_eq_one_iff _ hpq0, ← legendre_sym_eq_one_iff _ hqp0],
  cases (legendre_sym_eq_one_or_neg_one p q hqp0) with h h,
  { simp only [h, eq_self_iff_true, true_iff, mul_one] at this ⊢,
    exact this, },
  { simp only [h, mul_neg, mul_one] at this ⊢,
    rw eq_neg_of_eq_neg this.symm, },
end

lemma exists_sq_eq_prime_iff_of_mod_four_eq_three (hp3 : p % 4 = 3)
  (hq3 : q % 4 = 3) (hpq : p ≠ q) : is_square (q : zmod p) ↔ ¬ is_square (p : zmod q) :=
have h1 : ((p / 2) * (q / 2)) % 2 = 1,
  from nat.odd_mul_odd
    (by rw [← mod_mul_right_div_self, show 2 * 2 = 4, from rfl, hp3]; refl)
    (by rw [← mod_mul_right_div_self, show 2 * 2 = 4, from rfl, hq3]; refl),
begin
  have hp_odd : p ≠ 2 := by { by_contra, simp [h] at hp3, norm_num at hp3, },
  have hq_odd : q ≠ 2 := by { by_contra, simp [h] at hq3, norm_num at hq3, },
  have hpq0 : ((p : ℤ) : zmod q) ≠ 0 := prime_ne_zero q p (ne.symm hpq),
  have hqp0 : ((q : ℤ) : zmod p) ≠ 0 := prime_ne_zero p q hpq,
  have := quadratic_reciprocity p q hp_odd hq_odd hpq,
  rw [neg_one_pow_eq_pow_mod_two, h1, pow_one] at this,
  rw [(by norm_cast : (p : zmod q) = (p : ℤ)), (by norm_cast : (q : zmod p) = (q : ℤ)),
       ← legendre_sym_eq_one_iff _ hpq0, ← legendre_sym_eq_one_iff _ hqp0],
  cases (legendre_sym_eq_one_or_neg_one q p hpq0) with h h,
  { simp only [h, eq_self_iff_true, not_true, iff_false, one_mul] at this ⊢,
    simp only [this],
    norm_num, },
  { simp only [h, neg_mul, one_mul, neg_inj] at this ⊢,
    simp only [this, eq_self_iff_true, true_iff],
    norm_num, },
end

end zmod
