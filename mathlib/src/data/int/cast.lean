/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.int.basic
import data.nat.cast

/-!
# Cast of integers

This file defines the *canonical* homomorphism from the integers into a type `α` with `0`,
`1`, `+` and `-` (typically a `ring`).

## Main declarations

* `cast`: Canonical homomorphism `ℤ → α` where `α` has a `0`, `1`, `+` and `-`.
* `cast_add_hom`: `cast` bundled as an `add_monoid_hom`.
* `cast_ring_hom`: `cast` bundled as a `ring_hom`.

## Implementation note

Setting up the coercions priorities is tricky. See Note [coercion into rings].
-/

open nat

namespace int

@[simp, push_cast] theorem nat_cast_eq_coe_nat : ∀ n,
  @coe ℕ ℤ (@coe_to_lift _ _ nat.cast_coe) n =
  @coe ℕ ℤ (@coe_to_lift _ _ (@coe_base _ _ int.has_coe)) n
| 0     := rfl
| (n+1) := congr_arg (+(1:ℤ)) (nat_cast_eq_coe_nat n)

/-- Coercion `ℕ → ℤ` as a `ring_hom`. -/
def of_nat_hom : ℕ →+* ℤ := ⟨coe, rfl, int.of_nat_mul, rfl, int.of_nat_add⟩

section cast
variables {α : Type*}

section
variables [has_zero α] [has_one α] [has_add α] [has_neg α]

/-- Canonical homomorphism from the integers to any ring(-like) structure `α` -/
protected def cast : ℤ → α
| (n : ℕ) := n
| -[1+ n] := -(n+1)

-- see Note [coercion into rings]
@[priority 900] instance cast_coe : has_coe_t ℤ α := ⟨int.cast⟩

@[simp, norm_cast] theorem cast_zero : ((0 : ℤ) : α) = 0 := rfl

theorem cast_of_nat (n : ℕ) : (of_nat n : α) = n := rfl
@[simp, norm_cast] theorem cast_coe_nat (n : ℕ) : ((n : ℤ) : α) = n := rfl
theorem cast_coe_nat' (n : ℕ) :
  (@coe ℕ ℤ (@coe_to_lift _ _ nat.cast_coe) n : α) = n :=
by simp

@[simp, norm_cast] theorem cast_neg_succ_of_nat (n : ℕ) : (-[1+ n] : α) = -(n + 1) := rfl

end

@[simp, norm_cast] theorem cast_one [add_monoid α] [has_one α] [has_neg α] :
  ((1 : ℤ) : α) = 1 := nat.cast_one

@[simp] theorem cast_sub_nat_nat [add_group α] [has_one α] (m n) :
  ((int.sub_nat_nat m n : ℤ) : α) = m - n :=
begin
  unfold sub_nat_nat, cases e : n - m,
  { simp [sub_nat_nat, e, tsub_eq_zero_iff_le.mp e] },
  { rw [sub_nat_nat, cast_neg_succ_of_nat, ← nat.cast_succ, ← e,
        nat.cast_sub $ _root_.le_of_lt $ nat.lt_of_sub_eq_succ e, neg_sub] },
end

@[simp, norm_cast] theorem cast_neg_of_nat [add_group α] [has_one α] :
  ∀ n, ((neg_of_nat n : ℤ) : α) = -n
| 0     := neg_zero.symm
| (n+1) := rfl

@[simp, norm_cast] theorem cast_add [add_group α] [has_one α] : ∀ m n, ((m + n : ℤ) : α) = m + n
| (m : ℕ) (n : ℕ) := nat.cast_add _ _
| (m : ℕ) -[1+ n] := by simpa only [sub_eq_add_neg] using cast_sub_nat_nat _ _
| -[1+ m] (n : ℕ) := (cast_sub_nat_nat _ _).trans $ sub_eq_of_eq_add $
  show (n:α) = -(m+1) + n + (m+1),
  by rw [add_assoc, ← cast_succ, ← nat.cast_add, add_comm,
         nat.cast_add, cast_succ, neg_add_cancel_left]
| -[1+ m] -[1+ n] := show -((m + n + 1 + 1 : ℕ) : α) = -(m + 1) + -(n + 1),
  begin
    rw [← neg_add_rev, ← nat.cast_add_one, ← nat.cast_add_one, ← nat.cast_add],
    apply congr_arg (λ x:ℕ, -(x:α)),
    ac_refl
  end

@[simp, norm_cast] theorem cast_neg [add_group α] [has_one α] : ∀ n, ((-n : ℤ) : α) = -n
| (n : ℕ) := cast_neg_of_nat _
| -[1+ n] := (neg_neg _).symm

@[simp, norm_cast] theorem cast_sub [add_group α] [has_one α] (m n) : ((m - n : ℤ) : α) = m - n :=
by simp [sub_eq_add_neg]

@[simp, norm_cast] theorem cast_mul [ring α] : ∀ m n, ((m * n : ℤ) : α) = m * n
| (m : ℕ) (n : ℕ) := nat.cast_mul _ _
| (m : ℕ) -[1+ n] := (cast_neg_of_nat _).trans $
  show (-(m * (n + 1) : ℕ) : α) = m * -(n + 1),
  by rw [nat.cast_mul, nat.cast_add_one, neg_mul_eq_mul_neg]
| -[1+ m] (n : ℕ) := (cast_neg_of_nat _).trans $
  show (-((m + 1) * n : ℕ) : α) = -(m + 1) * n,
  by rw [nat.cast_mul, nat.cast_add_one, neg_mul_eq_neg_mul]
| -[1+ m] -[1+ n] := show (((m + 1) * (n + 1) : ℕ) : α) = -(m + 1) * -(n + 1),
  by rw [nat.cast_mul, nat.cast_add_one, nat.cast_add_one, neg_mul_neg]

@[simp] theorem cast_div [field α] {m n : ℤ} (n_dvd : n ∣ m) (n_nonzero : (n : α) ≠ 0) :
  ((m / n : ℤ) : α) = m / n :=
begin
  rcases n_dvd with ⟨k, rfl⟩,
  have : n ≠ 0, { rintro rfl, simpa using n_nonzero },
  rw [int.mul_div_cancel_left _ this, int.cast_mul, mul_div_cancel_left _ n_nonzero],
end

/-- `coe : ℤ → α` as an `add_monoid_hom`. -/
def cast_add_hom (α : Type*) [add_group α] [has_one α] : ℤ →+ α := ⟨coe, cast_zero, cast_add⟩

@[simp] lemma coe_cast_add_hom [add_group α] [has_one α] : ⇑(cast_add_hom α) = coe := rfl

/-- `coe : ℤ → α` as a `ring_hom`. -/
def cast_ring_hom (α : Type*) [ring α] : ℤ →+* α := ⟨coe, cast_one, cast_mul, cast_zero, cast_add⟩

@[simp] lemma coe_cast_ring_hom [ring α] : ⇑(cast_ring_hom α) = coe := rfl

lemma cast_commute [ring α] (m : ℤ) (x : α) : commute ↑m x :=
int.cases_on m (λ n, n.cast_commute x) (λ n, ((n+1).cast_commute x).neg_left)

lemma cast_comm [ring α] (m : ℤ) (x : α) : (m : α) * x = x * m :=
(cast_commute m x).eq

lemma commute_cast [ring α] (x : α) (m : ℤ) : commute x m :=
(m.cast_commute x).symm

@[simp, norm_cast]
theorem coe_nat_bit0 (n : ℕ) : (↑(bit0 n) : ℤ) = bit0 ↑n := by {unfold bit0, simp}

@[simp, norm_cast]
theorem coe_nat_bit1 (n : ℕ) : (↑(bit1 n) : ℤ) = bit1 ↑n := by {unfold bit1, unfold bit0, simp}

@[simp, norm_cast] theorem cast_bit0 [ring α] (n : ℤ) : ((bit0 n : ℤ) : α) = bit0 n := cast_add _ _

@[simp, norm_cast] theorem cast_bit1 [ring α] (n : ℤ) : ((bit1 n : ℤ) : α) = bit1 n :=
by rw [bit1, cast_add, cast_one, cast_bit0]; refl

lemma cast_two [ring α] : ((2 : ℤ) : α) = 2 := by simp

lemma cast_three [ring α] : ((3 : ℤ) : α) = 3 := by simp

lemma cast_four [ring α] : ((4 : ℤ) : α) = 4 := by simp

theorem cast_mono [ordered_ring α] : monotone (coe : ℤ → α) :=
begin
  intros m n h,
  rw ← sub_nonneg at h,
  lift n - m to ℕ using h with k,
  rw [← sub_nonneg, ← cast_sub, ← h_1, cast_coe_nat],
  exact k.cast_nonneg
end

@[simp] theorem cast_nonneg [ordered_ring α] [nontrivial α] : ∀ {n : ℤ}, (0 : α) ≤ n ↔ 0 ≤ n
| (n : ℕ) := by simp
| -[1+ n] := have -(n:α) < 1, from lt_of_le_of_lt (by simp) zero_lt_one,
             by simpa [(neg_succ_lt_zero n).not_le, ← sub_eq_add_neg, le_neg] using this.not_le

@[simp, norm_cast] theorem cast_le [ordered_ring α] [nontrivial α] {m n : ℤ} :
  (m : α) ≤ n ↔ m ≤ n :=
by rw [← sub_nonneg, ← cast_sub, cast_nonneg, sub_nonneg]

theorem cast_strict_mono [ordered_ring α] [nontrivial α] : strict_mono (coe : ℤ → α) :=
strict_mono_of_le_iff_le $ λ m n, cast_le.symm

@[simp, norm_cast] theorem cast_lt [ordered_ring α] [nontrivial α] {m n : ℤ} :
  (m : α) < n ↔ m < n :=
cast_strict_mono.lt_iff_lt

@[simp] theorem cast_nonpos [ordered_ring α] [nontrivial α] {n : ℤ} : (n : α) ≤ 0 ↔ n ≤ 0 :=
by rw [← cast_zero, cast_le]

@[simp] theorem cast_pos [ordered_ring α] [nontrivial α] {n : ℤ} : (0 : α) < n ↔ 0 < n :=
by rw [← cast_zero, cast_lt]

@[simp] theorem cast_lt_zero [ordered_ring α] [nontrivial α] {n : ℤ} : (n : α) < 0 ↔ n < 0 :=
by rw [← cast_zero, cast_lt]

section linear_ordered_ring

variables [linear_ordered_ring α] {a b : ℤ} (n : ℤ)

@[simp, norm_cast] theorem cast_min : (↑(min a b) : α) = min a b :=
monotone.map_min cast_mono

@[simp, norm_cast] theorem cast_max : (↑(max a b) : α) = max a b :=
monotone.map_max cast_mono

@[simp, norm_cast] theorem cast_abs : ((|a| : ℤ) : α) = |a| :=
by simp [abs_eq_max_neg]

lemma cast_one_le_of_pos (h : 0 < a) : (1 : α) ≤ a :=
by exact_mod_cast int.add_one_le_of_lt h

lemma cast_le_neg_one_of_neg (h : a < 0) : (a : α) ≤ -1 :=
by exact_mod_cast int.le_sub_one_of_lt h

lemma nneg_mul_add_sq_of_abs_le_one {x : α} (hx : |x| ≤ 1) :
  (0 : α) ≤ n * x + n * n :=
begin
  have hnx : 0 < n → 0 ≤ x + n := λ hn, by
  { convert add_le_add (neg_le_of_abs_le hx) (cast_one_le_of_pos hn),
    rw add_left_neg, },
  have hnx' : n < 0 → x + n ≤ 0 := λ hn, by
  { convert add_le_add (le_of_abs_le hx) (cast_le_neg_one_of_neg hn),
    rw add_right_neg, },
  rw [← mul_add, mul_nonneg_iff],
  rcases lt_trichotomy n 0 with h | rfl | h,
  { exact or.inr ⟨by exact_mod_cast h.le, hnx' h⟩, },
  { simp [le_total 0 x], },
  { exact or.inl ⟨by exact_mod_cast h.le, hnx h⟩, },
end

lemma cast_nat_abs : (n.nat_abs : α) = |n| :=
begin
  cases n,
  { simp, },
  { simp only [int.nat_abs, int.cast_neg_succ_of_nat, abs_neg, ← nat.cast_succ, nat.abs_cast], },
end

end linear_ordered_ring

lemma coe_int_dvd [comm_ring α] (m n : ℤ) (h : m ∣ n) :
  (m : α) ∣ (n : α) :=
ring_hom.map_dvd (int.cast_ring_hom α) h

end cast

end int

namespace prod

variables {α : Type*} {β : Type*} [has_zero α] [has_one α] [has_add α] [has_neg α]
  [has_zero β] [has_one β] [has_add β] [has_neg β]

@[simp] lemma fst_int_cast (n : ℤ) : (n : α × β).fst = n :=
by induction n; simp *

@[simp] lemma snd_int_cast (n : ℤ) : (n : α × β).snd = n :=
by induction n; simp *

end prod

open int

namespace add_monoid_hom

variables {A : Type*}

/-- Two additive monoid homomorphisms `f`, `g` from `ℤ` to an additive monoid are equal
if `f 1 = g 1`. -/
@[ext] theorem ext_int [add_monoid A] {f g : ℤ →+ A} (h1 : f 1 = g 1) : f = g :=
have f.comp (int.of_nat_hom : ℕ →+ ℤ) = g.comp (int.of_nat_hom : ℕ →+ ℤ) := ext_nat' _ _ h1,
have ∀ n : ℕ, f n = g n := ext_iff.1 this,
ext $ λ n, int.cases_on n this $ λ n, eq_on_neg (this $ n + 1)

variables [add_group A] [has_one A]

theorem eq_int_cast_hom (f : ℤ →+ A) (h1 : f 1 = 1) : f = int.cast_add_hom A :=
ext_int $ by simp [h1]

theorem eq_int_cast (f : ℤ →+ A) (h1 : f 1 = 1) : ∀ n : ℤ, f n = n :=
ext_iff.1 (f.eq_int_cast_hom h1)

end add_monoid_hom

@[simp] lemma int.cast_add_hom_int : int.cast_add_hom ℤ = add_monoid_hom.id ℤ :=
((add_monoid_hom.id ℤ).eq_int_cast_hom rfl).symm

namespace monoid_hom
variables {M : Type*} [monoid M]
open multiplicative

@[ext] theorem ext_mint {f g : multiplicative ℤ →* M} (h1 : f (of_add 1) = g (of_add 1)) : f = g :=
monoid_hom.ext $ add_monoid_hom.ext_iff.mp $
  @add_monoid_hom.ext_int _ _ f.to_additive g.to_additive h1

/-- If two `monoid_hom`s agree on `-1` and the naturals then they are equal. -/
@[ext] theorem ext_int {f g : ℤ →* M}
  (h_neg_one : f (-1) = g (-1))
  (h_nat : f.comp int.of_nat_hom.to_monoid_hom = g.comp int.of_nat_hom.to_monoid_hom) :
  f = g :=
begin
  ext (x | x),
  { exact (monoid_hom.congr_fun h_nat x : _), },
  { rw [int.neg_succ_of_nat_eq, ← neg_one_mul, f.map_mul, g.map_mul],
    congr' 1,
    exact_mod_cast (monoid_hom.congr_fun h_nat (x + 1) : _), }
end

end monoid_hom

namespace monoid_with_zero_hom

variables {M : Type*} [monoid_with_zero M]

/-- If two `monoid_with_zero_hom`s agree on `-1` and the naturals then they are equal. -/
@[ext] lemma ext_int {f g : ℤ →*₀ M} (h_neg_one : f (-1) = g (-1))
  (h_nat : f.comp int.of_nat_hom.to_monoid_with_zero_hom =
           g.comp int.of_nat_hom.to_monoid_with_zero_hom) :
  f = g :=
to_monoid_hom_injective $ monoid_hom.ext_int h_neg_one $ monoid_hom.ext (congr_fun h_nat : _)

/-- If two `monoid_with_zero_hom`s agree on `-1` and the _positive_ naturals then they are equal. -/
lemma ext_int' {φ₁ φ₂ : ℤ →*₀ M} (h_neg_one : φ₁ (-1) = φ₂ (-1))
  (h_pos : ∀ n : ℕ, 0 < n → φ₁ n = φ₂ n) : φ₁ = φ₂ :=
ext_int h_neg_one $ ext_nat h_pos

end monoid_with_zero_hom

namespace ring_hom

variables {α : Type*} {β : Type*} [ring α] [ring β]

@[simp] lemma eq_int_cast (f : ℤ →+* α) (n : ℤ) : f n  = n :=
f.to_add_monoid_hom.eq_int_cast f.map_one n

lemma eq_int_cast' (f : ℤ →+* α) : f = int.cast_ring_hom α :=
ring_hom.ext f.eq_int_cast

@[simp] lemma map_int_cast (f : α →+* β) (n : ℤ) : f n = n :=
(f.comp (int.cast_ring_hom α)).eq_int_cast n

lemma ext_int {R : Type*} [semiring R] (f g : ℤ →+* R) : f = g :=
coe_add_monoid_hom_injective $ add_monoid_hom.ext_int $ f.map_one.trans g.map_one.symm

instance int.subsingleton_ring_hom {R : Type*} [semiring R] : subsingleton (ℤ →+* R) :=
⟨ring_hom.ext_int⟩

end ring_hom

@[simp, norm_cast] theorem int.cast_id (n : ℤ) : ↑n = n :=
((ring_hom.id ℤ).eq_int_cast n).symm

@[simp] lemma int.cast_ring_hom_int : int.cast_ring_hom ℤ = ring_hom.id ℤ :=
(ring_hom.id ℤ).eq_int_cast'.symm

namespace pi

variables {α β : Type*}

lemma int_apply [has_zero β] [has_one β] [has_add β] [has_neg β] :
  ∀ (n : ℤ) (a : α), (n : α → β) a = n
| (n:ℕ)  a := pi.nat_apply n a
| -[1+n] a :=
by rw [cast_neg_succ_of_nat, cast_neg_succ_of_nat, neg_apply, add_apply, one_apply, nat_apply]

@[simp] lemma coe_int [has_zero β] [has_one β] [has_add β] [has_neg β] (n : ℤ) :
  (n : α → β) = λ _, n :=
by { ext, rw pi.int_apply }

end pi

namespace mul_opposite

variables {α : Type*} [has_zero α] [has_one α] [has_add α] [has_neg α]

@[simp, norm_cast] lemma op_int_cast : ∀ z : ℤ, op (z : α) = z
| (n:ℕ) := op_nat_cast n
| -[1+n] := congr_arg (λ a : αᵐᵒᵖ, -(a + 1)) $ op_nat_cast n

@[simp, norm_cast] lemma unop_int_cast : ∀ n : ℤ, unop (n : αᵐᵒᵖ) = n
| (n:ℕ) := unop_nat_cast n
| -[1+n] := congr_arg (λ a : α, -(a + 1)) $ unop_nat_cast n

end mul_opposite
