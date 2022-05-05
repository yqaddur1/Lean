/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Amelia Livingston, Yury Kudryashov,
Neil Strickland, Aaron Anderson
-/

import algebra.group_with_zero.basic

/-!
# Divisibility

This file defines the basics of the divisibility relation in the context of `(comm_)` `monoid`s
`(_with_zero)`.

## Main definitions

 * `monoid.has_dvd`

## Implementation notes

The divisibility relation is defined for all monoids, and as such, depends on the order of
  multiplication if the monoid is not commutative. There are two possible conventions for
  divisibility in the noncommutative context, and this relation follows the convention for ordinals,
  so `a | b` is defined as `∃ c, b = a * c`.

## Tags

divisibility, divides
-/

variables {α : Type*}

section semigroup

variables [semigroup α] {a b c : α}

/-- There are two possible conventions for divisibility, which coincide in a `comm_monoid`.
    This matches the convention for ordinals. -/
@[priority 100]
instance semigroup_has_dvd : has_dvd α :=
has_dvd.mk (λ a b, ∃ c, b = a * c)

-- TODO: this used to not have `c` explicit, but that seems to be important
--       for use with tactics, similar to `exists.intro`
theorem dvd.intro (c : α) (h : a * c = b) : a ∣ b :=
exists.intro c h^.symm

alias dvd.intro ← dvd_of_mul_right_eq

theorem exists_eq_mul_right_of_dvd (h : a ∣ b) : ∃ c, b = a * c := h

theorem dvd.elim {P : Prop} {a b : α} (H₁ : a ∣ b) (H₂ : ∀ c, b = a * c → P) : P :=
exists.elim H₁ H₂

local attribute [simp] mul_assoc mul_comm mul_left_comm

@[trans] theorem dvd_trans : a ∣ b → b ∣ c → a ∣ c
| ⟨d, h₁⟩ ⟨e, h₂⟩ := ⟨d * e, h₁ ▸ h₂.trans $ mul_assoc a d e⟩

alias dvd_trans ← has_dvd.dvd.trans

@[simp] theorem dvd_mul_right (a b : α) : a ∣ a * b := dvd.intro b rfl

theorem dvd_mul_of_dvd_left (h : a ∣ b) (c : α) : a ∣ b * c :=
h.trans (dvd_mul_right b c)

alias dvd_mul_of_dvd_left ← has_dvd.dvd.mul_right

theorem dvd_of_mul_right_dvd (h : a * b ∣ c) : a ∣ c :=
(dvd_mul_right a b).trans h

section map_dvd

variables {M N : Type*} [monoid M] [monoid N]

lemma map_dvd {F : Type*} [mul_hom_class F M N] (f : F) {a b} : a ∣ b → f a ∣ f b
| ⟨c, h⟩ := ⟨f c, h.symm ▸ map_mul f a c⟩

lemma mul_hom.map_dvd (f : M →ₙ* N) {a b} : a ∣ b → f a ∣ f b := map_dvd f

lemma monoid_hom.map_dvd (f : M →* N) {a b} : a ∣ b → f a ∣ f b := map_dvd f

end map_dvd

end semigroup

section monoid

variables [monoid α]

@[refl, simp] theorem dvd_refl (a : α) : a ∣ a :=
dvd.intro 1 (mul_one _)

lemma dvd_rfl {a : α} : a ∣ a :=
dvd_refl a

theorem one_dvd (a : α) : 1 ∣ a := dvd.intro a (one_mul _)

end monoid

section comm_semigroup

variables [comm_semigroup α] {a b c : α}

theorem dvd.intro_left (c : α) (h : c * a = b) : a ∣ b :=
dvd.intro _ (begin rewrite mul_comm at h, apply h end)

alias dvd.intro_left ← dvd_of_mul_left_eq

theorem exists_eq_mul_left_of_dvd (h : a ∣ b) : ∃ c, b = c * a :=
dvd.elim h (assume c, assume H1 : b = a * c, exists.intro c (eq.trans H1 (mul_comm a c)))

lemma dvd_iff_exists_eq_mul_left : a ∣ b ↔ ∃ c, b = c * a :=
⟨exists_eq_mul_left_of_dvd, by { rintro ⟨c, rfl⟩, exact ⟨c, mul_comm _ _⟩, }⟩

theorem dvd.elim_left {P : Prop} (h₁ : a ∣ b) (h₂ : ∀ c, b = c * a → P) : P :=
exists.elim (exists_eq_mul_left_of_dvd h₁) (assume c, assume h₃ : b = c * a, h₂ c h₃)

@[simp] theorem dvd_mul_left (a b : α) : a ∣ b * a := dvd.intro b (mul_comm a b)

theorem dvd_mul_of_dvd_right (h : a ∣ b) (c : α) : a ∣ c * b :=
begin rw mul_comm, exact h.mul_right _ end

alias dvd_mul_of_dvd_right ← has_dvd.dvd.mul_left

local attribute [simp] mul_assoc mul_comm mul_left_comm

theorem mul_dvd_mul : ∀ {a b c d : α}, a ∣ b → c ∣ d → a * c ∣ b * d
| a ._ c ._ ⟨e, rfl⟩ ⟨f, rfl⟩ := ⟨e * f, by simp⟩

theorem dvd_of_mul_left_dvd (h : a * b ∣ c) : b ∣ c :=
dvd.elim h (λ d ceq, dvd.intro (a * d) (by simp [ceq]))

end comm_semigroup

section comm_monoid

variables [comm_monoid α] {a b : α}

theorem mul_dvd_mul_left (a : α) {b c : α} (h : b ∣ c) : a * b ∣ a * c :=
mul_dvd_mul (dvd_refl a) h

theorem mul_dvd_mul_right (h : a ∣ b) (c : α) : a * c ∣ b * c :=
mul_dvd_mul h (dvd_refl c)

end comm_monoid

section semigroup_with_zero

variables [semigroup_with_zero α] {a : α}

theorem eq_zero_of_zero_dvd (h : 0 ∣ a) : a = 0 :=
dvd.elim h (assume c, assume H' : a = 0 * c, eq.trans H' (zero_mul c))

/-- Given an element `a` of a commutative semigroup with zero, there exists another element whose
    product with zero equals `a` iff `a` equals zero. -/
@[simp] lemma zero_dvd_iff : 0 ∣ a ↔ a = 0 :=
⟨eq_zero_of_zero_dvd, λ h, by { rw h, use 0, simp, }⟩

@[simp] theorem dvd_zero (a : α) : a ∣ 0 := dvd.intro 0 (by simp)

end semigroup_with_zero

/-- Given two elements `b`, `c` of a `cancel_monoid_with_zero` and a nonzero element `a`,
 `a*b` divides `a*c` iff `b` divides `c`. -/
theorem mul_dvd_mul_iff_left [cancel_monoid_with_zero α] {a b c : α}
  (ha : a ≠ 0) : a * b ∣ a * c ↔ b ∣ c :=
exists_congr $ λ d, by rw [mul_assoc, mul_right_inj' ha]

/-- Given two elements `a`, `b` of a commutative `cancel_monoid_with_zero` and a nonzero
  element `c`, `a*c` divides `b*c` iff `a` divides `b`. -/
theorem mul_dvd_mul_iff_right [cancel_comm_monoid_with_zero α] {a b c : α} (hc : c ≠ 0) :
  a * c ∣ b * c ↔ a ∣ b :=
exists_congr $ λ d, by rw [mul_right_comm, mul_left_inj' hc]

/-!
### Units in various monoids
-/

namespace units

section monoid
variables [monoid α] {a b : α} {u : αˣ}

/-- Elements of the unit group of a monoid represented as elements of the monoid
    divide any element of the monoid. -/
lemma coe_dvd : ↑u ∣ a := ⟨↑u⁻¹ * a, by simp⟩

/-- In a monoid, an element `a` divides an element `b` iff `a` divides all
    associates of `b`. -/
lemma dvd_mul_right : a ∣ b * u ↔ a ∣ b :=
iff.intro
  (assume ⟨c, eq⟩, ⟨c * ↑u⁻¹, by rw [← mul_assoc, ← eq, units.mul_inv_cancel_right]⟩)
  (assume ⟨c, eq⟩, eq.symm ▸ (dvd_mul_right _ _).mul_right _)

/-- In a monoid, an element `a` divides an element `b` iff all associates of `a` divide `b`. -/
lemma mul_right_dvd : a * u ∣ b ↔ a ∣ b :=
iff.intro
  (λ ⟨c, eq⟩, ⟨↑u * c, eq.trans (mul_assoc _ _ _)⟩)
  (λ h, dvd_trans (dvd.intro ↑u⁻¹ (by rw [mul_assoc, u.mul_inv, mul_one])) h)

end monoid

section comm_monoid
variables [comm_monoid α] {a b : α} {u : αˣ}

/-- In a commutative monoid, an element `a` divides an element `b` iff `a` divides all left
    associates of `b`. -/
lemma dvd_mul_left : a ∣ u * b ↔ a ∣ b := by { rw mul_comm, apply dvd_mul_right }

/-- In a commutative monoid, an element `a` divides an element `b` iff all
  left associates of `a` divide `b`.-/
lemma mul_left_dvd : ↑u * a ∣ b ↔ a ∣ b :=
by { rw mul_comm, apply mul_right_dvd }

end comm_monoid

end units

namespace is_unit

section monoid

variables [monoid α] {a b u : α} (hu : is_unit u)
include hu

/-- Units of a monoid divide any element of the monoid. -/
@[simp] lemma dvd : u ∣ a := by { rcases hu with ⟨u, rfl⟩, apply units.coe_dvd, }

@[simp] lemma dvd_mul_right : a ∣ b * u ↔ a ∣ b :=
by { rcases hu with ⟨u, rfl⟩, apply units.dvd_mul_right, }

/-- In a monoid, an element a divides an element b iff all associates of `a` divide `b`.-/
@[simp] lemma mul_right_dvd : a * u ∣ b ↔ a ∣ b :=
by { rcases hu with ⟨u, rfl⟩, apply units.mul_right_dvd, }

end monoid

section comm_monoid
variables [comm_monoid α] (a b u : α) (hu : is_unit u)
include hu

/-- In a commutative monoid, an element `a` divides an element `b` iff `a` divides all left
    associates of `b`. -/
@[simp] lemma dvd_mul_left : a ∣ u * b ↔ a ∣ b :=
by { rcases hu with ⟨u, rfl⟩, apply units.dvd_mul_left, }

/-- In a commutative monoid, an element `a` divides an element `b` iff all
  left associates of `a` divide `b`.-/
@[simp] lemma mul_left_dvd : u * a ∣ b ↔ a ∣ b :=
by { rcases hu with ⟨u, rfl⟩, apply units.mul_left_dvd, }

end comm_monoid

end is_unit

section comm_monoid
variables [comm_monoid α]

theorem is_unit_iff_dvd_one {x : α} : is_unit x ↔ x ∣ 1 :=
⟨by rintro ⟨u, rfl⟩; exact ⟨_, u.mul_inv.symm⟩,
 λ ⟨y, h⟩, ⟨⟨x, y, h.symm, by rw [h, mul_comm]⟩, rfl⟩⟩

theorem is_unit_iff_forall_dvd {x : α} :
  is_unit x ↔ ∀ y, x ∣ y :=
is_unit_iff_dvd_one.trans ⟨λ h y, h.trans (one_dvd _), λ h, h _⟩

theorem is_unit_of_dvd_unit {x y : α}
  (xy : x ∣ y) (hu : is_unit y) : is_unit x :=
is_unit_iff_dvd_one.2 $ xy.trans $ is_unit_iff_dvd_one.1 hu

lemma is_unit_of_dvd_one : ∀a ∣ 1, is_unit (a:α)
| a ⟨b, eq⟩ := ⟨units.mk_of_mul_eq_one a b eq.symm, rfl⟩

lemma not_is_unit_of_not_is_unit_dvd {a b : α} (ha : ¬is_unit a) (hb : a ∣ b) :
  ¬ is_unit b :=
mt (is_unit_of_dvd_unit hb) ha

end comm_monoid

section comm_monoid_with_zero

variable [comm_monoid_with_zero α]

/-- `dvd_not_unit a b` expresses that `a` divides `b` "strictly", i.e. that `b` divided by `a`
is not a unit. -/
def dvd_not_unit (a b : α) : Prop := a ≠ 0 ∧ ∃ x, ¬is_unit x ∧ b = a * x

lemma dvd_not_unit_of_dvd_of_not_dvd {a b : α} (hd : a ∣ b) (hnd : ¬ b ∣ a) :
  dvd_not_unit a b :=
begin
  split,
  { rintro rfl, exact hnd (dvd_zero _) },
  { rcases hd with ⟨c, rfl⟩,
    refine ⟨c, _, rfl⟩,
    rintro ⟨u, rfl⟩,
    simpa using hnd }
end

end comm_monoid_with_zero

lemma dvd_and_not_dvd_iff [cancel_comm_monoid_with_zero α] {x y : α} :
  x ∣ y ∧ ¬y ∣ x ↔ dvd_not_unit x y :=
⟨λ ⟨⟨d, hd⟩, hyx⟩, ⟨λ hx0, by simpa [hx0] using hyx, ⟨d,
    mt is_unit_iff_dvd_one.1 (λ ⟨e, he⟩, hyx ⟨e, by rw [hd, mul_assoc, ← he, mul_one]⟩), hd⟩⟩,
  λ ⟨hx0, d, hdu, hdx⟩, ⟨⟨d, hdx⟩, λ ⟨e, he⟩, hdu (is_unit_of_dvd_one _
    ⟨e, mul_left_cancel₀ hx0 $ by conv {to_lhs, rw [he, hdx]};simp [mul_assoc]⟩)⟩⟩

section monoid_with_zero

variable [monoid_with_zero α]

theorem ne_zero_of_dvd_ne_zero {p q : α} (h₁ : q ≠ 0)
  (h₂ : p ∣ q) : p ≠ 0 :=
begin
  rcases h₂ with ⟨u, rfl⟩,
  exact left_ne_zero_of_mul h₁,
end

end monoid_with_zero
