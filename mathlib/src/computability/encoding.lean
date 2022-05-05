/-
Copyright (c) 2020 Pim Spelier, Daan van Gent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Spelier, Daan van Gent
-/

import data.fintype.basic
import data.num.lemmas
import set_theory.cardinal.ordinal
import tactic.derive_fintype

/-!
# Encodings

This file contains the definition of a (finite) encoding, a map from a type to
strings in an alphabet, used in defining computability by Turing machines.
It also contains several examples:

## Examples

- `fin_encoding_nat_bool`   : a binary encoding of ℕ in a simple alphabet.
- `fin_encoding_nat_Γ'`    : a binary encoding of ℕ in the alphabet used for TM's.
- `unary_fin_encoding_nat` : a unary encoding of ℕ
- `fin_encoding_bool_bool`  : an encoding of bool.
-/

universes u v
open_locale cardinal

namespace computability

/-- An encoding of a type in a certain alphabet, together with a decoding. -/
structure encoding (α : Type u) :=
(Γ : Type v)
(encode : α → list Γ)
(decode : list Γ → option α)
(decode_encode : ∀ x, decode (encode x) = some x)

lemma encoding.encode_injective {α : Type u} (e : encoding α) :
  function.injective e.encode :=
begin
  refine λ _ _ h, option.some_injective _ _,
  rw [← e.decode_encode, ← e.decode_encode, h],
end

/-- An encoding plus a guarantee of finiteness of the alphabet. -/
structure fin_encoding (α : Type u) extends encoding.{u 0} α :=
(Γ_fin : fintype Γ)

instance {α : Type u} (e : fin_encoding α) :
  fintype e.to_encoding.Γ :=
e.Γ_fin

/-- A standard Turing machine alphabet, consisting of blank,bit0,bit1,bra,ket,comma. -/
@[derive [decidable_eq,fintype]]
inductive Γ'
| blank | bit (b : bool) | bra | ket | comma

instance inhabited_Γ' : inhabited Γ' := ⟨Γ'.blank⟩

/-- The natural inclusion of bool in Γ'. -/
def inclusion_bool_Γ' : bool → Γ' := Γ'.bit

/-- An arbitrary section of the natural inclusion of bool in Γ'. -/
def section_Γ'_bool : Γ' → bool
| (Γ'.bit b) := b
| _ := arbitrary bool

lemma left_inverse_section_inclusion : function.left_inverse section_Γ'_bool inclusion_bool_Γ' :=
λ x, bool.cases_on x rfl rfl

lemma inclusion_bool_Γ'_injective : function.injective inclusion_bool_Γ' :=
function.has_left_inverse.injective (Exists.intro section_Γ'_bool left_inverse_section_inclusion)

/-- An encoding function of the positive binary numbers in bool. -/
def encode_pos_num : pos_num → list bool
| pos_num.one := [tt]
| (pos_num.bit0 n) := ff :: encode_pos_num n
| (pos_num.bit1 n) := tt :: encode_pos_num n

/-- An encoding function of the binary numbers in bool. -/
def encode_num : num → list bool
| num.zero := []
| (num.pos n) := encode_pos_num n

/-- An encoding function of ℕ in bool. -/
def encode_nat (n : ℕ) : list bool := encode_num n

/-- A decoding function from `list bool` to the positive binary numbers. -/
def decode_pos_num : list bool → pos_num
| (ff :: l) := (pos_num.bit0 (decode_pos_num l))
| (tt :: l) := ite (l = []) pos_num.one (pos_num.bit1 (decode_pos_num l))
| _ := pos_num.one

/-- A decoding function from `list bool` to the binary numbers. -/
def decode_num : list bool → num := λ l, ite (l = []) num.zero $ decode_pos_num l

/-- A decoding function from `list bool` to ℕ. -/
def decode_nat : list bool → nat := λ l, decode_num l

lemma encode_pos_num_nonempty (n : pos_num) : (encode_pos_num n) ≠ [] :=
pos_num.cases_on n (list.cons_ne_nil _ _) (λ m, list.cons_ne_nil _ _) (λ m, list.cons_ne_nil _ _)

lemma decode_encode_pos_num : ∀ n, decode_pos_num(encode_pos_num n) = n :=
begin
  intros n,
  induction n with m hm m hm; unfold encode_pos_num decode_pos_num,
  { refl },
  { rw hm,
    exact if_neg (encode_pos_num_nonempty m) },
  { exact congr_arg pos_num.bit0 hm }
end

lemma decode_encode_num : ∀ n, decode_num(encode_num n) = n :=
begin
  intros n,
  cases n; unfold encode_num decode_num,
  { refl },
  rw decode_encode_pos_num n,
  rw pos_num.cast_to_num,
  exact if_neg (encode_pos_num_nonempty n),
end

lemma decode_encode_nat : ∀ n, decode_nat(encode_nat n) = n :=
begin
  intro n,
  conv_rhs {rw ← num.to_of_nat n},
  exact congr_arg coe (decode_encode_num ↑n),
end

/-- A binary encoding of ℕ in bool. -/
def encoding_nat_bool : encoding ℕ :=
{ Γ := bool,
  encode := encode_nat,
  decode := λ n, some (decode_nat n),
  decode_encode := λ n, congr_arg _ (decode_encode_nat n) }

/-- A binary fin_encoding of ℕ in bool. -/
def fin_encoding_nat_bool : fin_encoding ℕ := ⟨encoding_nat_bool, bool.fintype⟩

/-- A binary encoding of ℕ in Γ'. -/
def encoding_nat_Γ' : encoding ℕ :=
{ Γ := Γ',
  encode := λ x, list.map inclusion_bool_Γ' (encode_nat x),
  decode := λ x, some (decode_nat (list.map section_Γ'_bool x)),
  decode_encode := λ x, congr_arg _ $
    by rw [list.map_map, list.map_id' left_inverse_section_inclusion, decode_encode_nat] }

/-- A binary fin_encoding of ℕ in Γ'. -/
def fin_encoding_nat_Γ' : fin_encoding ℕ := ⟨encoding_nat_Γ', Γ'.fintype⟩

/-- A unary encoding function of ℕ in bool. -/
def unary_encode_nat : nat → list bool
| 0 := []
| (n+1) := tt :: (unary_encode_nat n)

/-- A unary decoding function from `list bool` to ℕ. -/
def unary_decode_nat : list bool → nat := list.length

lemma unary_decode_encode_nat : ∀ n, unary_decode_nat (unary_encode_nat n) = n :=
λ n, nat.rec rfl (λ (m : ℕ) hm, (congr_arg nat.succ hm.symm).symm) n

/-- A unary fin_encoding of ℕ. -/
def unary_fin_encoding_nat : fin_encoding ℕ :=
{ Γ := bool,
  encode := unary_encode_nat,
  decode := λ n, some (unary_decode_nat n),
  decode_encode := λ n, congr_arg _ (unary_decode_encode_nat n),
  Γ_fin := bool.fintype}

/-- An encoding function of bool in bool. -/
def encode_bool : bool → list bool := list.ret

/-- A decoding function from `list bool` to bool. -/
def decode_bool : list bool → bool
| (b :: _) := b
| _ := arbitrary bool

lemma decode_encode_bool : ∀ b, decode_bool(encode_bool b) = b := λ b, bool.cases_on b rfl rfl

/-- A fin_encoding of bool in bool. -/
def fin_encoding_bool_bool : fin_encoding bool :=
{ Γ := bool,
  encode := encode_bool,
  decode := λ x, some (decode_bool x),
  decode_encode := λ x, congr_arg _ (decode_encode_bool x),
  Γ_fin := bool.fintype }

instance inhabited_fin_encoding : inhabited (fin_encoding bool) := ⟨fin_encoding_bool_bool⟩

instance inhabited_encoding : inhabited (encoding bool) := ⟨fin_encoding_bool_bool.to_encoding⟩

lemma encoding.card_le_card_list {α : Type u} (e : encoding.{u v} α) :
  cardinal.lift.{v} (# α) ≤ cardinal.lift.{u} (# (list e.Γ)) :=
(cardinal.lift_mk_le').2 ⟨⟨e.encode, e.encode_injective⟩⟩

lemma encoding.card_le_omega {α : Type u} (e : encoding.{u v} α) [encodable e.Γ] :
  (# α) ≤ ω :=
begin
  refine cardinal.lift_le.1 (e.card_le_card_list.trans _),
  simp only [cardinal.lift_omega, cardinal.lift_le_omega],
  casesI is_empty_or_nonempty e.Γ with h h,
  { simp only [cardinal.mk_le_omega], },
  { rw cardinal.mk_list_eq_omega },
end

lemma fin_encoding.card_le_omega {α : Type u} (e : fin_encoding α) :
  (# α) ≤ ω :=
begin
  haveI : encodable e.Γ := fintype.to_encodable _,
  exact e.to_encoding.card_le_omega,
end

end computability
