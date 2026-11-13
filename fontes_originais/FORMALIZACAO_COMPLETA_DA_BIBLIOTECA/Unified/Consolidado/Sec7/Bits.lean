module
public import Unified.Consolidado.Sec7.Heights
@[expose] public section

/-!
# Bit-level codes used in Section 7

Fixed-width binary blocks, the Elias gamma code `γ(n) = 0^{⌊log₂ n⌋} bin(n)`, the zig-zag map
`ζ`, and the codes `C_ℤ`, `C_rat`, `C_dyad` of eqs. (56)–(58), together with their exact
(self-delimiting) decoders.  A decoder is a map `List Bool → Option (α × List Bool)` returning the
decoded value and the unread suffix; "self-delimiting" means `dec (enc x ++ r) = some (x, r)` for
every suffix `r`.
-/

namespace Dyadic.Lib

/-- The maximal height `H = max_{a ∈ Λ} ht(a)` of a finite family of atoms. -/
def maxHeight (Λ : Finset Atom) : ℕ := Λ.sup Atom.height

/-! ### Fixed-width binary blocks -/

/-- `toBits b n`: the `b` lowest bits of `n`, most significant first (length exactly `b`). -/
def toBits : ℕ → ℕ → List Bool
  | 0, _ => []
  | b + 1, n => decide (n / 2 ^ b % 2 = 1) :: toBits b n

/-- Value of a big-endian bit string. -/
def ofBits : List Bool → ℕ
  | [] => 0
  | x :: l => (if x then 2 ^ l.length else 0) + ofBits l

@[simp] lemma length_toBits (b n : ℕ) : (toBits b n).length = b := by
  induction b with
  | zero => rfl
  | succ b ih => simp [toBits, ih]

lemma ofBits_toBits (b n : ℕ) : ofBits (toBits b n) = n % 2 ^ b := by
  induction b with
  | zero => simp [toBits, ofBits, Nat.mod_one]
  | succ b ih =>
    simp only [toBits, ofBits, length_toBits, ih]
    rw [Nat.mod_pow_succ (b := 2)]
    have h := Nat.mod_two_eq_zero_or_one (n / 2 ^ b)
    rcases h with h | h <;> simp [h] <;> ring

lemma ofBits_toBits_of_lt {b n : ℕ} (h : n < 2 ^ b) : ofBits (toBits b n) = n := by
  rw [ofBits_toBits, Nat.mod_eq_of_lt h]

/-- Decoder for blocks of fixed width `b`. -/
def fixedDec (b : ℕ) (l : List Bool) : Option (ℕ × List Bool) :=
  if (l.take b).length = b then some (ofBits (l.take b), l.drop b) else none

lemma fixedDec_toBits {b n : ℕ} (h : n < 2 ^ b) (r : List Bool) :
    fixedDec b (toBits b n ++ r) = some (n, r) := by
  unfold fixedDec
  have h1 : (toBits b n ++ r).take b = toBits b n := by
    rw [List.take_append_of_le_length (by simp)]; simp
  have h2 : (toBits b n ++ r).drop b = r := by
    rw [List.drop_append_of_le_length (by simp)]; simp
  rw [h1, h2, if_pos (by simp), ofBits_toBits_of_lt h]

/-! ### Elias gamma code -/

/-- The Elias gamma code `γ(n) = 0^{⌊log₂ n⌋} bin(n)` (for `n ≥ 1`). -/
def eliasGamma (n : ℕ) : List Bool :=
  List.replicate (Nat.log 2 n) false ++ toBits (Nat.log 2 n + 1) n

/-- `|γ(n)| = 2⌊log₂ n⌋ + 1`. -/
@[simp] lemma length_eliasGamma (n : ℕ) : (eliasGamma n).length = 2 * Nat.log 2 n + 1 := by
  simp [eliasGamma]; ring

lemma toBits_log_head {n : ℕ} (hn : 1 ≤ n) :
    toBits (Nat.log 2 n + 1) n = true :: toBits (Nat.log 2 n) n := by
  simp only [toBits, List.cons.injEq, and_true, decide_eq_true_eq]
  have h1 := Nat.pow_log_le_self 2 (show n ≠ 0 by omega)
  have h2 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
  have h3 : n / 2 ^ Nat.log 2 n = 1 := by
    apply le_antisymm
    · rw [Nat.div_le_iff_le_mul_add_pred (by positivity)]
      rw [pow_succ] at h2; omega
    · exact (Nat.le_div_iff_mul_le (by positivity)).2 (by simpa using h1)
  rw [h3]

/-- Decoder of the Elias gamma code: count the leading zeros `z`, then read `z+1` bits. -/
def gammaDec (l : List Bool) : Option (ℕ × List Bool) :=
  let z := (l.takeWhile (fun b => !b)).length
  fixedDec (z + 1) (l.drop z)

lemma takeWhile_not_replicate (z : ℕ) (t : List Bool) :
    ((List.replicate z false ++ true :: t).takeWhile (fun b => !b)) = List.replicate z false := by
  induction z with
  | zero => simp
  | succ z ih => simp [List.replicate_succ, ih]

lemma gammaDec_eliasGamma {n : ℕ} (hn : 1 ≤ n) (r : List Bool) :
    gammaDec (eliasGamma n ++ r) = some (n, r) := by
  unfold gammaDec eliasGamma
  have e : List.replicate (Nat.log 2 n) false ++ toBits (Nat.log 2 n + 1) n ++ r =
      List.replicate (Nat.log 2 n) false ++ true :: (toBits (Nat.log 2 n) n ++ r) := by
    rw [toBits_log_head hn]; simp
  simp only
  rw [e, takeWhile_not_replicate, List.length_replicate, List.drop_left' (by simp),
    show true :: (toBits (Nat.log 2 n) n ++ r) = toBits (Nat.log 2 n + 1) n ++ r by
      rw [toBits_log_head hn]; simp]
  exact fixedDec_toBits (Nat.lt_pow_succ_log_self (by norm_num) n) r

/-! ### Integers, rationals and dyadics (eqs. (56)–(58)) -/

/-- The zig-zag bijection `ζ : ℤ → ℕ`, `ζ(z) = 2z` for `z ≥ 0`, `-2z-1` for `z < 0`. -/
def zeta (z : ℤ) : ℕ := if 0 ≤ z then 2 * z.toNat else 2 * (-z).toNat - 1

/-- Inverse of `ζ`. -/
def zetaInv (n : ℕ) : ℤ := if n % 2 = 0 then (n / 2 : ℕ) else -(((n + 1) / 2 : ℕ) : ℤ)

@[simp] lemma zetaInv_zeta (z : ℤ) : zetaInv (zeta z) = z := by
  unfold zeta zetaInv; split_ifs <;> omega

lemma zeta_le (z : ℤ) : zeta z ≤ 2 * z.natAbs := by unfold zeta; split_ifs <;> omega

/-- eq. (56): `C_ℤ(z) = γ(ζ(z) + 1)`. -/
def codeZ (z : ℤ) : List Bool := eliasGamma (zeta z + 1)

/-- Decoder of `C_ℤ`. -/
def decZ (l : List Bool) : Option (ℤ × List Bool) :=
  (gammaDec l).map (fun p => (zetaInv (p.1 - 1), p.2))

lemma decZ_codeZ (z : ℤ) (r : List Bool) : decZ (codeZ z ++ r) = some (z, r) := by
  simp [decZ, codeZ, gammaDec_eliasGamma (show 1 ≤ zeta z + 1 by omega)]

/-- eq. (57): `C_rat(p/q) = C_ℤ(p) γ(q)` for the reduced form `p/q`, `q > 0`. -/
def codeRat (r : ℚ) : List Bool := codeZ r.num ++ eliasGamma r.den

/-- Decoder of `C_rat`. -/
def decRat (l : List Bool) : Option (ℚ × List Bool) :=
  (decZ l).bind fun p => (gammaDec p.2).map fun q => ((p.1 : ℚ) / (q.1 : ℚ), q.2)

lemma decRat_codeRat (x : ℚ) (r : List Bool) : decRat (codeRat x ++ r) = some (x, r) := by
  simp only [decRat, codeRat, List.append_assoc, decZ_codeZ, Option.bind_some,
    gammaDec_eliasGamma x.den_pos, Option.map_some]
  rw [Rat.num_div_den]

/-- The exponent `k` of the canonical dyadic form `t = u 2^{-k}` (`k = log₂ den`). -/
def dyadExp (t : ℚ) : ℕ := Nat.log 2 t.den

/-- eq. (58): `C_dyad(u, k) = C_ℤ(u) γ(k+1)` for `t = u 2^{-k}` in canonical form (`u` odd when
`k > 0`, i.e. `u = num t`, `2^k = den t`). -/
def codeDyad (t : ℚ) : List Bool := codeZ t.num ++ eliasGamma (dyadExp t + 1)

/-- Decoder of `C_dyad`. -/
def decDyad (l : List Bool) : Option (ℚ × List Bool) :=
  (decZ l).bind fun p => (gammaDec p.2).map fun q => ((p.1 : ℚ) / 2 ^ (q.1 - 1), q.2)

/-- A rational is dyadic if its reduced denominator is a power of two. -/
def IsDyadic (t : ℚ) : Prop := ∃ k : ℕ, t.den = 2 ^ k

lemma decDyad_codeDyad {t : ℚ} (ht : IsDyadic t) (r : List Bool) :
    decDyad (codeDyad t ++ r) = some (t, r) := by
  obtain ⟨k, hk⟩ := ht
  simp only [decDyad, codeDyad, List.append_assoc, decZ_codeZ, Option.bind_some,
    gammaDec_eliasGamma (show 1 ≤ dyadExp t + 1 by omega), Option.map_some, Nat.add_sub_cancel]
  have : dyadExp t = k := by unfold dyadExp; rw [hk, Nat.log_pow (by norm_num)]
  rw [this]
  have e : ((2 : ℚ) ^ k) = ((t.den : ℕ) : ℚ) := by rw [hk]; push_cast; ring
  rw [e, Rat.num_div_den]

/-! ### Generic sequential decoding -/

/-- Decode `n` consecutive items with the decoder `d`. -/
def decMany {α : Type*} (d : List Bool → Option (α × List Bool)) :
    ℕ → List Bool → Option (List α × List Bool)
  | 0, l => some ([], l)
  | n + 1, l => (d l).bind fun p => (decMany d n p.2).map fun q => (p.1 :: q.1, q.2)

lemma decMany_flatten {α : Type*} (d : List Bool → Option (α × List Bool)) (e : α → List Bool)
    (xs : List α) (hd : ∀ x ∈ xs, ∀ r, d (e x ++ r) = some (x, r)) (r : List Bool) :
    decMany d xs.length ((xs.map e).flatten ++ r) = some (xs, r) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, List.map_cons, List.flatten_cons, List.append_assoc, decMany]
    rw [hd x (by simp), Option.bind_some, ih (fun y hy => hd y (by simp [hy]))]
    rfl

/-- If a decoder exactly inverts an encoder on every suffix, the codewords form a prefix-free
family: no codeword of one item is a proper prefix of the codeword of another. -/
lemma prefixFree_of_dec {α : Type*} (d : List Bool → Option (α × List Bool)) (e : α → List Bool)
    (S : Set α) (hd : ∀ x ∈ S, ∀ r, d (e x ++ r) = some (x, r)) :
    ∀ x ∈ S, ∀ y ∈ S, e x <+: e y → x = y ∧ e x = e y := by
  intro x hx y hy ⟨r, hr⟩
  have h1 := hd x hx r
  rw [hr, ← List.append_nil (e y), hd y hy []] at h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  exact ⟨rfl, by simpa using hr⟩

/-! ### Length estimates -/

lemma natLog_le_logb (n : ℕ) : (Nat.log 2 n : ℝ) ≤ Real.logb 2 n := by
  have := Real.natLog_le_logb n 2
  simpa using this

/-- `|γ(n)| ≤ 2 log₂ n + 1`. -/
lemma length_eliasGamma_le (n : ℕ) : ((eliasGamma n).length : ℝ) ≤ 2 * Real.logb 2 n + 1 := by
  rw [length_eliasGamma]; push_cast; linarith [natLog_le_logb n]

lemma length_eliasGamma_mono {m n : ℕ} (h : m ≤ n) :
    (eliasGamma m).length ≤ (eliasGamma n).length := by
  simp only [length_eliasGamma]; have := Nat.log_mono_right (b := 2) h; omega

/-- `|C_ℤ(z)| ≤ 2 log₂(2A+1) + 1` whenever `|z| ≤ A`. -/
lemma length_codeZ_le {z : ℤ} {A : ℕ} (h : z.natAbs ≤ A) :
    (codeZ z).length ≤ (eliasGamma (2 * A + 1)).length :=
  length_eliasGamma_mono (by have := zeta_le z; omega)

/-- `L_rat(r) ≤ 2 |γ(2A+1)|` whenever `ht(r) ≤ A`. -/
lemma length_codeRat_le {x : ℚ} {A : ℕ} (h : ratHeight x ≤ A) :
    (codeRat x).length ≤ 2 * (eliasGamma (2 * A + 1)).length := by
  unfold codeRat
  rw [List.length_append]
  have h1 := length_codeZ_le ((natAbs_num_le_ratHeight x).trans h)
  have h2 := length_eliasGamma_mono (show x.den ≤ 2 * A + 1 by
    have := den_le_ratHeight x; omega)
  omega

/-- `L_dyad(t) ≤ |γ(2A+1)| + |γ(B+1)|` whenever `|num t| ≤ A` and `log₂ den t ≤ B`. -/
lemma length_codeDyad_le {t : ℚ} {A B : ℕ} (hA : t.num.natAbs ≤ A) (hB : dyadExp t ≤ B) :
    (codeDyad t).length ≤ (eliasGamma (2 * A + 1)).length + (eliasGamma (B + 1)).length := by
  unfold codeDyad
  rw [List.length_append]
  have h1 := length_codeZ_le hA
  have h2 := length_eliasGamma_mono (show dyadExp t + 1 ≤ B + 1 by omega)
  omega

lemma clog_le_logb_add_one {x : ℕ} (hx : 1 ≤ x) : (Nat.clog 2 x : ℝ) ≤ Real.logb 2 x + 1 := by
  rcases Nat.eq_or_lt_of_le hx with h | h
  · subst h; simp
  · have h1 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h
    have hpos : 0 < Nat.clog 2 x := Nat.clog_pos (by norm_num) h
    have h2 : ((2 : ℝ) ^ (Nat.clog 2 x - 1 : ℕ)) < x := by exact_mod_cast h1
    have h3 : ((Nat.clog 2 x - 1 : ℕ) : ℝ) < Real.logb 2 x := by
      rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by positivity)]
      rw [Real.rpow_natCast]; exact h2
    push_cast [Nat.cast_sub hpos] at h3
    linarith

lemma logb_le_clog {x : ℕ} : Real.logb 2 x ≤ Nat.clog 2 x := by
  rcases Nat.eq_zero_or_pos x with h | h
  · subst h; simp
  have h1 : (x : ℝ) ≤ 2 ^ Nat.clog 2 x := by exact_mod_cast Nat.le_pow_clog (b := 2) (by norm_num) x
  rw [Real.logb_le_iff_le_rpow (by norm_num) (by exact_mod_cast h), Real.rpow_natCast]
  exact h1

lemma one_le_logb_of_two_le {H : ℕ} (hH : 2 ≤ H) : 1 ≤ Real.logb 2 H := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
  simp; exact_mod_cast hH

lemma logb_nonneg_nat (n : ℕ) : 0 ≤ Real.logb 2 n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast h)

end Dyadic.Lib
