import RequestProject.Addresses

/-!
# Section 3.3 — Prefix-free codes

Binary words are `List Bool`.  We define fixed-width binary, the Elias gamma code
`γ(n) = 0^{⌊log₂ n⌋} bin(n)`, the integer code `C_ℤ(z) = γ(ζ(z)+1)`, the rational code
`C_rat(p/q) = C_ℤ(p) γ(q)` and the dyadic code `C_dyad(u,k) = C_ℤ(u) γ(k+1)`, together with
exact decoders (self-delimiting round trips).
-/

namespace Artigo

/-! ## Fixed-width binary -/

/-- the `w`-bit binary expansion of `n`, most significant bit first -/
def toBits : ℕ → ℕ → List Bool
  | 0, _ => []
  | w + 1, n => decide (2 ^ w ≤ n % 2 ^ (w + 1)) :: toBits w (n % 2 ^ w)

/-- value of a binary word (most significant bit first) -/
def ofBits : List Bool → ℕ
  | [] => 0
  | b :: L => (if b then 2 ^ L.length else 0) + ofBits L

@[simp] lemma toBits_length (w n : ℕ) : (toBits w n).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [toBits, ih]

lemma ofBits_toBits (w n : ℕ) (h : n < 2 ^ w) : ofBits (toBits w n) = n := by
  induction w generalizing n with
  | zero => simp at h; subst h; rfl
  | succ w ih =>
    simp only [toBits, ofBits, toBits_length]
    rw [ih _ (Nat.mod_lt _ (by positivity)), Nat.mod_eq_of_lt h]
    split_ifs with hb
    · simp only [decide_eq_true_eq] at hb
      have : n % 2 ^ w = n - 2 ^ w := by
        rw [Nat.mod_eq_sub_mod hb, Nat.mod_eq_of_lt (by rw [pow_succ] at h; omega)]
      omega
    · simp only [decide_eq_true_eq, not_le] at hb
      rw [Nat.mod_eq_of_lt hb]; simp

lemma ofBits_lt (L : List Bool) : ofBits L < 2 ^ L.length := by
  induction L with
  | nil => simp [ofBits]
  | cons b L ih => simp only [ofBits, List.length_cons, pow_succ]; split_ifs <;> omega

/-! ## Elias gamma -/

/-- the Elias gamma code `γ(n) = 0^{⌊log₂ n⌋} bin(n)` (for `n ≥ 1`). -/
def gamma (n : ℕ) : List Bool := List.replicate (Nat.log 2 n) false ++ toBits (Nat.log 2 n + 1) n

/-- `|γ(n)| = 2⌊log₂ n⌋ + 1` -/
@[simp] lemma gamma_length (n : ℕ) : (gamma n).length = 2 * Nat.log 2 n + 1 := by
  simp [gamma]; ring

lemma toBits_log_head {n : ℕ} (hn : 1 ≤ n) :
    ∃ L, toBits (Nat.log 2 n + 1) n = true :: L := by
  refine ⟨toBits (Nat.log 2 n) (n % 2 ^ Nat.log 2 n), ?_⟩
  simp only [toBits, List.cons.injEq, and_true, decide_eq_true_eq]
  rw [Nat.mod_eq_of_lt (Nat.lt_pow_succ_log_self (by norm_num) n)]
  exact Nat.pow_log_le_self 2 (by omega)

/-- number of leading zeros -/
def countZeros : List Bool → ℕ
  | false :: s => countZeros s + 1
  | _ => 0

/-- decoder for `γ`: count leading zeros `z`, then read `z+1` bits. -/
def decGamma (s : List Bool) : Option (ℕ × List Bool) :=
  let z := countZeros s
  let rest := s.drop z
  if rest.length < z + 1 then none else some (ofBits (rest.take (z + 1)), rest.drop (z + 1))

lemma countZeros_replicate_true (L : ℕ) (u : List Bool) :
    countZeros (List.replicate L false ++ true :: u) = L := by
  induction L with
  | zero => simp [countZeros]
  | succ L ih => simp [List.replicate_succ, countZeros, ih]

lemma decGamma_gamma {n : ℕ} (hn : 1 ≤ n) (t : List Bool) : decGamma (gamma n ++ t) = some (n, t) := by
  obtain ⟨L, hL⟩ := toBits_log_head hn
  have hlen := toBits_length (Nat.log 2 n + 1) n
  rw [hL] at hlen
  simp only [List.length_cons] at hlen
  unfold decGamma gamma
  simp only [List.append_assoc]
  rw [hL, List.cons_append, countZeros_replicate_true, List.drop_left' (by simp)]
  have h1 : ¬ ((true :: (L ++ t)).length < Nat.log 2 n + 1) := by simp; omega
  rw [if_neg h1]
  have h2 : (true :: (L ++ t)).take (Nat.log 2 n + 1) = true :: L := by
    rw [← List.cons_append, List.take_left' (by simp; omega)]
  have h3 : (true :: (L ++ t)).drop (Nat.log 2 n + 1) = t := by
    rw [← List.cons_append, List.drop_left' (by simp; omega)]
  rw [h2, h3, ← hL, ofBits_toBits _ _ (Nat.lt_pow_succ_log_self (by norm_num) n)]

/-! ## Generic codecs -/

/-- a binary code with a decoder that returns the unread remainder -/
structure Codec (α : Type*) where
  enc : α → List Bool
  dec : List Bool → Option (α × List Bool)

/-- the round-trip (self-delimiting exact decoding) property on the inputs satisfying `P` -/
def Codec.RT {α : Type*} (c : Codec α) (P : α → Prop) : Prop :=
  ∀ x, P x → ∀ t, c.dec (c.enc x ++ t) = some (x, t)

/-- A self-delimiting code is prefix-free. -/
lemma Codec.RT.prefix_free {α : Type*} {c : Codec α} {P : α → Prop} (h : c.RT P) {x y : α}
    (hx : P x) (hy : P y) (hxy : c.enc x <+: c.enc y) : x = y := by
  obtain ⟨t, ht⟩ := hxy
  have h1 := h x hx t
  have h2 := h y hy []
  rw [List.append_nil] at h2
  rw [ht, h2] at h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  exact h1.1.symm

lemma Codec.RT.injective {α : Type*} {c : Codec α} {P : α → Prop} (h : c.RT P) {x y : α}
    (hx : P x) (hy : P y) (hxy : c.enc x = c.enc y) : x = y :=
  h.prefix_free hx hy ⟨[], by simp [hxy]⟩

/-- unique parsing: concatenations of self-delimiting codes split uniquely -/
lemma Codec.RT.unique_parse {α : Type*} {c : Codec α} {P : α → Prop} (h : c.RT P) {x y : α}
    (hx : P x) (hy : P y) {s t : List Bool} (hxy : c.enc x ++ s = c.enc y ++ t) : x = y ∧ s = t := by
  have h1 := h x hx s
  have h2 := h y hy t
  rw [hxy, h2] at h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  exact ⟨h1.1.symm, h1.2.symm⟩

/-- product of codecs -/
def Codec.prod {α β : Type*} (c₁ : Codec α) (c₂ : Codec β) : Codec (α × β) where
  enc p := c₁.enc p.1 ++ c₂.enc p.2
  dec s := match c₁.dec s with
    | none => none
    | some (a, s₁) => match c₂.dec s₁ with
      | none => none
      | some (b, s₂) => some ((a, b), s₂)

lemma Codec.RT.prod {α β : Type*} {c₁ : Codec α} {c₂ : Codec β} {P₁ : α → Prop} {P₂ : β → Prop}
    (h₁ : c₁.RT P₁) (h₂ : c₂.RT P₂) : (c₁.prod c₂).RT (fun p => P₁ p.1 ∧ P₂ p.2) := by
  rintro ⟨a, b⟩ ⟨ha, hb⟩ t
  simp only [Codec.prod, List.append_assoc]
  rw [h₁ a ha]
  simp only
  rw [h₂ b hb]

/-- transport a codec along maps `f : α → β`, `g : β → Option α` -/
def Codec.map {α β : Type*} (c : Codec α) (f : β → α) (g : α → Option β) : Codec β where
  enc b := c.enc (f b)
  dec s := match c.dec s with
    | none => none
    | some (a, s₁) => match g a with
      | none => none
      | some b => some (b, s₁)

lemma Codec.RT.map {α β : Type*} {c : Codec α} {P : α → Prop} (h : c.RT P) (f : β → α)
    (g : α → Option β) {Q : β → Prop} (hQ : ∀ b, Q b → P (f b) ∧ g (f b) = some b) :
    (c.map f g).RT Q := by
  intro b hb t
  simp only [Codec.map]
  rw [h (f b) (hQ b hb).1]
  simp only
  rw [(hQ b hb).2]

/-- decode exactly `n` items -/
def Codec.decN {α : Type*} (c : Codec α) : ℕ → List Bool → Option (List α × List Bool)
  | 0, s => some ([], s)
  | n + 1, s => match c.dec s with
    | none => none
    | some (a, s₁) => match c.decN n s₁ with
      | none => none
      | some (L, s₂) => some (a :: L, s₂)

/-- concatenation of the codes of a list -/
def Codec.encList {α : Type*} (c : Codec α) (L : List α) : List Bool := (L.map c.enc).flatten

lemma Codec.RT.decN {α : Type*} {c : Codec α} {P : α → Prop} (h : c.RT P) :
    ∀ (L : List α), (∀ x ∈ L, P x) → ∀ t, c.decN L.length (c.encList L ++ t) = some (L, t) := by
  intro L
  induction L with
  | nil => intros; rfl
  | cons a L ih =>
    intro hL t
    simp only [Codec.encList, List.map_cons, List.flatten_cons, List.length_cons, Codec.decN,
      List.append_assoc]
    rw [h a (hL a (by simp))]
    simp only
    have := ih (fun x hx => hL x (by simp [hx])) t
    simp only [Codec.encList] at this
    rw [this]

/-- the gamma codec -/
def gammaCodec : Codec ℕ := ⟨gamma, decGamma⟩

lemma gammaCodec_RT : gammaCodec.RT (fun n => 1 ≤ n) := fun _ hn t => decGamma_gamma hn t

/-- a list codec with a gamma-coded length header: `γ(N)` followed by the items -/
def Codec.withLen {α : Type*} (c : Codec α) : Codec (List α) where
  enc L := gamma L.length ++ c.encList L
  dec s := match decGamma s with
    | none => none
    | some (n, s₁) => c.decN n s₁

lemma Codec.RT.withLen {α : Type*} {c : Codec α} {P : α → Prop} (h : c.RT P) :
    c.withLen.RT (fun L => L ≠ [] ∧ ∀ x ∈ L, P x) := by
  intro L ⟨hne, hL⟩ t
  simp only [Codec.withLen, List.append_assoc]
  have hlen : 1 ≤ L.length := List.length_pos_iff.mpr hne
  rw [decGamma_gamma hlen]
  exact h.decN L hL t

lemma Codec.encList_length {α : Type*} (c : Codec α) (L : List α) :
    (c.encList L).length = (L.map (fun x => (c.enc x).length)).sum := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [Codec.encList] at ih ⊢; rw [ih]

/-! ## Integer, rational and dyadic codes -/

/-- `C_ℤ(z) = γ(ζ(z)+1)` where `ζ(z) = 2z` (`z ≥ 0`), `-2z-1` (`z < 0`) is `Z⁻¹`. -/
def intCodec : Codec ℤ := gammaCodec.map (fun z => Zinv z + 1) (fun n => some (Zenum (n - 1)))

lemma intCodec_RT : intCodec.RT (fun _ => True) :=
  gammaCodec_RT.map _ _ (fun z _ => ⟨by simp, by simp [Zenum_Zinv]⟩)

/-- `ζ = Z⁻¹` -/
lemma zeta_eq (z : ℤ) : (Zinv z : ℤ) = if 0 ≤ z then 2 * z else -2 * z - 1 := by
  unfold Zinv; split_ifs <;> omega

/-- `C_rat(p/q) = C_ℤ(p) γ(q)` -/
def ratCodec : Codec ℚ :=
  (intCodec.prod gammaCodec).map (fun r => (r.num, r.den))
    (fun p => some ((p.1 : ℚ) / p.2))

lemma ratCodec_RT : ratCodec.RT (fun _ => True) :=
  (intCodec_RT.prod gammaCodec_RT).map _ _ (fun r _ => ⟨⟨trivial, r.den_pos⟩, by simp [Rat.num_div_den]⟩)

/-- a rational is dyadic when its reduced denominator is a power of two -/
def IsDyadic (t : ℚ) : Prop := ∃ k : ℕ, t.den = 2 ^ k

/-- `C_dyad(u,k) = C_ℤ(u) γ(k+1)` for `t = u 2^{-k}` in canonical form -/
def dyadCodec : Codec ℚ :=
  (intCodec.prod gammaCodec).map (fun t => (t.num, Nat.log 2 t.den + 1))
    (fun p => some ((p.1 : ℚ) / 2 ^ (p.2 - 1)))

lemma dyadCodec_RT : dyadCodec.RT IsDyadic := by
  apply (intCodec_RT.prod gammaCodec_RT).map
  rintro t ⟨k, hk⟩
  refine ⟨⟨trivial, by simp⟩, ?_⟩
  simp only [Option.some.injEq, Nat.add_sub_cancel]
  rw [hk, Nat.log_pow (by norm_num)]
  conv_rhs => rw [← Rat.num_div_den t, hk]
  push_cast; rfl

lemma intCodec_length (z : ℤ) : (intCodec.enc z).length = 2 * Nat.log 2 (Zinv z + 1) + 1 := by
  simp [intCodec, Codec.map, gammaCodec]

lemma ratCodec_length (r : ℚ) :
    (ratCodec.enc r).length = 2 * Nat.log 2 (Zinv r.num + 1) + 1 + (2 * Nat.log 2 r.den + 1) := by
  simp [ratCodec, Codec.map, Codec.prod, intCodec, gammaCodec]

lemma dyadCodec_length (t : ℚ) :
    (dyadCodec.enc t).length = 2 * Nat.log 2 (Zinv t.num + 1) + 1 + (2 * Nat.log 2 (Nat.log 2 t.den + 1) + 1) := by
  simp [dyadCodec, Codec.map, Codec.prod, intCodec, gammaCodec]

/-! ### Length bounds -/

lemma log_le_log_of_le {a b : ℕ} (h : a ≤ b) : Nat.log 2 a ≤ Nat.log 2 b := Nat.log_mono_right h

/-- if `|z| ≤ A` (with `A ≥ 1`) then `|C_ℤ(z)| ≤ 2 log₂ A + 5` -/
lemma intCodec_length_le {z : ℤ} {A : ℕ} (hA : 1 ≤ A) (hz : z.natAbs ≤ A) :
    (intCodec.enc z).length ≤ 2 * Nat.log 2 A + 5 := by
  rw [intCodec_length]
  have h1 : Zinv z + 1 ≤ 2 ^ 2 * A := by have := Zinv_le_nat z; omega
  have h2 : Nat.log 2 (Zinv z + 1) ≤ Nat.log 2 A + 2 := by
    calc Nat.log 2 (Zinv z + 1) ≤ Nat.log 2 (2 ^ 2 * A) := log_le_log_of_le h1
      _ = Nat.log 2 A + 2 := by
        rw [show 2 ^ 2 * A = A * 2 * 2 by ring, Nat.log_mul_base (by norm_num) (by omega),
          Nat.log_mul_base (by norm_num) (by omega)]
  omega

/-- if `ht r ≤ A` (with `A ≥ 1`) then `L_rat(r) ≤ 4 log₂ A + 7` -/
lemma ratCodec_length_le {r : ℚ} {A : ℕ} (hA : 1 ≤ A) (hr : ht r ≤ A) :
    (ratCodec.enc r).length ≤ 4 * Nat.log 2 A + 7 := by
  have h1 : r.num.natAbs ≤ A := le_trans (le_max_left _ _) hr
  have h2 : r.den ≤ A := le_trans (le_max_right _ _) hr
  have := intCodec_length_le hA h1
  rw [intCodec_length] at this
  rw [ratCodec_length]
  have := log_le_log_of_le h2
  omega

/-- dyadic code length bound: `|u| ≤ A`, `k ≤ B` -/
lemma dyadCodec_length_le {t : ℚ} {A B : ℕ} (hA : 1 ≤ A) (hu : t.num.natAbs ≤ A) {k : ℕ}
    (hk : t.den = 2 ^ k) (hkB : k + 1 ≤ B) :
    (dyadCodec.enc t).length ≤ 2 * Nat.log 2 A + 2 * Nat.log 2 B + 6 := by
  have := intCodec_length_le hA hu
  rw [intCodec_length] at this
  rw [dyadCodec_length, hk, Nat.log_pow (by norm_num)]
  have := log_le_log_of_le hkB
  omega

lemma ratCodec_length_ge_log_den (r : ℚ) : 2 * Nat.log 2 r.den ≤ (ratCodec.enc r).length := by
  rw [ratCodec_length]; omega

end Artigo
