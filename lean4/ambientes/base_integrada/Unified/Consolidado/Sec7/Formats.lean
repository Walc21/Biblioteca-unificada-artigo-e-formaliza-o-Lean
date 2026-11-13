module
public import Unified.Consolidado.Sec7.Bits
public import Unified.Consolidado.Sec7.Chain
@[expose] public section

/-!
# Theorem 7.12: rigorous comparison of the three prefix-free formats

An assembly with `N` leaves is given by its leaves `a 0, …, a (N-1)` in spatial order.  The three
streams are
* `C_atom`: `γ(N)` and, for each leaf, `γ(k+1) C_ℤ(m) C_rat(y₀) C_rat(s)`;
* `C_ReLU,str`: `γ(N)`, `C_dyad(x₀) C_rat(y₀) C_rat(s₀)` for the first leaf, and the pairs
  `C_dyad(t_j) C_rat(s_j - s_{j-1})`;
* `C_ReLU,rat`: `γ(N)`, `C_rat(c) C_rat(s₀)` with `c = g(t₀) - s₀ t₀` (read as `ℓ₀(t₀) - s₀ t₀`,
  the intercept of the first leaf), and the pairs `C_rat(t_j) C_rat(s_j - s_{j-1})`.
-/

open Finset

namespace Dyadic.Lib

/-! ### Blocks -/

/-- One leaf of the atomic stream: `γ(k+1) C_ℤ(m) C_rat(y₀) C_rat(s)`. -/
def codeAtom (a : Atom) : List Bool :=
  eliasGamma (a.k + 1) ++ codeZ a.m ++ codeRat a.y0 ++ codeRat a.s

/-- Decoder of one atomic block. -/
def decAtom (l : List Bool) : Option (Atom × List Bool) :=
  (gammaDec l).bind fun p1 => (decZ p1.2).bind fun p2 => (decRat p2.2).bind fun p3 =>
    (decRat p3.2).bind fun p4 =>
      if h : p4.1 = 0 then none else some (⟨p1.1 - 1, p2.1, p3.1, p4.1, h⟩, p4.2)

lemma decAtom_codeAtom (a : Atom) (r : List Bool) : decAtom (codeAtom a ++ r) = some (a, r) := by
  simp only [decAtom, codeAtom, List.append_assoc, gammaDec_eliasGamma (Nat.le_add_left 1 a.k),
    Option.bind_some, decZ_codeZ, decRat_codeRat, dif_neg a.hs, Nat.add_sub_cancel]

/-- A pair `C_dyad(t) C_rat(δ)` of the structural ReLU stream. -/
def codePairDyad (p : ℚ × ℚ) : List Bool := codeDyad p.1 ++ codeRat p.2
/-- A pair `C_rat(t) C_rat(δ)` of the expanded ReLU stream. -/
def codePairRat (p : ℚ × ℚ) : List Bool := codeRat p.1 ++ codeRat p.2

def decPairDyad (l : List Bool) : Option ((ℚ × ℚ) × List Bool) :=
  (decDyad l).bind fun p => (decRat p.2).map fun q => ((p.1, q.1), q.2)
def decPairRat (l : List Bool) : Option ((ℚ × ℚ) × List Bool) :=
  (decRat l).bind fun p => (decRat p.2).map fun q => ((p.1, q.1), q.2)

lemma decPairDyad_code {p : ℚ × ℚ} (hp : IsDyadic p.1) (r : List Bool) :
    decPairDyad (codePairDyad p ++ r) = some (p, r) := by
  simp [decPairDyad, codePairDyad, decDyad_codeDyad hp, decRat_codeRat]

lemma decPairRat_code (p : ℚ × ℚ) (r : List Bool) :
    decPairRat (codePairRat p ++ r) = some (p, r) := by
  simp [decPairRat, codePairRat, decRat_codeRat]

/-! ### The three streams -/

/-- The ReLU parameters `(t_j, s_j - s_{j-1})`, `1 ≤ j ≤ N-1` (nodes and slope jumps, eq. (24)). -/
def jumps (a : ℕ → Atom) (N : ℕ) : List (ℚ × ℚ) :=
  (List.range' 1 (N - 1)).map fun j => ((a j).left, (a j).s - (a (j - 1)).s)

/-- `C_atom(g)`. -/
def streamAtom (a : ℕ → Atom) (N : ℕ) : List Bool :=
  eliasGamma N ++ (((List.range N).map a).map codeAtom).flatten

/-- `C_ReLU,str(g)`. -/
def streamStr (a : ℕ → Atom) (N : ℕ) : List Bool :=
  eliasGamma N ++ codeDyad (a 0).center ++ codeRat (a 0).y0 ++ codeRat (a 0).s ++
    ((jumps a N).map codePairDyad).flatten

/-- `C_ReLU,rat(g)`. -/
def streamRat (a : ℕ → Atom) (N : ℕ) : List Bool :=
  eliasGamma N ++ codeRat (a 0).intercept ++ codeRat (a 0).s ++
    ((jumps a N).map codePairRat).flatten

/-- Decoder of `C_atom`: returns the leaves. -/
def decStreamAtom (l : List Bool) : Option (List Atom × List Bool) :=
  (gammaDec l).bind fun p => decMany decAtom p.1 p.2

/-- Decoder of `C_ReLU,str`: returns `(x₀, y₀, s₀, [(t_j, s_j - s_{j-1})])`. -/
def decStreamStr (l : List Bool) : Option ((ℚ × ℚ × ℚ × List (ℚ × ℚ)) × List Bool) :=
  (gammaDec l).bind fun p => (decDyad p.2).bind fun q1 => (decRat q1.2).bind fun q2 =>
    (decRat q2.2).bind fun q3 => (decMany decPairDyad (p.1 - 1) q3.2).map fun q4 =>
      ((q1.1, q2.1, q3.1, q4.1), q4.2)

/-- Decoder of `C_ReLU,rat`: returns `(c, s₀, [(t_j, s_j - s_{j-1})])`. -/
def decStreamRat (l : List Bool) : Option ((ℚ × ℚ × List (ℚ × ℚ)) × List Bool) :=
  (gammaDec l).bind fun p => (decRat p.2).bind fun q1 => (decRat q1.2).bind fun q2 =>
    (decMany decPairRat (p.1 - 1) q2.2).map fun q3 => ((q1.1, q2.1, q3.1), q3.2)

/-- Evaluation of the ReLU parameters `(c, s₀, [(t_j, δ_j)])`:
`c + s₀ x + ∑_j δ_j ρ(x - t_j)`. -/
noncomputable def reluEval (c s0 : ℚ) (ps : List (ℚ × ℚ)) (x : ℝ) : ℝ :=
  c + s0 * x + (ps.map fun p => (p.2 : ℝ) * relu (x - p.1)).sum

lemma length_jumps (a : ℕ → Atom) (N : ℕ) : (jumps a N).length = N - 1 := by simp [jumps]

lemma Atom.left_isDyadic (a : Atom) : IsDyadic a.left := by
  obtain ⟨-, j, -, h⟩ := dyadic_reduced a.m a.k; exact ⟨j, h⟩

lemma Atom.center_eq' (a : Atom) : a.center = ((2 * a.m + 1 : ℤ) : ℚ) / 2 ^ (a.k + 1) := by
  simp [Atom.center]

lemma Atom.center_isDyadic (a : Atom) : IsDyadic a.center := by
  obtain ⟨-, j, -, h⟩ := dyadic_reduced (2 * a.m + 1) (a.k + 1); exact ⟨j, by rw [a.center_eq']; exact h⟩

lemma decStreamAtom_exact (a : ℕ → Atom) {N : ℕ} (hN : 1 ≤ N) (r : List Bool) :
    decStreamAtom (streamAtom a N ++ r) = some ((List.range N).map a, r) := by
  unfold decStreamAtom streamAtom
  rw [List.append_assoc, gammaDec_eliasGamma hN, Option.bind_some]
  have := decMany_flatten decAtom codeAtom ((List.range N).map a)
    (fun x _ r => decAtom_codeAtom x r) r
  simpa using this

lemma decStreamStr_exact (a : ℕ → Atom) {N : ℕ} (hN : 1 ≤ N) (r : List Bool) :
    decStreamStr (streamStr a N ++ r) =
      some (((a 0).center, (a 0).y0, (a 0).s, jumps a N), r) := by
  unfold decStreamStr streamStr
  simp only [List.append_assoc]
  rw [gammaDec_eliasGamma hN, Option.bind_some, decDyad_codeDyad (a 0).center_isDyadic,
    Option.bind_some, decRat_codeRat, Option.bind_some, decRat_codeRat, Option.bind_some]
  simp only
  rw [← length_jumps a N, decMany_flatten _ _ _ (fun p hp r => decPairDyad_code (by
    simp only [jumps, List.mem_map] at hp
    obtain ⟨j, -, rfl⟩ := hp
    exact (a j).left_isDyadic) r)]
  rfl

lemma decStreamRat_exact (a : ℕ → Atom) {N : ℕ} (hN : 1 ≤ N) (r : List Bool) :
    decStreamRat (streamRat a N ++ r) = some (((a 0).intercept, (a 0).s, jumps a N), r) := by
  unfold decStreamRat streamRat
  simp only [List.append_assoc]
  rw [gammaDec_eliasGamma hN, Option.bind_some, decRat_codeRat, Option.bind_some, decRat_codeRat,
    Option.bind_some]
  simp only
  rw [← length_jumps a N, decMany_flatten _ _ _ (fun p _ r => decPairRat_code p r)]
  rfl

/-- Exact self-delimiting decoding implies prefix-freeness of the family of codewords. -/
lemma prefix_eq_of_dec {α β : Type*} (d : List Bool → Option (β × List Bool)) (e : α → List Bool)
    (v : α → β) (S : Set α) (hd : ∀ x ∈ S, ∀ r, d (e x ++ r) = some (v x, r)) :
    ∀ x ∈ S, ∀ y ∈ S, e x <+: e y → e x = e y := by
  intro x hx y hy ⟨t, ht⟩
  have h1 := hd x hx t
  rw [ht, ← List.append_nil (e y), hd y hy []] at h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  rw [← ht, ← h1.2, List.append_nil]

lemma sum_range'_eq_sum_Ico {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range' 1 n).map f).sum = ∑ j ∈ Finset.Ico 1 (n + 1), f j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range'_concat, List.map_append, List.sum_append, ih,
      Finset.sum_Ico_succ_top (a := 1) (b := n + 1) (by omega)]
    simp [Nat.add_comm 1 n]

/-- The expanded ReLU parameters reproduce the assembly on `K` (Theorem 4.3). -/
lemma reluEval_jumps {K : Set ℝ} {g : ℝ → ℝ} {a : ℕ → Atom} {N : ℕ} (hN : 1 ≤ N)
    (hcons : ∀ j, j + 1 < N → (a j).right = (a (j + 1)).left)
    (hmatch : ∀ j, j + 1 < N → (a j).line (a j).right = (a (j + 1)).line (a (j + 1)).left)
    (hg : ∀ j < N, ∀ x ∈ (a j).cell ∩ K, g x = (a j).line x)
    (hK : K ⊆ Set.Icc ((a 0).left : ℝ) ((a (N - 1)).right)) :
    ∀ x ∈ K, g x = reluEval (a 0).intercept (a 0).s (jumps a N) x := by
  intro x hx
  rw [assembly_eq_relu K g hN hcons hmatch hg hK x hx, affine_part_expand]
  unfold reluEval jumps
  rw [List.map_map, sum_range'_eq_sum_Ico, Nat.sub_add_cancel hN]
  rfl

/-! ### Length estimates -/

lemma length_flatten_le {α : Type*} (xs : List α) (e : α → List Bool) (B : ℕ)
    (h : ∀ x ∈ xs, (e x).length ≤ B) : ((xs.map e).flatten).length ≤ xs.length * B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
    have := h x (by simp)
    have := ih (fun y hy => h y (by simp [hy]))
    nlinarith

lemma length_eliasGamma_le_of_lt_pow {n e : ℕ} (h : n < 2 ^ (e + 1)) :
    (eliasGamma n).length ≤ 2 * e + 1 := by
  rw [length_eliasGamma]
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0; simp
  · have := Nat.log_lt_of_lt_pow (b := 2) (by omega) h; omega

/-- `|γ(n)| ≤ 4⌊log₂ H⌋ + 9` whenever `n ≤ 5H²`. -/
lemma gamma_le_poly {H n : ℕ} (hn : n ≤ 5 * H ^ 2) :
    (eliasGamma n).length ≤ 4 * Nat.log 2 H + 9 := by
  have h1 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) H
  set l := Nat.log 2 H
  have h2 : H ^ 2 < (2 ^ (l + 1)) ^ 2 := Nat.pow_lt_pow_left h1 (by norm_num)
  have h3 : n < 2 ^ (2 * l + 4 + 1) := by
    have : (2 : ℕ) ^ (2 * l + 4 + 1) = 8 * (2 ^ (l + 1)) ^ 2 := by ring
    omega
  have := length_eliasGamma_le_of_lt_pow h3
  omega

/-- `|γ(n)| ≤ 8H + 7` whenever `n < 2^{4H+4}`. -/
lemma gamma_le_exp {H n : ℕ} (hn : n < 2 ^ (4 * H + 4)) : (eliasGamma n).length ≤ 8 * H + 7 := by
  have := length_eliasGamma_le_of_lt_pow (e := 4 * H + 3) (by simpa using hn)
  omega

lemma ratHeight_le_dyadExp {t : ℚ} {j B : ℕ} (h : t.den = 2 ^ j) (hj : j ≤ B) : dyadExp t ≤ B := by
  unfold dyadExp; rw [h, Nat.log_pow (by norm_num)]; exact hj

lemma length_codeAtom_le {H : ℕ} {a : Atom} (ha : a.height ≤ H) :
    (codeAtom a).length ≤ 6 * (4 * Nat.log 2 H + 9) := by
  have h := (Atom.height_le_iff a).1 ha
  unfold codeAtom
  simp only [List.length_append]
  have g1 := gamma_le_poly (H := H) (n := 2 * H + 1) (by nlinarith)
  have e1 := gamma_le_poly (H := H) (n := a.k + 1) (by nlinarith)
  have e2 := length_codeZ_le (show a.m.natAbs ≤ H by omega)
  have e3 := length_codeRat_le h.2.2.2.1
  have e4 := length_codeRat_le h.2.2.2.2
  omega

lemma length_codeDyad_center_le {H : ℕ} {a : Atom} (ha : a.height ≤ H) :
    (codeDyad a.center).length ≤ 2 * (4 * Nat.log 2 H + 9) := by
  have h := (Atom.height_le_iff a).1 ha
  obtain ⟨hn, j, hj, hd⟩ := dyadic_reduced (2 * a.m + 1) (a.k + 1)
  rw [← a.center_eq'] at hn hd
  have e := length_codeDyad_le (A := 2 * H) (B := H) (by omega) (ratHeight_le_dyadExp hd (by omega))
  have g1 := gamma_le_poly (H := H) (n := 2 * (2 * H) + 1) (by nlinarith)
  have g2 := gamma_le_poly (H := H) (n := H + 1) (by nlinarith)
  omega

lemma length_codeDyad_left_le {H : ℕ} {a : Atom} (ha : a.height ≤ H) :
    (codeDyad a.left).length ≤ 2 * (4 * Nat.log 2 H + 9) := by
  have h := (Atom.height_le_iff a).1 ha
  obtain ⟨hn, j, hj, hd⟩ := dyadic_reduced a.m a.k
  have e := length_codeDyad_le (A := H) (B := H) (t := a.left) (by unfold Atom.left; omega)
    (ratHeight_le_dyadExp hd (by omega))
  have g1 := gamma_le_poly (H := H) (n := 2 * H + 1) (by nlinarith)
  have g2 := gamma_le_poly (H := H) (n := H + 1) (by nlinarith)
  omega

lemma length_codeRat_poly {H : ℕ} {x : ℚ} (hx : ratHeight x ≤ 2 * H ^ 2) (hH : 1 ≤ H) :
    (codeRat x).length ≤ 2 * (4 * Nat.log 2 H + 9) := by
  have e := length_codeRat_le hx
  have g := gamma_le_poly (H := H) (n := 2 * (2 * H ^ 2) + 1) (by nlinarith)
  omega

lemma length_codeRat_exp {H : ℕ} {x : ℚ} (hx : ratHeight x ≤ 2 ^ (H + 1) * H ^ 2) :
    (codeRat x).length ≤ 2 * (8 * H + 7) := by
  have e := length_codeRat_le hx
  have hH : H ^ 2 < 2 ^ (2 * H) := by
    have := Nat.lt_two_pow_self (n := H)
    calc H ^ 2 < (2 ^ H) ^ 2 := Nat.pow_lt_pow_left this (by norm_num)
      _ = 2 ^ (2 * H) := by ring
  have : 2 * (2 ^ (H + 1) * H ^ 2) + 1 < 2 ^ (4 * H + 4) := by
    have e1 : 2 ^ (4 * H + 4) = 2 ^ (H + 2) * 2 ^ (2 * H) * 2 ^ (H + 2) := by
      rw [← pow_add, ← pow_add]; ring_nf
    have e2 : 2 * (2 ^ (H + 1) * H ^ 2) = 2 ^ (H + 2) * H ^ 2 := by ring
    have e3 : 2 ^ (H + 2) * H ^ 2 + 1 ≤ 2 ^ (H + 2) * 2 ^ (2 * H) :=
      by have := Nat.mul_le_mul_left (2 ^ (H + 2)) hH; have : 1 ≤ 2 ^ (H + 2) := Nat.one_le_two_pow; nlinarith
    have e4 : 2 ^ (H + 2) * 2 ^ (2 * H) < 2 ^ (H + 2) * 2 ^ (2 * H) * 2 ^ (H + 2) := by
      have : 1 < 2 ^ (H + 2) := Nat.one_lt_two_pow (by omega)
      have : 0 < 2 ^ (H + 2) * 2 ^ (2 * H) := by positivity
      nlinarith
    omega
  have g := gamma_le_exp this
  omega

/-! ### Natural-number length bounds for the three streams -/

lemma streamAtom_length_le {H N : ℕ} (a : ℕ → Atom) (ha : ∀ j < N, (a j).height ≤ H) :
    (streamAtom a N).length ≤ (2 * Nat.log 2 N + 1) + N * (6 * (4 * Nat.log 2 H + 9)) := by
  unfold streamAtom
  rw [List.length_append, length_eliasGamma]
  have := length_flatten_le ((List.range N).map a) codeAtom (6 * (4 * Nat.log 2 H + 9))
    (fun x hx => by
      simp only [List.mem_map, List.mem_range] at hx
      obtain ⟨j, hj, rfl⟩ := hx
      exact length_codeAtom_le (ha j hj))
  simpa using this

lemma length_codePairDyad_le {H N : ℕ} (a : ℕ → Atom) (ha : ∀ j < N, (a j).height ≤ H)
    (hH : 1 ≤ H) : ∀ p ∈ jumps a N, (codePairDyad p).length ≤ 4 * (4 * Nat.log 2 H + 9) := by
  intro p hp
  simp only [jumps, List.mem_map, List.mem_range'] at hp
  obtain ⟨j, ⟨i, hi, hij⟩, rfl⟩ := hp
  have h1 := ha j (by omega)
  have h0 := ha (j - 1) (by omega)
  have e1 := length_codeDyad_left_le h1
  have e2 := length_codeRat_poly (height_calculus (a (j - 1)) (a j) h0 h1).2.1 hH
  simp only [codePairDyad, List.length_append]
  omega

lemma length_codePairRat_le {H N : ℕ} (a : ℕ → Atom) (ha : ∀ j < N, (a j).height ≤ H)
    (hH : 1 ≤ H) : ∀ p ∈ jumps a N, (codePairRat p).length ≤ 4 * (8 * H + 7) := by
  intro p hp
  simp only [jumps, List.mem_map, List.mem_range'] at hp
  obtain ⟨j, ⟨i, hi, hij⟩, rfl⟩ := hp
  have h1 := ha j (by omega)
  have h0 := ha (j - 1) (by omega)
  have hH1 : 1 ≤ H ^ 2 := Nat.one_le_pow _ _ (by omega)
  have e1 := length_codeRat_exp (H := H) (x := (a j).left) (by
    have := (a j).ratHeight_left_le h1
    calc ratHeight (a j).left ≤ 2 ^ H := this
      _ ≤ 2 ^ (H + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega))
  have e2 := length_codeRat_poly (height_calculus (a (j - 1)) (a j) h0 h1).2.1 hH
  have hl : Nat.log 2 H < H := Nat.log_lt_self 2 (by omega)
  simp only [codePairRat, List.length_append]
  omega

lemma streamStr_length_le {H N : ℕ} (a : ℕ → Atom) (hN : 1 ≤ N) (ha : ∀ j < N, (a j).height ≤ H)
    (hH : 1 ≤ H) :
    (streamStr a N).length ≤ (2 * Nat.log 2 N + 1) + 6 * (4 * Nat.log 2 H + 9) +
      (N - 1) * (4 * (4 * Nat.log 2 H + 9)) := by
  have h0 := ha 0 hN
  have h := (Atom.height_le_iff _).1 h0
  unfold streamStr
  simp only [List.length_append, length_eliasGamma]
  have e1 := length_codeDyad_center_le h0
  have e2 := length_codeRat_poly (H := H) (x := (a 0).y0) (by nlinarith) hH
  have e3 := length_codeRat_poly (H := H) (x := (a 0).s) (by nlinarith) hH
  have e4 := length_flatten_le (jumps a N) codePairDyad _ (length_codePairDyad_le a ha hH)
  rw [length_jumps] at e4
  omega

lemma streamRat_length_le {H N : ℕ} (a : ℕ → Atom) (hN : 1 ≤ N) (ha : ∀ j < N, (a j).height ≤ H)
    (hH : 1 ≤ H) :
    (streamRat a N).length ≤ (2 * Nat.log 2 N + 1) + 4 * (8 * H + 7) +
      (N - 1) * (4 * (8 * H + 7)) := by
  have h0 := ha 0 hN
  have h := (Atom.height_le_iff _).1 h0
  unfold streamRat
  simp only [List.length_append, length_eliasGamma]
  have hH1 : 1 ≤ H ^ 2 := Nat.one_le_pow _ _ (by omega)
  have e1 := length_codeRat_exp (height_calculus (a 0) (a 0) h0 h0).2.2.2
  have e2 := length_codeRat_exp (H := H) (x := (a 0).s) (by
    calc ratHeight (a 0).s ≤ H := h.2.2.2.2
      _ ≤ 2 ^ (H + 1) := (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_right (by norm_num)
            (by omega))
      _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega))
  have e4 := length_flatten_le (jumps a N) codePairRat _ (length_codePairRat_le a ha hH)
  rw [length_jumps] at e4
  omega

/-- Explicit length bounds behind eq. (63), with the universal constant `200`. -/
theorem formats_length_bounds (a : ℕ → Atom) {N H : ℕ} (hN : 1 ≤ N) (hH : 2 ≤ H)
    (ha : ∀ j < N, (a j).height ≤ H) :
    ((streamAtom a N).length : ℝ) ≤ 200 * N * Real.logb 2 H ∧
    ((streamStr a N).length : ℝ) ≤ 200 * N * Real.logb 2 H ∧
    ((streamRat a N).length : ℝ) ≤ 200 * N * H := by
  have hl := one_le_logb_of_two_le hH
  have hlH := natLog_le_logb H
  have hlN : (Nat.log 2 N : ℝ) ≤ N := by exact_mod_cast (Nat.log_lt_self 2 (by omega)).le
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hHr : (2 : ℝ) ≤ H := by exact_mod_cast hH
  have hN1 : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
  have hNL : (N : ℝ) ≤ N * Real.logb 2 H := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · have := streamAtom_length_le a ha
    have h' : ((streamAtom a N).length : ℝ) ≤ (2 * Nat.log 2 N + 1) +
        N * (6 * (4 * Nat.log 2 H + 9)) := by exact_mod_cast this
    have : (N : ℝ) * Nat.log 2 H ≤ N * Real.logb 2 H := mul_le_mul_of_nonneg_left hlH (by linarith)
    nlinarith
  · have := streamStr_length_le a hN ha (by omega)
    have h' : ((streamStr a N).length : ℝ) ≤ (2 * Nat.log 2 N + 1) +
        6 * (4 * Nat.log 2 H + 9) + ((N - 1 : ℕ) : ℝ) * (4 * (4 * Nat.log 2 H + 9)) := by
      exact_mod_cast this
    have e1 : ((N - 1 : ℕ) : ℝ) * (4 * (4 * Nat.log 2 H + 9)) ≤ N * (4 * (4 * Real.logb 2 H + 9)) :=
      mul_le_mul hN1 (by linarith) (by positivity) (by linarith)
    have : (N : ℝ) * Real.logb 2 H ≥ 1 := by nlinarith
    nlinarith
  · have := streamRat_length_le a hN ha (by omega)
    have h' : ((streamRat a N).length : ℝ) ≤ (2 * Nat.log 2 N + 1) +
        4 * (8 * H + 7) + ((N - 1 : ℕ) : ℝ) * (4 * (8 * H + 7)) := by exact_mod_cast this
    have e1 : ((N - 1 : ℕ) : ℝ) * (4 * (8 * H + 7)) ≤ N * (4 * (8 * H + 7)) :=
      mul_le_mul_of_nonneg_right hN1 (by positivity)
    have : (N : ℝ) * H ≥ 2 := by nlinarith
    nlinarith

/-! ### Theorem 7.12 -/

/-- **Theorem 7.12** (rigorous comparison of the formats), general part.  The three streams are
self-delimiting with exact decoders, hence prefix-free; the decoded data determine the assembly
(the leaves themselves, resp. the ReLU parameters of eq. (24), with `c = y₀ - s₀ x₀`); and, with
universal constants, for every assembly with `N ≥ 1` leaves of height at most `H ≥ 2`:
`L_atom = O(N log H)`, `L_ReLU,str = O(N log H)`, `L_ReLU,rat = O(N H)` (eq. (63)). -/
theorem formats_comparison :
    -- exact decoders (self-delimiting)
    (∀ (a : ℕ → Atom) (N : ℕ), 1 ≤ N → ∀ r : List Bool,
      decStreamAtom (streamAtom a N ++ r) = some ((List.range N).map a, r) ∧
      decStreamStr (streamStr a N ++ r) =
        some (((a 0).center, (a 0).y0, (a 0).s, jumps a N), r) ∧
      decStreamRat (streamRat a N ++ r) = some (((a 0).intercept, (a 0).s, jumps a N), r)) ∧
    -- prefix-freeness
    (∀ (a b : ℕ → Atom) (N M : ℕ), 1 ≤ N → 1 ≤ M →
      (streamAtom a N <+: streamAtom b M → streamAtom a N = streamAtom b M) ∧
      (streamStr a N <+: streamStr b M → streamStr a N = streamStr b M) ∧
      (streamRat a N <+: streamRat b M → streamRat a N = streamRat b M)) ∧
    -- the decoded parameters reproduce the assembly
    (∀ (K : Set ℝ) (g : ℝ → ℝ) (a : ℕ → Atom) (N : ℕ), 1 ≤ N →
      (∀ j, j + 1 < N → (a j).right = (a (j + 1)).left) →
      (∀ j, j + 1 < N → (a j).line (a j).right = (a (j + 1)).line (a (j + 1)).left) →
      (∀ j < N, ∀ x ∈ (a j).cell ∩ K, g x = (a j).line x) →
      K ⊆ Set.Icc ((a 0).left : ℝ) ((a (N - 1)).right) →
      (a 0).intercept = (a 0).y0 - (a 0).s * (a 0).center ∧
      ∀ x ∈ K, g x = reluEval (a 0).intercept (a 0).s (jumps a N) x) ∧
    -- length bounds (63)
    ∃ C : ℝ, ∀ (a : ℕ → Atom) (N H : ℕ), 1 ≤ N → 2 ≤ H → (∀ j < N, (a j).height ≤ H) →
      ((streamAtom a N).length : ℝ) ≤ C * N * Real.logb 2 H ∧
      ((streamStr a N).length : ℝ) ≤ C * N * Real.logb 2 H ∧
      ((streamRat a N).length : ℝ) ≤ C * N * H := by
  refine ⟨fun a N hN r => ⟨decStreamAtom_exact a hN r, decStreamStr_exact a hN r,
    decStreamRat_exact a hN r⟩, fun a b N M hN hM => ⟨?_, ?_, ?_⟩,
    fun K g a N hN hcons hmatch hg hK => ⟨rfl, reluEval_jumps hN hcons hmatch hg hK⟩,
    200, fun a N H hN hH ha => ?_⟩
  · exact prefix_eq_of_dec decStreamAtom (fun p : (ℕ → Atom) × ℕ => streamAtom p.1 p.2)
      (fun p => (List.range p.2).map p.1) {p | 1 ≤ p.2}
      (fun p hp r => decStreamAtom_exact p.1 hp r) (a, N) hN (b, M) hM
  · exact prefix_eq_of_dec decStreamStr (fun p : (ℕ → Atom) × ℕ => streamStr p.1 p.2)
      (fun p => ((p.1 0).center, (p.1 0).y0, (p.1 0).s, jumps p.1 p.2)) {p | 1 ≤ p.2}
      (fun p hp r => decStreamStr_exact p.1 hp r) (a, N) hN (b, M) hM
  · exact prefix_eq_of_dec decStreamRat (fun p : (ℕ → Atom) × ℕ => streamRat p.1 p.2)
      (fun p => ((p.1 0).intercept, (p.1 0).s, jumps p.1 p.2)) {p | 1 ≤ p.2}
      (fun p hp r => decStreamRat_exact p.1 hp r) (a, N) hN (b, M) hM
  · exact formats_length_bounds a hN hH ha

/-! ### The extremal family of Theorem 7.12 -/

/-- The leaf `J_{H-1,j}` with central value `0` and slope `(-1)^j`. -/
def famAtom (H j : ℕ) : Atom := ⟨H - 1, j, 0, (-1) ^ j, pow_ne_zero _ (by norm_num)⟩

lemma ratHeight_neg_one_pow (j : ℕ) : ratHeight ((-1 : ℚ) ^ j) = 1 := by
  rcases Nat.even_or_odd j with h | h
  · rw [h.neg_one_pow]; simp [ratHeight]
  · rw [h.neg_one_pow]; simp [ratHeight]

lemma famAtom_height {H j : ℕ} (hH : 2 ≤ H) (hj : j < H) : (famAtom H j).height = H := by
  apply le_antisymm
  · rw [Atom.height_le_iff]
    simp only [famAtom, ratHeight_neg_one_pow, Int.natAbs_natCast]
    refine ⟨hH, by omega, by omega, by simp [ratHeight]; omega, by omega⟩
  · have := (famAtom H j).k_lt_height
    have e : (famAtom H j).k = H - 1 := rfl
    omega

lemma famAtom_cons (H j : ℕ) : (famAtom H j).right = (famAtom H (j + 1)).left := by
  simp [famAtom, Atom.right, Atom.left]

lemma famAtom_match {H : ℕ} (hH : 1 ≤ H) (j : ℕ) :
    (famAtom H j).line (famAtom H j).right =
      (famAtom H (j + 1)).line (famAtom H (j + 1)).left := by
  obtain ⟨k, rfl⟩ : ∃ k, H = k + 1 := ⟨H - 1, by omega⟩
  simp only [famAtom, Atom.line, Atom.right, Atom.left, Atom.center, Nat.add_sub_cancel]
  push_cast
  field_simp
  ring

lemma den_odd_div_two_pow (i k : ℕ) : ((((2 * i + 1 : ℕ) : ℤ) : ℚ) / ((2 : ℚ) ^ k)).den = 2 ^ k := by
  have h := Rat.den_div_eq_of_coprime (a := ((2 * i + 1 : ℕ) : ℤ)) (b := ((2 ^ k : ℕ) : ℤ))
    (by positivity) (by
      simp only [Int.natAbs_natCast]
      exact Nat.Coprime.pow_right k (Nat.coprime_two_right.2 (odd_two_mul_add_one i)))
  have e : (((2 ^ k : ℕ) : ℤ) : ℚ) = (2 : ℚ) ^ k := by push_cast; ring
  rw [e] at h
  exact_mod_cast h

/-- The extremal family: lower bound for the expanded ReLU stream. -/
lemma streamRat_family_ge {H M : ℕ} (hH : 2 ≤ H) (hM : 1 ≤ M) :
    M * (2 * H - 1) ≤ (streamRat (famAtom H) (M + M)).length := by
  have key : ∀ j ∈ Finset.Ico 1 (M + M), 0 ≤ (codePairRat ((famAtom H j).left,
      (famAtom H j).s - (famAtom H (j - 1)).s)).length := fun _ _ => Nat.zero_le _
  have hodd : ∀ i < M, 2 * H - 1 ≤ (codePairRat ((famAtom H (2 * i + 1)).left,
      (famAtom H (2 * i + 1)).s - (famAtom H (2 * i + 1 - 1)).s)).length := by
    intro i _
    simp only [codePairRat, List.length_append, codeRat]
    have hd : ((famAtom H (2 * i + 1)).left).den = 2 ^ (H - 1) := by
      simp only [famAtom, Atom.left]
      exact den_odd_div_two_pow i (H - 1)
    rw [hd, length_eliasGamma, Nat.log_pow (by norm_num)]
    omega
  unfold streamRat
  simp only [List.length_append, List.length_flatten, List.map_map]
  unfold jumps
  rw [List.map_map, sum_range'_eq_sum_Ico, show M + M - 1 + 1 = M + M by omega]
  have hsub : (Finset.range M).image (fun i => 2 * i + 1) ⊆ Finset.Ico 1 (M + M) := by
    intro j hj
    simp only [Finset.mem_image, Finset.mem_range] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    simp only [Finset.mem_Ico]; omega
  have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j hj _ => key j hj)
  rw [Finset.sum_image (fun a _ b _ h => by simpa using h)] at h1
  have h2 : ∑ i ∈ Finset.range M, (2 * H - 1) ≤ ∑ i ∈ Finset.range M,
      (codePairRat ((famAtom H (2 * i + 1)).left,
        (famAtom H (2 * i + 1)).s - (famAtom H (2 * i + 1 - 1)).s)).length :=
    Finset.sum_le_sum fun i hi => hodd i (Finset.mem_range.1 hi)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at h2
  simp only [Function.comp_def] at h1 ⊢
  omega

/-- **Theorem 7.12** (rigorous comparison of the formats), extremal family.  For every `H ≥ 2` and
every even `N` with `2 ≤ N ≤ H`, the leaves `J_{H-1,j}` (`0 ≤ j < N`) with central value `0` and
slope `(-1)^j` form a continuous assembly (consecutive cells, matching values at the nodes) of
maximal atomic height exactly `H`, and (eq. (64))
`L_atom ≤ 200 N log₂ H`, `L_ReLU,str ≤ 200 N log₂ H` (the universal constant of eq. (63)), while
`L_ReLU,rat ≥ N H / 2`, i.e. `L_ReLU,rat = Ω(N H)`. -/
theorem formats_family {H N : ℕ} (hH : 2 ≤ H) (hNe : Even N) (hN2 : 2 ≤ N) (hNH : N ≤ H) :
    (∀ j, j + 1 < N → (famAtom H j).right = (famAtom H (j + 1)).left) ∧
    (∀ j, j + 1 < N → (famAtom H j).line (famAtom H j).right =
      (famAtom H (j + 1)).line (famAtom H (j + 1)).left) ∧
    chainFun (famAtom H) N ∈
      Asm (Set.Icc ((famAtom H 0).left : ℝ) ((famAtom H (N - 1)).right)) ∧
    IsAssemblyRep (Set.Icc ((famAtom H 0).left : ℝ) ((famAtom H (N - 1)).right))
      (chainFun (famAtom H) N) ((Finset.range N).image (famAtom H)) ∧
    ((Finset.range N).image (famAtom H)).card = N ∧
    maxHeight ((Finset.range N).image (famAtom H)) = H ∧
    ((streamAtom (famAtom H) N).length : ℝ) ≤ 200 * N * Real.logb 2 H ∧
    ((streamStr (famAtom H) N).length : ℝ) ≤ 200 * N * Real.logb 2 H ∧
    (N : ℝ) * H / 2 ≤ (streamRat (famAtom H) N).length := by
  have hcons : ∀ j, j + 1 < N → (famAtom H j).right = (famAtom H (j + 1)).left :=
    fun j _ => famAtom_cons H j
  have hmatch : ∀ j, j + 1 < N → (famAtom H j).line (famAtom H j).right =
      (famAtom H (j + 1)).line (famAtom H (j + 1)).left := fun j _ => famAtom_match (by omega) j
  have hht : ∀ j < N, (famAtom H j).height ≤ H := fun j hj => (famAtom_height hH (by omega)).le
  obtain ⟨b1, b2, -⟩ := formats_length_bounds (famAtom H) (by omega) hH hht
  refine ⟨hcons, hmatch, chain_mem_Asm (by omega) hcons hmatch,
    chain_isAssemblyRep (by omega) hcons hmatch, chain_card hcons, ?_, b1, b2, ?_⟩
  · apply le_antisymm
    · exact Finset.sup_le fun b hb => by
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hb
        exact hht j (Finset.mem_range.1 hj)
    · have : famAtom H 0 ∈ (Finset.range N).image (famAtom H) :=
        Finset.mem_image.2 ⟨0, Finset.mem_range.2 (by omega), rfl⟩
      have h := Finset.le_sup (f := Atom.height) this
      rw [famAtom_height hH (by omega)] at h
      exact h
  · obtain ⟨M, rfl⟩ := hNe
    have h := streamRat_family_ge (M := M) hH (by omega)
    have h' : ((M * (2 * H - 1) : ℕ) : ℝ) ≤ (streamRat (famAtom H) (M + M)).length := by
      exact_mod_cast h
    push_cast [Nat.cast_sub (show 1 ≤ 2 * H by omega)] at h'
    have : (1 : ℝ) ≤ H := by exact_mod_cast (show 1 ≤ H by omega)
    push_cast
    nlinarith

end Dyadic.Lib
