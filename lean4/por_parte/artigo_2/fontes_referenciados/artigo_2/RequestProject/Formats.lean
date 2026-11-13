import RequestProject.Coding
import RequestProject.Trees

/-!
# Section 3.3 — Height arithmetic (Lemma 3.7) and the three prefix-free formats (Theorem 3.8)
-/

namespace Artigo

open LTree

/-! ## Lemma 3.7 (cálculo elementar de alturas) -/

lemma rat_add_eq (r s : ℚ) : r + s = ((r.num * s.den + s.num * r.den : ℤ) : ℚ) / ((r.den * s.den : ℕ) : ℤ) := by
  have h1 : (r.den : ℚ) ≠ 0 := by positivity
  have h2 : (s.den : ℚ) ≠ 0 := by positivity
  conv_lhs => rw [← Rat.num_div_den r, ← Rat.num_div_den s]
  push_cast
  field_simp

lemma rat_mul_eq (r s : ℚ) : r * s = ((r.num * s.num : ℤ) : ℚ) / ((r.den * s.den : ℕ) : ℤ) := by
  conv_lhs => rw [← Rat.num_div_den r, ← Rat.num_div_den s]
  push_cast
  field_simp

/-- **Lemma 3.7**: `ht(r + s) ≤ 2 ht(r) ht(s)`. -/
theorem ht_add_le (r s : ℚ) : ht (r + s) ≤ 2 * ht r * ht s := by
  rw [rat_add_eq]
  refine le_trans (ht_div_le' _ _ (by positivity)) ?_
  have hr1 := le_max_left r.num.natAbs r.den
  have hr2 := le_max_right r.num.natAbs r.den
  have hs1 := le_max_left s.num.natAbs s.den
  have hs2 := le_max_right s.num.natAbs s.den
  simp only [ht] at *
  set R := max r.num.natAbs r.den
  set S := max s.num.natAbs s.den
  apply max_le
  · calc (r.num * s.den + s.num * r.den).natAbs ≤ (r.num * s.den).natAbs + (s.num * r.den).natAbs :=
          Int.natAbs_add_le _ _
      _ = r.num.natAbs * s.den + s.num.natAbs * r.den := by simp [Int.natAbs_mul]
      _ ≤ R * S + S * R := by gcongr
      _ = 2 * R * S := by ring
  · simp only [Int.natAbs_natCast]
    calc r.den * s.den ≤ R * S := by gcongr
      _ ≤ 2 * R * S := by nlinarith

/-- **Lemma 3.7**: `ht(r - s) ≤ 2 ht(r) ht(s)`. -/
theorem ht_sub_le (r s : ℚ) : ht (r - s) ≤ 2 * ht r * ht s := by
  rw [sub_eq_add_neg]; have := ht_add_le r (-s); rwa [ht_neg] at this

/-- **Lemma 3.7**: `ht(r s) ≤ ht(r) ht(s)`. -/
theorem ht_mul_le (r s : ℚ) : ht (r * s) ≤ ht r * ht s := by
  rw [rat_mul_eq]
  refine le_trans (ht_div_le' _ _ (by positivity)) ?_
  have hr1 := le_max_left r.num.natAbs r.den
  have hr2 := le_max_right r.num.natAbs r.den
  have hs1 := le_max_left s.num.natAbs s.den
  have hs2 := le_max_right s.num.natAbs s.den
  simp only [ht] at *
  apply max_le
  · rw [Int.natAbs_mul]; gcongr
  · simp only [Int.natAbs_natCast]; gcongr

/-- a dyadic fraction `n / 2^k` with `|n| ≤ A` and `k ≤ B` has reduced form `u 2^{-j}`,
`|u| ≤ A`, `j ≤ k`. -/
lemma dyadic_reduced (n : ℤ) (k : ℕ) :
    ((n : ℚ) / 2 ^ k).num.natAbs ≤ n.natAbs ∧ ∃ j ≤ k, ((n : ℚ) / 2 ^ k).den = 2 ^ j := by
  have hc : ((2 : ℚ) ^ k) = (((2 ^ k : ℕ) : ℤ) : ℚ) := by push_cast; rfl
  refine ⟨?_, ?_⟩
  · rw [hc]; exact num_div_le n (2 ^ k) (by positivity) |>.trans (by simp)
  · have := Rat.den_dvd n (2 ^ k : ℕ)
    rw [Rat.divInt_eq_div] at this
    push_cast at this
    have hd : ((n : ℚ) / 2 ^ k).den ∣ 2 ^ k := by exact_mod_cast this
    exact (Nat.dvd_prime_pow Nat.prime_two).mp hd

lemma ht_dyadic_le (n : ℤ) (k : ℕ) : ht ((n : ℚ) / 2 ^ k) ≤ max n.natAbs (2 ^ k) := by
  obtain ⟨h1, j, hj, h2⟩ := dyadic_reduced n k
  unfold ht; rw [h2]
  exact max_le_max h1 (Nat.pow_le_pow_right (by norm_num) hj)

lemma Atom.left_eq (a : Atom) : a.left = (a.m : ℚ) / 2 ^ a.k := rfl
lemma Atom.right_eq (a : Atom) : a.right = ((a.m + 1 : ℤ) : ℚ) / 2 ^ a.k := by
  simp [Atom.right]
lemma Atom.x0_eq (a : Atom) : a.x0 = ((2 * a.m + 1 : ℤ) : ℚ) / 2 ^ (a.k + 1) := by
  simp only [Atom.x0, pow_succ]; push_cast; field_simp

/-- **Lemma 3.7 (knots)**: every endpoint `t` of an atom of height `≤ H` has reduced form
`u 2^{-j}` with `|u| ≤ H`, `j ≤ H`; in particular `ht(t) ≤ 2^H`. -/
theorem Atom.endpoint_reduced (a : Atom) {H : ℕ} (hH : a.height ≤ H) :
    ∀ t ∈ ({a.left, a.right} : Set ℚ), t.num.natAbs ≤ H ∧ (∃ j ≤ H, t.den = 2 ^ j) ∧ ht t ≤ 2 ^ H := by
  have hk := a.k_lt_height
  have hm := a.m_lt_height
  have hHk : a.k ≤ H := by omega
  have hpow : H ≤ 2 ^ H := le_of_lt (Nat.lt_two_pow_self)
  intro t ht
  rcases ht with rfl | rfl
  · obtain ⟨h1, j, hj, h2⟩ := dyadic_reduced a.m a.k
    rw [← a.left_eq] at h1 h2
    refine ⟨by omega, ⟨j, by omega, h2⟩, ?_⟩
    unfold ht; rw [h2]
    exact max_le (by omega) (Nat.pow_le_pow_right (by norm_num) (by omega))
  · obtain ⟨h1, j, hj, h2⟩ := dyadic_reduced (a.m + 1) a.k
    rw [← a.right_eq] at h1 h2
    have : (a.m + 1).natAbs ≤ H := by omega
    refine ⟨by omega, ⟨j, by omega, h2⟩, ?_⟩
    unfold ht; rw [h2]
    exact max_le (by omega) (Nat.pow_le_pow_right (by norm_num) (by omega))

lemma Atom.ht_x0_le (a : Atom) {H : ℕ} (hH : a.height ≤ H) : ht a.x0 ≤ 2 ^ H := by
  have hk := a.k_lt_height
  have hm := a.m_lt_height
  rw [a.x0_eq]
  refine le_trans (ht_dyadic_le _ _) (max_le ?_ (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have : (2 * a.m + 1).natAbs ≤ 2 * H := by omega
  have h2 : 2 * H ≤ 2 ^ H := by
    have h2H : 2 ≤ H := le_trans a.two_le_height hH
    clear * - h2H
    induction H with
    | zero => omega
    | succ n ih =>
      rcases Nat.lt_or_ge n 2 with h | h
      · interval_cases n <;> simp_all
      · have := ih h; rw [pow_succ]; omega
  omega

/-- **Lemma 3.7**: slope jumps have height `≤ 2H^2`. -/
theorem slope_jump_height {a b : Atom} {H : ℕ} (ha : a.height ≤ H) (hb : b.height ≤ H) :
    ht (b.s - a.s) ≤ 2 * H ^ 2 := by
  refine le_trans (ht_sub_le _ _) ?_
  have h1 := le_trans b.ht_s_le_height hb
  have h2 := le_trans a.ht_s_le_height ha
  calc 2 * ht b.s * ht a.s ≤ 2 * H * H := by gcongr
    _ = 2 * H ^ 2 := by ring

/-- **Lemma 3.7**: `ht(s_j t_j) ≤ H 2^H`. -/
theorem slope_knot_height {a : Atom} {H : ℕ} (ha : a.height ≤ H) :
    ht (a.s * a.left) ≤ H * 2 ^ H := by
  refine le_trans (ht_mul_le _ _) ?_
  have h1 := le_trans a.ht_s_le_height ha
  have h2 := (a.endpoint_reduced ha a.left (by simp)).2.2
  gcongr

/-- **Lemma 3.7**: the intercept `g(t₀) - s₀ t₀ = y₀ - s₀ x₀` has height `≤ 2^{H+1} H^2`. -/
theorem intercept_height {a : Atom} {H : ℕ} (ha : a.height ≤ H) :
    ht (a.y0 - a.s * a.x0) ≤ 2 ^ (H + 1) * H ^ 2 := by
  refine le_trans (ht_sub_le _ _) ?_
  have h1 := le_trans a.ht_y0_le_height ha
  have h2 : ht (a.s * a.x0) ≤ H * 2 ^ H :=
    le_trans (ht_mul_le _ _) (Nat.mul_le_mul (le_trans a.ht_s_le_height ha) (a.ht_x0_le ha))
  calc 2 * ht a.y0 * ht (a.s * a.x0) ≤ 2 * H * (H * 2 ^ H) := by gcongr
    _ = 2 ^ (H + 1) * H ^ 2 := by ring

lemma Atom.lval_sub (a : Atom) : a.lval - a.s * a.left = a.y0 - a.s * a.x0 := by
  simp only [Atom.lval, Atom.evalQ]; ring

/-- **Lemma 3.7 (assembly form)**: for an assembly of maximal atomic height `H`, every pair of
consecutive leaves satisfies `ht(s_j - s_{j-1}) ≤ 2H^2`, the knot `t_j` is `u_j 2^{-k_j}` with
`|u_j| ≤ H`, `k_j ≤ H`, `ht(s_j t_j) ≤ H 2^H`, and `ht(g(t₀) - s₀ t₀) ≤ 2^{H+1} H^2`. -/
theorem assembly_height_arith {k : ℕ} {m : ℤ} {T : LTree} (hT : WF k m T) {H : ℕ}
    (hH : T.maxHeight ≤ H) :
    (∀ p ∈ T.leaves.zip T.leaves.tail,
      ht (p.2.s - p.1.s) ≤ 2 * H ^ 2 ∧ p.2.left.num.natAbs ≤ H ∧ (∃ j ≤ H, p.2.left.den = 2 ^ j) ∧
      ht (p.2.s * p.2.left) ≤ H * 2 ^ H) ∧
    ht (T.lval - T.firstLeaf.s * T.firstLeaf.left) ≤ 2 ^ (H + 1) * H ^ 2 := by
  have hall := maxHeight_le_iff.mp hH
  refine ⟨fun p hp => ?_, ?_⟩
  · have h1 : p.1 ∈ T.leaves := (List.of_mem_zip hp).1
    have h2 : p.2 ∈ T.leaves := List.mem_of_mem_tail (List.of_mem_zip hp).2
    have := p.2.endpoint_reduced (hall _ h2) p.2.left (by simp)
    exact ⟨slope_jump_height (hall _ h1) (hall _ h2), this.1, this.2.1,
      slope_knot_height (hall _ h2)⟩
  · obtain ⟨L, hL⟩ := leaves_eq_cons T
    have hf : T.firstLeaf ∈ T.leaves := by rw [hL]; simp
    rw [← (firstLeaf_left hT).2, Atom.lval_sub]
    exact intercept_height (hall _ hf)

/-! ## The three formats -/

/-- per-leaf block of `C_atom`: `γ(k+1) C_ℤ(m) C_rat(y₀) C_rat(s)` -/
def atomTuple (a : Atom) : (ℕ × ℤ) × (ℚ × ℚ) := ((a.k + 1, a.m), (a.y0, a.s))

/-- inverse of `atomTuple` (rejects `s = 0`) -/
def atomOfTuple (p : (ℕ × ℤ) × (ℚ × ℚ)) : Option Atom :=
  if h : p.2.2 ≠ 0 then some ⟨p.1.1 - 1, p.1.2, p.2.1, p.2.2, h⟩ else none

/-- the per-leaf atomic block codec -/
def atomBlockCodec : Codec Atom :=
  ((gammaCodec.prod intCodec).prod (ratCodec.prod ratCodec)).map atomTuple atomOfTuple

lemma atomBlockCodec_RT : atomBlockCodec.RT (fun _ => True) := by
  apply ((gammaCodec_RT.prod intCodec_RT).prod (ratCodec_RT.prod ratCodec_RT)).map
  intro a _
  refine ⟨⟨⟨by simp [atomTuple], trivial⟩, trivial, trivial⟩, ?_⟩
  simp [atomOfTuple, atomTuple, a.hs]

/-- **format (i)** `C_atom(g)`: `γ(N)` followed by the atomic blocks of the leaves. -/
def CatomCodec : Codec (List Atom) := atomBlockCodec.withLen

/-- a ReLU-type stream: `γ(N)`, a head, then `N-1` pairs (knot, slope jump) -/
def reluCodec {Hd : Type*} (cHead : Codec Hd) (cKnot : Codec ℚ) : Codec (Hd × List (ℚ × ℚ)) where
  enc p := gamma (p.2.length + 1) ++ cHead.enc p.1 ++ (cKnot.prod ratCodec).encList p.2
  dec s := match decGamma s with
    | none => none
    | some (n, s₁) => match cHead.dec s₁ with
      | none => none
      | some (h, s₂) => match (cKnot.prod ratCodec).decN (n - 1) s₂ with
        | none => none
        | some (L, s₃) => some ((h, L), s₃)

lemma reluCodec_RT {Hd : Type*} {cHead : Codec Hd} {cKnot : Codec ℚ} {PH : Hd → Prop}
    {PK : ℚ → Prop} (hH : cHead.RT PH) (hK : cKnot.RT PK) :
    (reluCodec cHead cKnot).RT (fun p => PH p.1 ∧ ∀ q ∈ p.2, PK q.1) := by
  rintro ⟨h, L⟩ ⟨hh, hL⟩ t
  simp only [reluCodec, List.append_assoc]
  rw [decGamma_gamma (by omega)]
  simp only
  rw [hH h hh]
  simp only [Nat.add_sub_cancel]
  rw [(hK.prod ratCodec_RT).decN L (fun q hq => ⟨hL q hq, trivial⟩) t]

/-- the (knot, slope-jump) pairs of consecutive leaves -/
def reluPairs (L : List Atom) : List (ℚ × ℚ) := (L.zip L.tail).map (fun p => (p.2.left, p.2.s - p.1.s))

/-- **format (ii)** parameters: `(x₀, y₀, s₀)` of the first atom and the pairs `(t_j, s_j - s_{j-1})`. -/
def strParams : List Atom → (ℚ × ℚ × ℚ) × List (ℚ × ℚ)
  | [] => ((0, 0, 0), [])
  | a :: L => ((a.x0, a.y0, a.s), reluPairs (a :: L))

/-- **format (iii)** parameters: intercept `c = g(t₀) - s₀ t₀`, slope `s₀` and the pairs. -/
def ratParams : List Atom → (ℚ × ℚ) × List (ℚ × ℚ)
  | [] => ((0, 0), [])
  | a :: L => ((a.y0 - a.s * a.x0, a.s), reluPairs (a :: L))

/-- the structural ReLU codec `C_{ReLU,str}` (dyadic knots coded structurally) -/
def strCodec : Codec ((ℚ × ℚ × ℚ) × List (ℚ × ℚ)) :=
  reluCodec (dyadCodec.prod (ratCodec.prod ratCodec)) dyadCodec

/-- the expanded rational ReLU codec `C_{ReLU,rat}` -/
def ratReluCodec : Codec ((ℚ × ℚ) × List (ℚ × ℚ)) :=
  reluCodec (ratCodec.prod ratCodec) ratCodec

/-- `L_atom(g)` -/
def Latom (L : List Atom) : ℕ := (CatomCodec.enc L).length
/-- `L_{ReLU,str}(g)` -/
def Lstr (L : List Atom) : ℕ := (strCodec.enc (strParams L)).length
/-- `L_{ReLU,rat}(g)` -/
def Lrat (L : List Atom) : ℕ := (ratReluCodec.enc (ratParams L)).length

lemma Atom.x0_dyadic (a : Atom) : IsDyadic a.x0 := by
  obtain ⟨_, j, _, h⟩ := dyadic_reduced (2 * a.m + 1) (a.k + 1)
  exact ⟨j, by rw [a.x0_eq]; exact h⟩

lemma Atom.left_dyadic (a : Atom) : IsDyadic a.left := by
  obtain ⟨_, j, _, h⟩ := dyadic_reduced a.m a.k
  exact ⟨j, h⟩

lemma reluPairs_dyadic (L : List Atom) : ∀ q ∈ reluPairs L, IsDyadic q.1 := by
  intro q hq
  simp only [reluPairs, List.mem_map] at hq
  obtain ⟨p, _, rfl⟩ := hq
  exact p.2.left_dyadic

lemma reluPairs_length (a : Atom) (L : List Atom) : (reluPairs (a :: L)).length + 1 = (a :: L).length := by
  simp [reluPairs]

/-- **Theorem 3.8 (exact decoders)**: the three streams are self-delimiting (hence prefix-free)
with exact decoders: `C_atom` recovers the list of leaf atoms, the ReLU streams recover their
parameters. -/
theorem coding_formats_decoders :
    CatomCodec.RT (fun L => L ≠ []) ∧
    (∀ L : List Atom, ∀ t, strCodec.dec (strCodec.enc (strParams L) ++ t) = some (strParams L, t)) ∧
    (∀ L : List Atom, ∀ t, ratReluCodec.dec (ratReluCodec.enc (ratParams L) ++ t) = some (ratParams L, t)) := by
  refine ⟨fun L hL t => atomBlockCodec_RT.withLen L ⟨hL, fun _ _ => trivial⟩ t, ?_, ?_⟩
  · intro L t
    apply reluCodec_RT (dyadCodec_RT.prod (ratCodec_RT.prod ratCodec_RT)) dyadCodec_RT
    cases L with
    | nil => exact ⟨⟨⟨0, by simp [strParams]⟩, trivial, trivial⟩, by simp [strParams]⟩
    | cons a L => exact ⟨⟨a.x0_dyadic, trivial, trivial⟩, reluPairs_dyadic _⟩
  · intro L t
    exact reluCodec_RT (ratCodec_RT.prod ratCodec_RT) ratCodec_RT (PK := fun _ => True) _
      ⟨⟨trivial, trivial⟩, fun _ _ => trivial⟩ t

/-! ### Length bounds -/

lemma nlog_le {n a e H : ℕ} (hH : 1 ≤ H) (hn : n ≤ 2 ^ a * H ^ e) :
    Nat.log 2 n ≤ a + e * (Nat.log 2 H + 1) := by
  have h1 : H ≤ 2 ^ (Nat.log 2 H + 1) := (Nat.lt_pow_succ_log_self (by norm_num) H).le
  have h2 : n ≤ 2 ^ (a + e * (Nat.log 2 H + 1)) := by
    calc n ≤ 2 ^ a * H ^ e := hn
      _ ≤ 2 ^ a * (2 ^ (Nat.log 2 H + 1)) ^ e := by gcongr
      _ = 2 ^ (a + e * (Nat.log 2 H + 1)) := by rw [← pow_mul, ← pow_add, mul_comm]
  calc Nat.log 2 n ≤ Nat.log 2 (2 ^ (a + e * (Nat.log 2 H + 1))) := Nat.log_mono_right h2
    _ = _ := Nat.log_pow (by norm_num) _

lemma log_le_self' (H : ℕ) : Nat.log 2 H ≤ H := by
  rcases Nat.eq_zero_or_pos H with h | h
  · simp [h]
  · exact (Nat.log_lt_self 2 h.ne').le

lemma ratCodec_length_le_ht {r : ℚ} {a e H : ℕ} (hH : 1 ≤ H) (hr : ht r ≤ 2 ^ a * H ^ e) :
    (ratCodec.enc r).length ≤ 4 * (a + e * (Nat.log 2 H + 1)) + 7 := by
  have h1 : 1 ≤ 2 ^ a * H ^ e := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have := ratCodec_length_le h1 hr
  have := nlog_le hH (le_refl (2 ^ a * H ^ e))
  omega

lemma atomBlock_length_le {a : Atom} {H : ℕ} (ha : a.height ≤ H) :
    (atomBlockCodec.enc a).length ≤ 12 * Nat.log 2 H + 20 := by
  have hH : 2 ≤ H := le_trans a.two_le_height ha
  have hk := a.k_lt_height
  have hm := a.m_lt_height
  simp only [atomBlockCodec, Codec.map, Codec.prod, List.length_append, atomTuple, gammaCodec]
  have e1 : (gamma (a.k + 1)).length ≤ 2 * Nat.log 2 H + 1 := by
    rw [gamma_length]; have := Nat.log_mono_right (b := 2) (show a.k + 1 ≤ H by omega); omega
  have e2 := intCodec_length_le (A := H) (by omega) (show a.m.natAbs ≤ H by omega)
  have e3 := ratCodec_length_le (A := H) (by omega) (le_trans a.ht_y0_le_height ha)
  have e4 := ratCodec_length_le (A := H) (by omega) (le_trans a.ht_s_le_height ha)
  omega

lemma gamma_length_le_self {N : ℕ} : (gamma N).length ≤ 2 * N + 1 := by
  rw [gamma_length]
  rcases Nat.eq_zero_or_pos N with h | h
  · simp [h]
  · have := (Nat.log_lt_self 2 h.ne').le; omega

lemma sum_map_le {α : Type*} (L : List α) (f : α → ℕ) (B : ℕ) (h : ∀ x ∈ L, f x ≤ B) :
    (L.map f).sum ≤ L.length * B := by
  have := List.sum_le_card_nsmul (L.map f) B (by simpa using h)
  simpa using this

/-- bound on `L_atom` -/
lemma Latom_le {L : List Atom} {H : ℕ} (hH : 2 ≤ H) (hL : L ≠ []) (hh : ∀ a ∈ L, a.height ≤ H) :
    Latom L ≤ 35 * L.length * Nat.log 2 H := by
  have hlog : 1 ≤ Nat.log 2 H := Nat.le_log_of_pow_le (by norm_num) (by simpa using hH)
  have hN : 1 ≤ L.length := List.length_pos_iff.mpr hL
  unfold Latom CatomCodec Codec.withLen
  simp only [List.length_append]
  rw [Codec.encList_length]
  try dsimp only
  have h1 := sum_map_le L (fun x => (atomBlockCodec.enc x).length) (12 * Nat.log 2 H + 20)
    (fun a ha => atomBlock_length_le (hh a ha))
  have h2 : (gamma L.length).length ≤ 2 * L.length + 1 := gamma_length_le_self
  nlinarith

lemma pair_heights {L : List Atom} {H : ℕ} (hh : ∀ a ∈ L, a.height ≤ H) :
    ∀ q ∈ reluPairs L, q.1.num.natAbs ≤ H ∧ (∃ j ≤ H, q.1.den = 2 ^ j) ∧ ht q.1 ≤ 2 ^ H ∧
      ht q.2 ≤ 2 * H ^ 2 := by
  intro q hq
  simp only [reluPairs, List.mem_map] at hq
  obtain ⟨p, hp, rfl⟩ := hq
  have h1 : p.1 ∈ L := (List.of_mem_zip hp).1
  have h2 : p.2 ∈ L := List.mem_of_mem_tail (List.of_mem_zip hp).2
  have := p.2.endpoint_reduced (hh _ h2) p.2.left (by simp)
  exact ⟨this.1, this.2.1, this.2.2, slope_jump_height (hh _ h1) (hh _ h2)⟩

/-- bound on `L_{ReLU,str}` -/
lemma Lstr_le {L : List Atom} {H : ℕ} (hH : 2 ≤ H) (hL : L ≠ []) (hh : ∀ a ∈ L, a.height ≤ H) :
    Lstr L ≤ 100 * L.length * Nat.log 2 H := by
  have hlog : 1 ≤ Nat.log 2 H := Nat.le_log_of_pow_le (by norm_num) (by simpa using hH)
  obtain ⟨a, L', rfl⟩ := List.exists_cons_of_ne_nil hL
  have ha := hh a (by simp)
  have hk := a.k_lt_height
  have hm := a.m_lt_height
  have e2H : Nat.log 2 (2 * H) = Nat.log 2 H + 1 := by
    rw [mul_comm, Nat.log_mul_base (by norm_num) (by omega)]
  have hlogH1 : Nat.log 2 (H + 1) ≤ Nat.log 2 H + 1 := by
    rw [← e2H]; exact Nat.log_mono_right (by omega)
  unfold Lstr strCodec reluCodec
  simp only [strParams, List.length_append, Codec.prod]
  rw [Codec.encList_length]
  try dsimp only
  -- head
  obtain ⟨hx1, j, hj, hx2⟩ := dyadic_reduced (2 * a.m + 1) (a.k + 1)
  rw [← a.x0_eq] at hx1 hx2
  have e1 := dyadCodec_length_le (A := 2 * H) (B := H + 1) (by omega) (by omega) hx2 (by omega)
  have e2 := ratCodec_length_le (A := H) (by omega) (le_trans a.ht_y0_le_height ha)
  have e3 := ratCodec_length_le (A := H) (by omega) (le_trans a.ht_s_le_height ha)
  -- pairs
  have hp := sum_map_le (reluPairs (a :: L')) (fun q => (dyadCodec.enc q.1 ++ ratCodec.enc q.2).length)
    (12 * Nat.log 2 H + 29) (by
      intro q hq
      obtain ⟨h1, ⟨j, hj, h2⟩, _, h4⟩ := pair_heights hh q hq
      simp only [List.length_append]
      have f1 := dyadCodec_length_le (A := H) (B := H + 1) (by omega) h1 h2 (by omega)
      have f2 := ratCodec_length_le_ht (a := 1) (e := 2) (H := H) (by omega) (by simpa using h4)
      omega)
  have hlen := reluPairs_length a L'
  have hg := gamma_length_le_self (N := (reluPairs (a :: L')).length + 1)
  simp only [List.length_cons] at hlen ⊢
  nlinarith

/-- bound on `L_{ReLU,rat}` -/
lemma Lrat_le {L : List Atom} {H : ℕ} (hH : 2 ≤ H) (hL : L ≠ []) (hh : ∀ a ∈ L, a.height ≤ H) :
    Lrat L ≤ 100 * L.length * H := by
  obtain ⟨a, L', rfl⟩ := List.exists_cons_of_ne_nil hL
  have ha := hh a (by simp)
  have hlogH := log_le_self' H
  unfold Lrat ratReluCodec reluCodec
  simp only [ratParams, List.length_append, Codec.prod]
  rw [Codec.encList_length]
  try dsimp only
  have e1 := ratCodec_length_le_ht (a := H + 1) (e := 2) (H := H) (by omega) (intercept_height ha)
  have e2 := ratCodec_length_le (A := H) (by omega) (le_trans a.ht_s_le_height ha)
  have hp := sum_map_le (reluPairs (a :: L')) (fun q => (ratCodec.enc q.1 ++ ratCodec.enc q.2).length)
    (12 * H + 26) (by
      intro q hq
      obtain ⟨_, _, h3, h4⟩ := pair_heights hh q hq
      simp only [List.length_append]
      have f1 := ratCodec_length_le_ht (a := H) (e := 0) (H := H) (by omega) (by simpa using h3)
      have f2 := ratCodec_length_le_ht (a := 1) (e := 2) (H := H) (by omega) (by simpa using h4)
      omega)
  have hlen := reluPairs_length a L'
  have hg := gamma_length_le_self (N := (reluPairs (a :: L')).length + 1)
  simp only [List.length_cons] at hlen ⊢
  nlinarith

/-- **Theorem 3.8 (orders)**: for every assembly with `N` leaves and maximal atomic height
`H ≥ 2`, `L_atom = O(N log H)`, `L_{ReLU,str} = O(N log H)`, `L_{ReLU,rat} = O(N H)`, with
universal constants. -/
theorem coding_format_orders : ∃ C : ℕ, ∀ H : ℕ, 2 ≤ H → ∀ L : List Atom, L ≠ [] →
    (∀ a ∈ L, a.height ≤ H) →
    Latom L ≤ C * L.length * Nat.log 2 H ∧ Lstr L ≤ C * L.length * Nat.log 2 H ∧
    Lrat L ≤ C * L.length * H := by
  refine ⟨100, fun H hH L hL hh => ⟨?_, ?_, ?_⟩⟩
  · have := Latom_le hH hL hh
    have : 35 * L.length * Nat.log 2 H ≤ 100 * L.length * Nat.log 2 H := by gcongr; norm_num
    omega
  · exact Lstr_le hH hL hh
  · exact Lrat_le hH hL hh

/-! ### The extremal family -/

/-- the atom on `J_{H-1,j}` with central value `0` and slope `(-1)^j` -/
def famAtom (H : ℕ) (j : ℕ) : Atom := ⟨H - 1, j, 0, (-1) ^ j, by simp⟩

/-- the family of Theorem 3.8: leaves `J_{H-1,j}`, `0 ≤ j < N` -/
def famList (H N : ℕ) : List Atom := (List.range N).map (famAtom H)

lemma famAtom_height {H j : ℕ} (hH : 2 ≤ H) (hj : j < H) : (famAtom H j).height = H := by
  have h1 : ht ((-1 : ℚ) ^ j) = 1 := by
    rcases neg_one_pow_eq_or ℚ j with h | h <;> rw [h] <;> simp [ht]
  simp only [Atom.height, famAtom, h1, ht_zero]
  simp only [Int.natAbs_natCast]
  omega

lemma famAtom_contig (H j : ℕ) : Contig (famAtom H j) (famAtom H (j + 1)) := by
  constructor
  · simp [famAtom, cR, cL]
  · rw [Atom.rval_eq, Atom.lval_eq]
    simp only [famAtom, pow_succ]
    ring

lemma famList_chain (H N : ℕ) : List.IsChain Contig (famList H N) := by
  unfold famList
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.map_append]
    rw [List.isChain_append]
    refine ⟨ih, by simp, ?_⟩
    intro x hx y hy
    simp only [List.map_cons, List.map_nil, List.head?_cons, Option.mem_def, Option.some.injEq] at hy
    subst hy
    cases N with
    | zero => simp at hx
    | succ N =>
      rw [List.range_succ, List.map_append] at hx
      simp at hx; subst hx
      exact famAtom_contig H N

lemma famList_tail (H n : ℕ) :
    (famList H (n + 1)).tail = (List.range n).map (fun j => famAtom H (j + 1)) := by
  simp [famList, List.range_succ_eq_map, List.map_map, Function.comp_def]

lemma famAtom_left_den {H j : ℕ} (hH : 2 ≤ H) (hj : Odd j) : (famAtom H j).left.den = 2 ^ (H - 1) := by
  simp only [famAtom, Atom.left]
  have hc : ((2 : ℚ) ^ (H - 1)) = (((2 ^ (H - 1) : ℕ) : ℤ) : ℚ) := by push_cast; rfl
  have hj' : ((j : ℤ) : ℚ) = (j : ℚ) := by push_cast; rfl
  rw [hc]
  have hcop : (j : ℤ).natAbs.Coprime ((2 ^ (H - 1) : ℕ) : ℤ).natAbs := by
    simp only [Int.natAbs_natCast]
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hj) |>.symm.symm
  have := Rat.den_div_eq_of_coprime (a := (j : ℤ)) (b := ((2 ^ (H - 1) : ℕ) : ℤ)) (by positivity) hcop
  exact_mod_cast this

lemma Lrat_ge_tail (L : List Atom) (hL : L ≠ []) :
    ((L.tail).map (fun b => 2 * Nat.log 2 b.left.den)).sum ≤ Lrat L := by
  obtain ⟨a, L', rfl⟩ := List.exists_cons_of_ne_nil hL
  unfold Lrat ratReluCodec reluCodec
  simp only [ratParams, List.length_append, Codec.prod]
  rw [Codec.encList_length]
  try dsimp only
  have : ((a :: L').tail.map (fun b => 2 * Nat.log 2 b.left.den)).sum ≤
      ((reluPairs (a :: L')).map (fun q => (ratCodec.enc q.1 ++ ratCodec.enc q.2).length)).sum := by
    have e : (a :: L').tail = ((a :: L').zip (a :: L').tail).map Prod.snd :=
      (List.map_snd_zip (by simp)).symm
    rw [e, List.map_map, reluPairs, List.map_map]
    apply List.sum_le_sum
    intro p _
    simp only [Function.comp_apply, List.length_append]
    have := ratCodec_length_ge_log_den p.2.left
    omega
  omega

lemma odd_sum_bound (H : ℕ) (hH : 2 ≤ H) : ∀ k : ℕ,
    (k + 1) * (2 * (H - 1)) ≤ ((List.range (2 * k + 1)).map
      (fun j => 2 * Nat.log 2 (famAtom H (j + 1)).left.den)).sum := by
  intro k
  induction k with
  | zero =>
    rw [show 2 * 0 + 1 = 1 by rfl, List.range_one]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [famAtom_left_den hH (by decide), Nat.log_pow (by norm_num)]; omega
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring, List.range_succ, List.range_succ]
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    rw [famAtom_left_den (j := 2 * k + 1 + 1 + 1) hH ⟨k + 1, by ring⟩, Nat.log_pow (by norm_num)]
    nlinarith

/-- **Theorem 3.8 (extremal family)**: for `H ≥ 2` and even `N` with `2 ≤ N ≤ H`, the leaves
`J_{H-1,j}`, `0 ≤ j < N`, with central values `0` and slopes `(-1)^j` form a continuous
assembly of height exactly `H`, with `L_atom, L_{ReLU,str} = O(N log H)` and
`L_{ReLU,rat} = Ω(NH)` (explicitly `NH ≤ 2 L_{ReLU,rat}`). -/
theorem coding_gap_family : ∃ C : ℕ, ∀ H N : ℕ, 2 ≤ H → Even N → 2 ≤ N → N ≤ H →
    List.IsChain Contig (famList H N) ∧ (∀ a ∈ famList H N, a.height = H) ∧
    (famList H N).length = N ∧
    Latom (famList H N) ≤ C * N * Nat.log 2 H ∧ Lstr (famList H N) ≤ C * N * Nat.log 2 H ∧
    N * H ≤ 2 * Lrat (famList H N) := by
  obtain ⟨C, hC⟩ := coding_format_orders
  refine ⟨C, fun H N hH hN hN2 hNH => ?_⟩
  have hheight : ∀ a ∈ famList H N, a.height = H := by
    intro a ha
    simp only [famList, List.mem_map, List.mem_range] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    exact famAtom_height hH (by omega)
  have hlen : (famList H N).length = N := by simp [famList]
  have hne : famList H N ≠ [] := by
    intro h; have := congrArg List.length h; rw [hlen] at this; simp at this; omega
  have hb := hC H hH (famList H N) hne (fun a ha => (hheight a ha).le)
  rw [hlen] at hb
  refine ⟨famList_chain H N, hheight, hlen, hb.1, hb.2.1, ?_⟩
  obtain ⟨k, hk⟩ := hN
  have hN' : N = (2 * (k - 1) + 1) + 1 := by omega
  have h1 := Lrat_ge_tail (famList H N) hne
  rw [hN', famList_tail, List.map_map] at h1
  have h2 := odd_sum_bound H hH (k - 1)
  erw [show ((fun b : Atom => 2 * Nat.log 2 b.left.den) ∘ fun j => famAtom H (j + 1)) =
    (fun j => 2 * Nat.log 2 (famAtom H (j + 1)).left.den) from rfl] at h1
  rw [← hN'] at h1
  have : N * H ≤ 2 * (k * (2 * (H - 1))) := by
    rw [hk]
    have : k - 1 + 1 = k := by omega
    nlinarith [Nat.sub_add_cancel (show 1 ≤ H by omega)]
  have hk1 : k - 1 + 1 = k := by omega
  rw [hk1] at h2
  omega

end Artigo
