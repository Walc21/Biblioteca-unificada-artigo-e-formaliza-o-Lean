import RequestProject.EntropyLower

/-!
# Theorem 3.14, codebook: counting the quantized interpolants by the curvature constraint
-/

namespace Artigo

open Set LTree

/-! ## Second differences -/

/-- `|f(t+h) - 2 f(t) + f(t-h)| ≤ M h²` for `f ∈ 𝓕_{R,M}` -/
lemma FRM_second_diff {R M : ℝ} {f : ℝ → ℝ} (hf : f ∈ FRM R M) {t h : ℝ}
    (h1 : t - h ∈ Icc (0 : ℝ) 1) (h2 : t ∈ Icc (0 : ℝ) 1) (h3 : t + h ∈ Icc (0 : ℝ) 1) :
    |f (t + h) - 2 * f t + f (t - h)| ≤ M * h ^ 2 := by
  obtain ⟨hd, hd2⟩ := FRM_hasDeriv hf
  have a := taylor1_bound hd hd2 hf.2.2 h2 h3
  have b := taylor1_bound hd hd2 hf.2.2 h2 h1
  have e : f (t + h) - 2 * f t + f (t - h) =
      (f (t + h) - f t - deriv f t * (t + h - t)) + (f (t - h) - f t - deriv f t * (t - h - t)) := by
    ring
  rw [e]
  calc _ ≤ |f (t + h) - f t - deriv f t * (t + h - t)| + |f (t - h) - f t - deriv f t * (t - h - t)| :=
        abs_add_le _ _
    _ ≤ M / 2 * (t + h - t) ^ 2 + M / 2 * (t - h - t) ^ 2 := add_le_add a b
    _ = M * h ^ 2 := by ring

/-- second differences of the numerators: `|b_{i+2} - 2 b_{i+1} + b_i| ≤ 2M + 4` -/
lemma bnum_second_diff {R M : ℝ} {f : ℝ → ℝ} (hf : f ∈ FRM R M) (r : ℕ) {i : ℤ} (h0 : 0 ≤ i)
    (h2 : i + 2 ≤ 2 ^ r) :
    |(bnum f r (i + 2) : ℝ) - 2 * bnum f r (i + 1) + bnum f r i| ≤ 2 * M + 4 := by
  have hn : (0 : ℝ) < 2 ^ r := by positivity
  have hsd := FRM_second_diff hf (t := cL r (i + 1)) (h := 1 / 2 ^ r)
    (by rw [show cL r (i + 1) - 1 / 2 ^ r = cL r i by unfold cL; push_cast; field_simp; ring]
        exact cL_mem01 h0 (by omega))
    (cL_mem01 (by omega) (by omega))
    (by rw [show cL r (i + 1) + 1 / 2 ^ r = cL r (i + 2) by unfold cL; push_cast; field_simp; ring]
        exact cL_mem01 (by omega) h2)
  rw [show cL r (i + 1) - 1 / 2 ^ r = cL r i by unfold cL; push_cast; field_simp; ring,
    show cL r (i + 1) + 1 / 2 ^ r = cL r (i + 2) by unfold cL; push_cast; field_simp; ring] at hsd
  have e0 := jvals_err f r i
  have e1 := jvals_err f r (i + 1)
  have e2 := jvals_err f r (i + 2)
  have h2r : (2 : ℝ) ^ (2 * r) = (2 ^ r) ^ 2 := by rw [← pow_mul, mul_comm]
  rw [bnum_cast, bnum_cast, bnum_cast]
  have e : 2 * 2 ^ (2 * r) * ((jvals f r (i + 2) : ℚ) : ℝ) - 2 * (2 * 2 ^ (2 * r) * ((jvals f r (i + 1) : ℚ) : ℝ))
      + 2 * 2 ^ (2 * r) * ((jvals f r i : ℚ) : ℝ) = 2 * 2 ^ (2 * r) *
      ((f (cL r (i + 2)) - 2 * f (cL r (i + 1)) + f (cL r i)) - (f (cL r (i + 2)) - jvals f r (i + 2))
        + 2 * (f (cL r (i + 1)) - jvals f r (i + 1)) - (f (cL r i) - jvals f r i)) := by ring
  rw [e, abs_mul, abs_of_pos (by positivity)]
  have hb : |(f (cL r (i + 2)) - 2 * f (cL r (i + 1)) + f (cL r i)) - (f (cL r (i + 2)) - jvals f r (i + 2))
        + 2 * (f (cL r (i + 1)) - jvals f r (i + 1)) - (f (cL r i) - jvals f r i)| ≤
      M * (1 / 2 ^ r) ^ 2 + 4 * (1 / (2 * 2 ^ (2 * r))) := by
    have ha := abs_le.mp hsd
    have hb0 := abs_le.mp e0
    have hb1 := abs_le.mp e1
    have hb2 := abs_le.mp e2
    rw [abs_le]; constructor <;> linarith [ha.1, ha.2, hb0.1, hb0.2, hb1.1, hb1.2, hb2.1, hb2.2]
  calc _ ≤ 2 * 2 ^ (2 * r) * (M * (1 / 2 ^ r) ^ 2 + 4 * (1 / (2 * 2 ^ (2 * r)))) := by gcongr
    _ = 2 * M + 4 := by rw [h2r]; field_simp

/-! ## Counting sequences with bounded second differences -/

/-- initial pairs `[b₁, b₀]` with `|b₀| ≤ B₀`, `|b₁ - b₀| ≤ B₁` -/
def initPairs (B0 B1 : ℤ) : Finset (List ℤ) :=
  (Finset.Icc (-B0) B0).biUnion fun b0 => (Finset.Icc (b0 - B1) (b0 + B1)).image fun b1 => [b1, b0]

/-- reversed sequences `[b_{m+1}, …, b₀]` with the initial constraints and all second differences
bounded by `D` -/
def seqSet (B0 B1 D : ℤ) : ℕ → Finset (List ℤ)
  | 0 => initPairs B0 B1
  | m + 1 => (seqSet B0 B1 D m).biUnion fun l =>
      (Finset.Icc (2 * l.headD 0 - l.tail.headD 0 - D) (2 * l.headD 0 - l.tail.headD 0 + D)).image
        fun x => x :: l

lemma card_Icc_le (a b : ℤ) (B : ℕ) (h : b - a ≤ 2 * B) : (Finset.Icc a b).card ≤ 2 * B + 1 := by
  rw [Int.card_Icc]; omega

lemma card_initPairs (B0 B1 : ℕ) : (initPairs B0 B1).card ≤ (2 * B0 + 1) * (2 * B1 + 1) := by
  unfold initPairs
  refine (Finset.card_biUnion_le).trans ?_
  calc _ ≤ ∑ _b0 ∈ Finset.Icc (-(B0 : ℤ)) B0, (2 * B1 + 1) := by
        apply Finset.sum_le_sum; intro b0 _
        exact Finset.card_image_le.trans (card_Icc_le _ _ _ (by omega))
    _ = _ := by
        rw [Finset.sum_const, smul_eq_mul, Int.card_Icc]
        have : ((B0 : ℤ) + 1 - -(B0 : ℤ)).toNat = 2 * B0 + 1 := by omega
        rw [this]

lemma card_seqSet (B0 B1 D : ℕ) (m : ℕ) :
    (seqSet B0 B1 D m).card ≤ (2 * B0 + 1) * (2 * B1 + 1) * (2 * D + 1) ^ m := by
  induction m with
  | zero => simpa [seqSet] using card_initPairs B0 B1
  | succ m ih =>
    simp only [seqSet]
    refine (Finset.card_biUnion_le).trans ?_
    calc _ ≤ ∑ _l ∈ seqSet B0 B1 D m, (2 * D + 1) := by
          apply Finset.sum_le_sum; intro l _
          exact Finset.card_image_le.trans (card_Icc_le _ _ _ (by omega))
      _ = (seqSet B0 B1 D m).card * (2 * D + 1) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (2 * B0 + 1) * (2 * B1 + 1) * (2 * D + 1) ^ m * (2 * D + 1) := by gcongr
      _ = _ := by ring

/-- the reversed list `[b_{m+1}, …, b₀]` of a sequence -/
def revList (b : ℕ → ℤ) : ℕ → List ℤ
  | 0 => [b 1, b 0]
  | m + 1 => b (m + 2) :: revList b m

lemma revList_reverse (b : ℕ → ℤ) (m : ℕ) : (revList b m).reverse = (List.range (m + 2)).map b := by
  induction m with
  | zero => simp [revList, List.range_succ]
  | succ m ih =>
    rw [revList, List.reverse_cons, ih]; simp [List.range_succ]

lemma revList_head (b : ℕ → ℤ) (m : ℕ) : (revList b m).headD 0 = b (m + 1) := by
  cases m <;> rfl

lemma revList_tail_head (b : ℕ → ℤ) (m : ℕ) : (revList b m).tail.headD 0 = b m := by
  cases m with
  | zero => rfl
  | succ m => simp only [revList, List.tail_cons]; exact revList_head b m

lemma revList_mem (b : ℕ → ℤ) (B0 B1 D : ℤ) (h0 : |b 0| ≤ B0) (h1 : |b 1 - b 0| ≤ B1) :
    ∀ m : ℕ, (∀ i, i + 2 ≤ m + 1 → |b (i + 2) - 2 * b (i + 1) + b i| ≤ D) →
      revList b m ∈ seqSet B0 B1 D m := by
  intro m
  induction m with
  | zero =>
    intro _
    rw [abs_le] at h0 h1
    exact Finset.mem_biUnion.mpr ⟨b 0, Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
      Finset.mem_image.mpr ⟨b 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, rfl⟩⟩
  | succ m ih =>
    intro hD
    simp only [revList, seqSet, Finset.mem_biUnion, Finset.mem_image, Finset.mem_Icc]
    refine ⟨revList b m, ih (fun i hi => hD i (by omega)), b (m + 2), ?_, rfl⟩
    have hd := hD m (by omega)
    rw [revList_head, revList_tail_head]; rw [abs_le] at hd; constructor <;> omega

/-! ## Uniform trees depend only on the nodal values in their cell -/

lemma interpAtom_congr {V V' : ℤ → ℚ} {k : ℕ} {n : ℤ} (h0 : V n = V' n) (h1 : V (n + 1) = V' (n + 1)) :
    interpAtom V k n = interpAtom V' k n := by
  unfold interpAtom; simp only [h0, h1]

lemma uniformTree_congr {V V' : ℤ → ℚ} : ∀ (r k : ℕ) (m : ℤ),
    (∀ j : ℤ, 2 ^ r * m ≤ j → j ≤ 2 ^ r * (m + 1) → V j = V' j) →
    uniformTree V r k m = uniformTree V' r k m := by
  intro r
  induction r with
  | zero =>
    intro k m h
    simp only [uniformTree]
    exact congrArg leaf (interpAtom_congr (h m (by simp) (by simp)) (h (m + 1) (by simp) (by simp)))
  | succ r ih =>
    intro k m h
    simp only [uniformTree]
    rw [ih (k + 1) (2 * m) (fun j h1 h2 => h j (by rw [pow_succ]; linarith) (by rw [pow_succ]; linarith)),
      ih (k + 1) (2 * m + 1) (fun j h1 h2 => h j (by rw [pow_succ]; linarith) (by rw [pow_succ]; linarith))]

/-! ## The codebook -/

/-- decoding a reversed numerator list into nodal values `v_j = b_j/(2n²)` -/
noncomputable def decodeVals (r : ℕ) (l : List ℤ) (j : ℤ) : ℚ :=
  ((l.reverse.getD j.toNat 0 : ℤ) : ℚ) / (2 * 2 ^ (2 * r))

/-- the assembly decoded from a numerator list -/
noncomputable def decodeTree (r : ℕ) (l : List ℤ) : LTree := uniformTree (decodeVals r l) r 0 0

/-- numerator bounds -/
noncomputable def cbB0 (R : ℝ) (r : ℕ) : ℕ := ⌈2 * R⌉₊ * 4 ^ r + 1
noncomputable def cbB1 (R M : ℝ) (r : ℕ) : ℕ := ⌈2 * C0 R M⌉₊ * 2 ^ r + 2
noncomputable def cbD (M : ℝ) : ℕ := ⌈2 * M⌉₊ + 4

open Classical in
/-- the codebook `𝒞`: the well-formed assemblies decoded from admissible numerator sequences -/
noncomputable def codebookSet (R M : ℝ) (r : ℕ) : Finset LTree :=
  ((seqSet (cbB0 R r) (cbB1 R M r) (cbD M) (2 ^ r - 1)).image (decodeTree r)).filter (WF 0 0)

lemma codebookSet_WF {R M : ℝ} {r : ℕ} {T : LTree} (h : T ∈ codebookSet R M r) : WF 0 0 T := by
  classical
  unfold codebookSet at h
  exact (Finset.mem_filter.mp h).2

lemma codebookSet_card (R M : ℝ) (r : ℕ) : (codebookSet R M r).card ≤
    (2 * cbB0 R r + 1) * (2 * cbB1 R M r + 1) * (2 * cbD M + 1) ^ (2 ^ r - 1) := by
  classical
  unfold codebookSet
  exact (Finset.card_filter_le _ _).trans (Finset.card_image_le.trans (card_seqSet _ _ _ _))

/-- every `f ∈ 𝓕_{R,M}` is quantized into the codebook -/
lemma codebook_mem {R M : ℝ} {f : ℝ → ℝ} (hf : f ∈ FRM R M) {r : ℕ} (hr : 1 ≤ r) :
    uniformTree (jvals f r) r 0 0 ∈ codebookSet R M r := by
  classical
  have hR := FRM_R_nonneg hf
  have hM := FRM_M_nonneg hf
  have hC0 : 0 ≤ C0 R M := by unfold C0; positivity
  set b : ℕ → ℤ := fun i => bnum f r i
  have hn1 : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  have hn2 : 2 ≤ 2 ^ r := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr
  have hnz : (2 : ℤ) ≤ 2 ^ r := by exact_mod_cast hn2
  -- the numerator list lies in the counted set
  have hmem : revList b (2 ^ r - 1) ∈ seqSet (cbB0 R r) (cbB1 R M r) (cbD M) (2 ^ r - 1) := by
    apply revList_mem
    · -- |b₀| ≤ B₀
      have h := bnum_abs_le (r := r) (j := 0) (hf.2.1 _ (cL_mem01 le_rfl (by positivity)))
      have h' : |(b 0 : ℝ)| ≤ (cbB0 R r : ℝ) := by
        refine h.trans ?_
        simp only [cbB0]; push_cast
        rw [show (2 : ℝ) ^ (2 * r) = 4 ^ r by rw [pow_mul]; norm_num]
        have := Nat.le_ceil (2 * R)
        have : (0 : ℝ) ≤ 4 ^ r := by positivity
        nlinarith
      exact_mod_cast h'
    · -- |b₁ - b₀| ≤ B₁
      have hlip : |f (cL r (0 + 1)) - f (cL r 0)| ≤ C0 R M / 2 ^ r := by
        have := FRM_lipschitz hf (cL_mem01 (r := r) (j := 0) le_rfl (by positivity))
          (cL_mem01 (r := r) (j := 0 + 1) (by omega) (by omega))
        have e : cL r (0 + 1) - cL r 0 = 1 / 2 ^ r := by unfold cL; push_cast; ring
        rw [e, abs_of_pos (a := (1 : ℝ) / 2 ^ r) (by positivity)] at this
        calc _ ≤ C0 R M * (1 / 2 ^ r) := this
          _ = _ := by ring
      have h := bnum_diff_le hlip
      have h' : |(b 1 : ℝ) - b 0| ≤ (cbB1 R M r : ℝ) := by
        simp only [b, zero_add] at h ⊢
        push_cast at h ⊢
        refine h.trans ?_
        simp only [cbB1]; push_cast
        have := Nat.le_ceil (2 * C0 R M)
        have : (0 : ℝ) ≤ 2 ^ r := by positivity
        nlinarith
      exact_mod_cast h'
    · intro i hi
      have h := bnum_second_diff hf r (i := (i : ℤ)) (by positivity) (by
        have : ((i + 2 : ℕ) : ℤ) ≤ ((2 ^ r : ℕ) : ℤ) := by exact_mod_cast (by omega : i + 2 ≤ 2 ^ r)
        push_cast at this; linarith)
      have h' : |(b (i + 2) : ℝ) - 2 * b (i + 1) + b i| ≤ (cbD M : ℝ) := by
        simp only [b]; push_cast
        refine h.trans ?_
        simp only [cbD]; push_cast
        have := Nat.le_ceil (2 * M)
        linarith
      exact_mod_cast h'
  -- the decoded tree is the construction
  have hdec : decodeTree r (revList b (2 ^ r - 1)) = uniformTree (jvals f r) r 0 0 := by
    unfold decodeTree
    apply uniformTree_congr
    intro j h0 h1
    simp only [mul_zero, zero_add, mul_one] at h0 h1
    unfold decodeVals
    rw [revList_reverse]
    have hc : ((2 ^ r : ℕ) : ℤ) = (2 : ℤ) ^ r := by push_cast; rfl
    have hj : j.toNat < 2 ^ r - 1 + 2 := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
    simp only [Option.map_some, Option.getD_some, b, jvals]
    rw [Int.toNat_of_nonneg h0]
  unfold codebookSet
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_image.mpr ⟨_, hmem, hdec⟩, uniformTree_WF _ r 0 0 (jvals_good f r r 0)⟩

/-- `⌈log₂ |𝒞|⌉ ≤ c · n` with `c` depending only on `R, M` -/
lemma codebook_clog (R M : ℝ) : ∃ c : ℕ, ∀ r : ℕ, 1 ≤ r →
    Nat.clog 2 (codebookSet R M r).card ≤ c * 2 ^ r := by
  set a := Nat.clog 2 (2 * ⌈2 * R⌉₊ + 3)
  set a' := Nat.clog 2 (2 * ⌈2 * C0 R M⌉₊ + 5)
  set d := Nat.clog 2 (2 * cbD M + 1)
  refine ⟨a + a' + 3 + d, fun r hr => ?_⟩
  set n := 2 ^ r
  have hrn : r < n := Nat.lt_two_pow_self
  have hn1 : 1 ≤ n := Nat.one_le_two_pow
  have ha := Nat.le_pow_clog (by norm_num : 1 < 2) (2 * ⌈2 * R⌉₊ + 3)
  have ha' := Nat.le_pow_clog (by norm_num : 1 < 2) (2 * ⌈2 * C0 R M⌉₊ + 5)
  have hd := Nat.le_pow_clog (by norm_num : 1 < 2) (2 * cbD M + 1)
  have h4 : 4 ^ r = 2 ^ (2 * r) := by rw [pow_mul]; norm_num
  have hP : (2 * cbB0 R r + 1) * (2 * cbB1 R M r + 1) * (2 * cbD M + 1) ^ (n - 1) ≤
      2 ^ ((a + a' + 3 + d) * n) := by
    have e1 : 2 * cbB0 R r + 1 ≤ 2 ^ a * 2 ^ (2 * r) := by
      simp only [cbB0]; rw [h4]
      have : 1 ≤ 2 ^ (2 * r) := Nat.one_le_two_pow
      nlinarith
    have e2 : 2 * cbB1 R M r + 1 ≤ 2 ^ a' * 2 ^ r := by
      simp only [cbB1]
      have : 1 ≤ 2 ^ r := Nat.one_le_two_pow
      nlinarith
    have e3 : (2 * cbD M + 1) ^ (n - 1) ≤ 2 ^ (d * n) := by
      calc (2 * cbD M + 1) ^ (n - 1) ≤ (2 ^ d) ^ (n - 1) := Nat.pow_le_pow_left hd _
        _ = 2 ^ (d * (n - 1)) := by rw [← pow_mul]
        _ ≤ 2 ^ (d * n) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (by omega))
    calc _ ≤ 2 ^ a * 2 ^ (2 * r) * (2 ^ a' * 2 ^ r) * 2 ^ (d * n) := by gcongr
      _ = 2 ^ (a + 2 * r + (a' + r) + d * n) := by simp only [pow_add]
      _ ≤ 2 ^ ((a + a' + 3 + d) * n) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  calc Nat.clog 2 (codebookSet R M r).card
      ≤ Nat.clog 2 (2 ^ ((a + a' + 3 + d) * n)) :=
        Nat.clog_mono_right 2 ((codebookSet_card R M r).trans hP)
    _ = (a + a' + 3 + d) * n := Nat.clog_pow 2 _ (by norm_num)

end Artigo
