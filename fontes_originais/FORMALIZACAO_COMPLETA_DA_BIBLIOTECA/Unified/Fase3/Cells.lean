module
public import Unified.Fase3.Indexing
public import Unified.Fase3.Heights

/-!
# Section 3: dyadic cells and the generating operator `Γ`
-/

@[expose] public section

namespace Fase3

open Set

/-! ## Cells, ownership and centres (Lemma 3.1) -/

/-- Left endpoint `m 2^{-k}` of the dyadic cell `J_{k,m}`. -/
noncomputable def cellL (k : ℕ) (m : ℤ) : ℝ := m / 2 ^ k

/-- Right endpoint `(m+1) 2^{-k}` of the dyadic cell `J_{k,m}`. -/
noncomputable def cellR (k : ℕ) (m : ℤ) : ℝ := (m + 1) / 2 ^ k

/-- The closed dyadic cell `J_{k,m} = [m2^{-k}, (m+1)2^{-k}]` (equation (09)). -/
def cell (k : ℕ) (m : ℤ) : Set ℝ := Icc (cellL k m) (cellR k m)

/-- The half-open owned cell `J^{own}_{k,m} = [m2^{-k}, (m+1)2^{-k})` (equation (09)). -/
def cellOwn (k : ℕ) (m : ℤ) : Set ℝ := Ico (cellL k m) (cellR k m)

/-- The centre `x₀(k,m) = (m + 1/2) 2^{-k} = (2m+1)/2^{k+1}` (equation (10)). -/
noncomputable def center (k : ℕ) (m : ℤ) : ℝ := (2 * m + 1) / 2 ^ (k + 1)

/-- Dyadic rationals `𝔻 = {j 2^{-K}}`. -/
def dyadic : Set ℝ := {x | ∃ j : ℤ, ∃ K : ℕ, x = j / 2 ^ K}

/-- Non-integer dyadic rationals `𝔻_mid = 𝔻 \ ℤ`. -/
def dyadicMid : Set ℝ := dyadic \ range (Int.cast : ℤ → ℝ)

lemma cellR_sub_cellL (k : ℕ) (m : ℤ) : cellR k m - cellL k m = 1 / 2 ^ k := by
  unfold cellR cellL; ring

lemma cellL_lt_cellR (k : ℕ) (m : ℤ) : cellL k m < cellR k m := by
  have := cellR_sub_cellL k m
  have : (0 : ℝ) < 1 / 2 ^ k := by positivity
  linarith

lemma center_eq (k : ℕ) (m : ℤ) : center k m = (cellL k m + cellR k m) / 2 := by
  unfold center cellL cellR; rw [pow_succ]; field_simp; ring

lemma cellR_eq_cellL_succ (k : ℕ) (m : ℤ) : cellR k m = cellL k (m + 1) := by
  unfold cellR cellL; push_cast; ring

lemma mem_cellOwn_iff (k : ℕ) (m : ℤ) (x : ℝ) : x ∈ cellOwn k m ↔ ⌊2 ^ k * x⌋ = m := by
  unfold cellOwn cellL cellR
  rw [Int.floor_eq_iff, mem_Ico, div_le_iff₀ (by positivity), lt_div_iff₀ (by positivity)]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- **Lemma 3.1 (partition).** For each scale `k`, the owned cells partition `ℝ`. -/
theorem cellOwn_partition (k : ℕ) (x : ℝ) : ∃! m : ℤ, x ∈ cellOwn k m :=
  ⟨⌊2 ^ k * x⌋, (mem_cellOwn_iff _ _ _).2 rfl, fun _ hm => ((mem_cellOwn_iff _ _ _).1 hm).symm⟩

/-- **Lemma 3.1 (refinement).** `J_{k,m} = J_{k+1,2m} ∪ J_{k+1,2m+1}`. -/
theorem cell_refine (k : ℕ) (m : ℤ) :
    cell k m = cell (k + 1) (2 * m) ∪ cell (k + 1) (2 * m + 1) := by
  have e1 : cellL (k + 1) (2 * m) = cellL k m := by
    unfold cellL; rw [pow_succ]; push_cast; field_simp
  have e2 : cellR (k + 1) (2 * m) = cellL (k + 1) (2 * m + 1) := by
    unfold cellR cellL; push_cast; ring
  have e3 : cellR (k + 1) (2 * m + 1) = cellR k m := by
    unfold cellR; rw [pow_succ]; push_cast; field_simp; ring
  unfold cell
  rw [e1, e2, e3, Icc_union_Icc_eq_Icc]
  · rw [← e2, ← e1]; exact (cellL_lt_cellR _ _).le
  · rw [← e3]; exact (cellL_lt_cellR _ _).le

/-- **Lemma 3.1 (length).** `|J_{k,m}| = 2^{-k}`. -/
theorem cell_length (k : ℕ) (m : ℤ) : cellR k m - cellL k m = (2 : ℝ) ^ (-(k : ℤ)) := by
  rw [cellR_sub_cellL, zpow_neg, zpow_natCast, one_div]

lemma center_mem_dyadicMid (k : ℕ) (m : ℤ) : center k m ∈ dyadicMid := by
  refine ⟨⟨2 * m + 1, k + 1, by unfold center; push_cast; ring⟩, ?_⟩
  rintro ⟨n, hn⟩
  unfold center at hn
  rw [eq_div_iff (by positivity)] at hn
  have : (n * 2 ^ (k + 1) : ℤ) = 2 * m + 1 := by exact_mod_cast hn
  have h2 : (2 : ℤ) ∣ n * 2 ^ (k + 1) := Dvd.dvd.mul_left (dvd_pow_self 2 (by omega)) n
  rw [this] at h2
  omega

lemma dyadicMid_subset_range_center :
    dyadicMid ⊆ range (fun p : ℕ × ℤ => center p.1 p.2) := by
  rintro x ⟨⟨j, K, rfl⟩, hnot⟩
  induction K generalizing j with
  | zero => exact absurd ⟨j, by simp⟩ hnot
  | succ K ih =>
    rcases Int.emod_two_eq_zero_or_one j with h | h
    · obtain ⟨i, rfl⟩ : (2 : ℤ) ∣ j := Int.dvd_of_emod_eq_zero h
      have : ((2 * i : ℤ) : ℝ) / 2 ^ (K + 1) = (i : ℝ) / 2 ^ K := by
        push_cast; rw [pow_succ]; field_simp
      rw [this] at hnot ⊢
      exact ih i hnot
    · refine ⟨(K, (j - 1) / 2), ?_⟩
      have hj : j = 2 * ((j - 1) / 2) + 1 := by omega
      simp only [center]
      conv_rhs => rw [hj]
      push_cast; ring

lemma center_injective : Function.Injective (fun p : ℕ × ℤ => center p.1 p.2) := by
  rintro ⟨k, m⟩ ⟨k', m'⟩ h
  simp only [center] at h
  rw [div_eq_div_iff (by positivity) (by positivity)] at h
  have hz : (2 * m + 1) * 2 ^ (k' + 1) = (2 * m' + 1) * (2 ^ (k + 1) : ℤ) := by exact_mod_cast h
  have hk : k = k' := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
      have : (2 * m + 1) * 2 ^ (d + 1) = (2 * m' + 1) := by
        have h' : ((2 * m + 1) * 2 ^ (d + 1)) * 2 ^ (k + 1) = (2 * m' + 1) * 2 ^ (k + 1) := by
          rw [← hz]; ring
        exact mul_right_cancel₀ (by positivity) h'
      have h2 : (2 : ℤ) ∣ (2 * m + 1) * 2 ^ (d + 1) := Dvd.dvd.mul_left (dvd_pow_self 2 (by omega)) _
      rw [this] at h2; omega
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
      have : (2 * m' + 1) * 2 ^ (d + 1) = (2 * m + 1) := by
        have h' : ((2 * m' + 1) * 2 ^ (d + 1)) * 2 ^ (k' + 1) = (2 * m + 1) * 2 ^ (k' + 1) := by
          rw [hz]; ring
        exact mul_right_cancel₀ (by positivity) h'
      have h2 : (2 : ℤ) ∣ (2 * m' + 1) * 2 ^ (d + 1) := Dvd.dvd.mul_left (dvd_pow_self 2 (by omega)) _
      rw [this] at h2; omega
  subst hk
  have : 2 * m + 1 = 2 * m' + 1 := mul_right_cancel₀ (by positivity) hz
  simp only [Prod.mk.injEq, true_and]; omega

/-- **Lemma 3.1 (centres).** `(k,m) ↦ x₀(k,m)` is a bijection of `ℕ × ℤ` onto `𝔻_mid`. -/
theorem center_bijOn : Function.Injective (fun p : ℕ × ℤ => center p.1 p.2) ∧
    range (fun p : ℕ × ℤ => center p.1 p.2) = dyadicMid :=
  ⟨center_injective, Subset.antisymm (by rintro _ ⟨p, rfl⟩; exact center_mem_dyadicMid _ _)
    dyadicMid_subset_range_center⟩

/-- **Lemma 3.1 (density).** `𝔻_mid` is dense in `ℝ`. -/
theorem dyadicMid_dense : Dense dyadicMid := by
  rw [Metric.dense_iff]
  intro x ε hε
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨center k ⌊2 ^ k * x⌋, ?_, center_mem_dyadicMid _ _⟩
  have hx := (mem_cellOwn_iff k ⌊2 ^ k * x⌋ x).2 rfl
  unfold cellOwn at hx
  rw [Metric.mem_ball, Real.dist_eq, center_eq]
  have hl := cellR_sub_cellL k ⌊2 ^ k * x⌋
  rw [one_div_pow] at hk
  rw [abs_lt]; constructor <;> linarith [hx.1, hx.2]

/-! ## Unpacking addresses (Lemma 3.2) -/

/-- The unpacking `n ↦ (k, μ, r, t)` of equation (13). -/
def decode4 (n : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  ((cunpair (cunpair n).1).1, (cunpair (cunpair n).1).2,
    (cunpair (cunpair n).2).1, (cunpair (cunpair n).2).2)

/-- The explicit inverse `(k,μ,r,t) ↦ π(π(k,μ), π(r,t))`. -/
def encode4 (p : ℕ × ℕ × ℕ × ℕ) : ℕ := cpair (cpair p.1 p.2.1) (cpair p.2.2.1 p.2.2.2)

lemma decode4_encode4 (p : ℕ × ℕ × ℕ × ℕ) : decode4 (encode4 p) = p := by
  simp [decode4, encode4, cunpair_cpair]

lemma encode4_decode4 (n : ℕ) : encode4 (decode4 n) = n := by
  simp [decode4, encode4, cpair_cunpair]

/-- **Lemma 3.2.** `n ↦ (k, μ, r, t)` is a bijection of `ℕ` onto `ℕ⁴`. -/
theorem decode4_bijective : Function.Bijective decode4 :=
  ⟨Function.LeftInverse.injective encode4_decode4,
    Function.RightInverse.surjective decode4_encode4⟩

/-! ## Anchored lines and the generator (equations (12)–(18), Definition 3.3) -/

/-- Scale `k(n)`. -/
def gK (n : ℕ) : ℕ := (decode4 n).1
/-- Cell index `m(n) = Z(μ)`. -/
def gM (n : ℕ) : ℤ := zEnum (decode4 n).2.1
/-- Anchor `x_{0,n} = x₀(k,m)`. -/
noncomputable def x0 (n : ℕ) : ℝ := center (gK n) (gM n)
/-- Anchored value `y_{0,n} = Q(r)`. -/
noncomputable def y0 (n : ℕ) : ℚ := Qenum (decode4 n).2.2.1
/-- Slope `s_n = Q*(t)`. -/
noncomputable def slope (n : ℕ) : ℚ := (QstarEnum (decode4 n).2.2.2).1

lemma slope_ne_zero (n : ℕ) : slope n ≠ 0 := (QstarEnum (decode4 n).2.2.2).2

/-- Global slope `b_n = s_n` (equation (15)). -/
noncomputable def coefB (n : ℕ) : ℝ := slope n
/-- Global intercept `a_n = y_{0,n} - s_n x_{0,n}` (equation (15)). -/
noncomputable def coefA (n : ℕ) : ℝ := y0 n - slope n * x0 n
/-- The line `ℓ_n(x) = a_n + b_n x` (equation (12)). -/
noncomputable def atomLine (n : ℕ) (x : ℝ) : ℝ := coefA n + coefB n * x

lemma atomLine_eq (n : ℕ) (x : ℝ) : atomLine n x = y0 n + slope n * (x - x0 n) := by
  unfold atomLine coefA coefB; ring

lemma coefB_ne_zero (n : ℕ) : coefB n ≠ 0 := by
  unfold coefB; exact_mod_cast slope_ne_zero n

/-- `x_L = m 2^{-k}` for the cell of `n`. -/
noncomputable def xL (n : ℕ) : ℝ := cellL (gK n) (gM n)
/-- `x_R = (m+1) 2^{-k}` for the cell of `n`. -/
noncomputable def xR (n : ℕ) : ℝ := cellR (gK n) (gM n)
/-- `c_n = min(ℓ_n(x_L), ℓ_n(x_R))` (equation (16)). -/
noncomputable def cLo (n : ℕ) : ℝ := min (atomLine n (xL n)) (atomLine n (xR n))
/-- `d_n = max(ℓ_n(x_L), ℓ_n(x_R))` (equation (16)). -/
noncomputable def dHi (n : ℕ) : ℝ := max (atomLine n (xL n)) (atomLine n (xR n))

/-- **Definition 3.3.** The generator `Γ(n) = (a_n, b_n, [c_n, d_n])` (equation (17));
the interval is represented by the pair of its endpoints. -/
noncomputable def gen (n : ℕ) : ℝ × ℝ × ℝ × ℝ := (coefA n, coefB n, cLo n, dHi n)

/-- The library `𝓛 = Γ(ℕ)`. -/
def library : Set (ℝ × ℝ × ℝ × ℝ) := range gen

/-- The interval `[c_n, d_n]` is non-degenerate. -/
theorem cLo_lt_dHi (n : ℕ) : cLo n < dHi n := by
  unfold cLo dHi
  rw [min_lt_max]
  intro h
  unfold atomLine at h
  have h2 : coefB n * (xL n - xR n) = 0 := by linarith
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact coefB_ne_zero n h3
  · have := cellL_lt_cellR (gK n) (gM n); unfold xL xR at h3; linarith

/-- The spatial preimage `I_n^x` of equation (18). -/
noncomputable def preimageInterval (n : ℕ) : Set ℝ :=
  Icc (min ((cLo n - coefA n) / coefB n) ((dHi n - coefA n) / coefB n))
    (max ((cLo n - coefA n) / coefB n) ((dHi n - coefA n) / coefB n))

lemma inv_line (n : ℕ) (x : ℝ) : (atomLine n x - coefA n) / coefB n = x := by
  unfold atomLine; field_simp [coefB_ne_zero n]; ring

/-- **Lemma 3.4 (exact spatial validity).** `I_n^x = J_{k(n), m(n)}`. -/
theorem preimageInterval_eq (n : ℕ) : preimageInterval n = cell (gK n) (gM n) := by
  have hlt := cellL_lt_cellR (gK n) (gM n)
  have key : min ((cLo n - coefA n) / coefB n) ((dHi n - coefA n) / coefB n) = xL n ∧
      max ((cLo n - coefA n) / coefB n) ((dHi n - coefA n) / coefB n) = xR n := by
    unfold cLo dHi
    unfold xL xR at *
    rcases le_total (atomLine n (cellL (gK n) (gM n))) (atomLine n (cellR (gK n) (gM n))) with h | h
    · rw [min_eq_left h, max_eq_right h, inv_line, inv_line]
      exact ⟨min_eq_left hlt.le, max_eq_right hlt.le⟩
    · rw [min_eq_right h, max_eq_left h, inv_line, inv_line]
      exact ⟨min_eq_right hlt.le, max_eq_left hlt.le⟩
  unfold preimageInterval cell
  rw [key.1, key.2]; rfl

lemma cell_index_ext {k k' : ℕ} {m m' : ℤ} (hL : cellL k m = cellL k' m')
    (hR : cellR k m = cellR k' m') : k = k' ∧ m = m' := by
  have h1 : (1 : ℝ) / 2 ^ k = 1 / 2 ^ k' := by
    rw [← cellR_sub_cellL, ← cellR_sub_cellL, hL, hR]
  have h2 : (2 : ℝ) ^ k = 2 ^ k' := by
    have := congrArg (fun t : ℝ => 1 / t) h1
    simpa using this
  have hk : k = k' := Nat.pow_right_injective (le_refl 2) (by exact_mod_cast h2)
  subst hk
  refine ⟨rfl, ?_⟩
  unfold cellL at hL
  have : (m : ℝ) = m' := by
    have := congrArg (fun t => t * 2 ^ k) hL
    simpa [div_mul_cancel₀, ne_of_gt (by positivity : (0 : ℝ) < 2 ^ k)] using this
  exact_mod_cast this

/-! ## Rational-jet dictionary (Theorem 3.6) and address uniqueness (Theorem 3.5) -/

/-- The jet map `n ↦ (x_{0,n}, y_{0,n}, s_n)` of equation (19). -/
noncomputable def jet (n : ℕ) : ℝ × ℚ × ℚ := (x0 n, y0 n, slope n)

lemma jet_injective : Function.Injective jet := by
  intro n n' h
  simp only [jet, Prod.mk.injEq] at h
  obtain ⟨hx, hy, hs⟩ := h
  have hc := center_injective (a₁ := (gK n, gM n)) (a₂ := (gK n', gM n')) hx
  simp only [Prod.mk.injEq] at hc
  obtain ⟨hk, hm⟩ := hc
  have hmu := zEnum_bijective.1 hm
  have hr := Qenum_bijective.1 hy
  have ht := QstarEnum_bijective.1 (Subtype.ext hs)
  apply decode4_bijective.1
  exact Prod.ext hk (Prod.ext hmu (Prod.ext hr ht))

lemma exists_jet (k : ℕ) (m : ℤ) (y s : ℚ) (hs : s ≠ 0) :
    ∃ n, gK n = k ∧ gM n = m ∧ y0 n = y ∧ slope n = s := by
  refine ⟨encode4 (k, zInv m, rankQ y, rankQstar ⟨s, hs⟩), ?_, ?_, ?_, ?_⟩ <;>
    simp [gK, gM, y0, slope, decode4_encode4, zEnum_zInv, Qenum_rankQ, QstarEnum_rankQstar]

/-- **Theorem 3.6 (rational-jet dictionary), bijectivity.** The jet map is a bijection of `ℕ`
onto `𝔻_mid × ℚ × ℚ*`. -/
theorem jet_bijective : Function.Injective jet ∧
    range jet = {p : ℝ × ℚ × ℚ | p.1 ∈ dyadicMid ∧ p.2.2 ≠ 0} := by
  refine ⟨jet_injective, Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact ⟨center_mem_dyadicMid _ _, slope_ne_zero n⟩
  · rintro ⟨x, y, s⟩ ⟨hx, hs⟩
    obtain ⟨⟨k, m⟩, rfl⟩ := dyadicMid_subset_range_center hx
    obtain ⟨n, hk, hm, hy, hs'⟩ := exists_jet k m y s hs
    exact ⟨n, by simp [jet, x0, hk, hm, hy, hs']⟩

/-- **Theorem 3.6 (density).** The image of the jet map is dense in `ℝ³`. -/
theorem jet_dense : Dense (range fun n => (x0 n, ((y0 n : ℚ) : ℝ), ((slope n : ℚ) : ℝ))) := by
  have hr : range (fun n => (x0 n, ((y0 n : ℚ) : ℝ), ((slope n : ℚ) : ℝ))) =
      dyadicMid ×ˢ (range (Rat.cast : ℚ → ℝ) ×ˢ (range (Rat.cast : ℚ → ℝ) \ {0})) := by
    ext ⟨x, y, s⟩
    simp only [mem_range, mem_prod, mem_diff, mem_singleton_iff, Prod.mk.injEq]
    constructor
    · rintro ⟨n, rfl, rfl, rfl⟩
      exact ⟨center_mem_dyadicMid _ _, ⟨_, rfl⟩, ⟨_, rfl⟩, by exact_mod_cast slope_ne_zero n⟩
    · rintro ⟨hx, ⟨y', rfl⟩, ⟨s', rfl⟩, hs⟩
      obtain ⟨⟨k, m⟩, rfl⟩ := dyadicMid_subset_range_center hx
      have hs' : s' ≠ 0 := by intro h; apply hs; simp [h]
      obtain ⟨n, hk, hm, hy, hsn⟩ := exists_jet k m y' s' hs'
      exact ⟨n, by simp [x0, hk, hm], by rw [hy], by rw [hsn]⟩
  rw [hr]
  exact dyadicMid_dense.prod (Rat.denseRange_cast.prod (Rat.denseRange_cast.diff_singleton 0))

/-- **Theorem 3.5 (address uniqueness).** `Γ` is injective, hence a bijection onto `𝓛`. -/
theorem gen_injective : Function.Injective gen := by
  intro n n' h
  simp only [gen, Prod.mk.injEq] at h
  obtain ⟨ha, hb, hc, hd⟩ := h
  have hI : preimageInterval n = preimageInterval n' := by
    unfold preimageInterval; rw [ha, hb, hc, hd]
  rw [preimageInterval_eq, preimageInterval_eq] at hI
  unfold cell at hI
  rw [Icc_eq_Icc_iff (cellL_lt_cellR _ _).le] at hI
  obtain ⟨hk, hm⟩ := cell_index_ext hI.1 hI.2
  apply jet_injective
  have hx : x0 n = x0 n' := by unfold x0; rw [hk, hm]
  have hs : slope n = slope n' := by unfold coefB at hb; exact_mod_cast hb
  have hy : y0 n = y0 n' := by
    unfold coefA at ha
    rw [hx, hs] at ha
    have : (y0 n : ℝ) = y0 n' := by linarith
    exact_mod_cast this
  simp [jet, hx, hy, hs]

/-- Existence of the atom with prescribed cell, centre value and nonzero rational slope
(the content of Theorem 3.6 used to build assemblies). -/
theorem exists_atom (k : ℕ) (m : ℤ) (y s : ℚ) (hs : s ≠ 0) :
    ∃ n, gK n = k ∧ gM n = m ∧ ∀ x, atomLine n x = y + s * (x - center k m) := by
  obtain ⟨n, hk, hm, hy, hsn⟩ := exists_jet k m y s hs
  exact ⟨n, hk, hm, fun x => by rw [atomLine_eq, hy, hsn, x0, hk, hm]⟩

end Fase3
