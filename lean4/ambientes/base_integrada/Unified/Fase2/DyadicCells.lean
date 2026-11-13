module

public import Unified.Fase2.Pairing
public import Unified.Fase2.HeightEnum

/-!
# Section 3: dyadic cells and the generating operator `Γ`

Formalization of Lemma 3.1 (dyadic structure), Lemma 3.2 (unpacking), Definition 3.3
(generator and library), Lemma 3.4 (exact spatial validity), Theorem 3.5 (uniqueness of the
address) and Theorem 3.6 (dictionary of rational jets).
-/

@[expose] public section

namespace Dyadic2

open Set Function

/-! ### Cells, ownership and centers, Equations (09)–(10) -/

/-- The closed dyadic cell `J_{k,m} = [m 2^{-k}, (m+1) 2^{-k}]`, Equation (09). -/
noncomputable def cellJ (k : ℕ) (m : ℤ) : Set ℝ := Icc ((m : ℝ) / 2 ^ k) (((m : ℝ) + 1) / 2 ^ k)

/-- The owned (half-open) dyadic cell `J^{own}_{k,m} = [m 2^{-k}, (m+1) 2^{-k})`. -/
noncomputable def cellOwn (k : ℕ) (m : ℤ) : Set ℝ :=
  Ico ((m : ℝ) / 2 ^ k) (((m : ℝ) + 1) / 2 ^ k)

/-- The center `x₀(k,m) = (m + 1/2) 2^{-k}`, Equation (10). -/
noncomputable def center (k : ℕ) (m : ℤ) : ℝ := ((m : ℝ) + 1 / 2) / 2 ^ k

/-- The dyadic rationals `𝔻 = {j 2^{-K}}`. -/
def Dset : Set ℝ := {x | ∃ j : ℤ, ∃ K : ℕ, x = (j : ℝ) / 2 ^ K}

/-- `𝔻_mid = 𝔻 \ ℤ`. -/
def Dmid : Set ℝ := Dset \ range ((↑) : ℤ → ℝ)

/-- Equation (10), second form: `x₀(k,m) = (2m+1)/2^{k+1}`. -/
lemma center_eq (k : ℕ) (m : ℤ) : center k m = (2 * (m : ℝ) + 1) / 2 ^ (k + 1) := by
  unfold center; rw [pow_succ]; field_simp

/-- **Lemma 3.1 (partition).** For each `k`, the owned cells partition `ℝ`. -/
theorem cellOwn_partition (k : ℕ) (x : ℝ) : ∃! m : ℤ, x ∈ cellOwn k m := by
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  have key : ∀ m : ℤ, x ∈ cellOwn k m ↔ ⌊2 ^ k * x⌋ = m := by
    intro m
    rw [Int.floor_eq_iff, cellOwn, mem_Ico, div_le_iff₀ hp, lt_div_iff₀ hp]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  exact ⟨⌊2 ^ k * x⌋, (key _).2 rfl, fun m hm => ((key m).1 hm).symm⟩

/-- **Lemma 3.1 (refinement), Equation (11).** `J_{k,m} = J_{k+1,2m} ∪ J_{k+1,2m+1}`. -/
theorem cellJ_refine (k : ℕ) (m : ℤ) :
    cellJ k m = cellJ (k + 1) (2 * m) ∪ cellJ (k + 1) (2 * m + 1) := by
  unfold cellJ
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  have e1 : (((2 * m : ℤ) : ℝ)) / 2 ^ (k + 1) = (m : ℝ) / 2 ^ k := by
    push_cast; rw [pow_succ]; field_simp
  have e2 : (((2 * m : ℤ) : ℝ) + 1) / 2 ^ (k + 1) = (((2 * m + 1 : ℤ) : ℝ)) / 2 ^ (k + 1) := by
    push_cast; ring
  have e3 : (((2 * m + 1 : ℤ) : ℝ) + 1) / 2 ^ (k + 1) = ((m : ℝ) + 1) / 2 ^ k := by
    push_cast; rw [pow_succ]; field_simp; ring
  rw [e1, e2, e3, Set.Icc_union_Icc_eq_Icc]
  · rw [← e1]; gcongr; linarith
  · rw [← e3]; gcongr; push_cast; linarith

/-- **Lemma 3.1 (length), Equation (11).** `|J_{k,m}| = 2^{-k}`. -/
theorem cellJ_volume (k : ℕ) (m : ℤ) :
    MeasureTheory.volume (cellJ k m) = ENNReal.ofReal ((2 : ℝ) ^ (-(k : ℤ))) := by
  rw [cellJ, Real.volume_Icc]
  congr 1
  rw [zpow_neg, zpow_natCast]
  field_simp
  ring

lemma center_mem_cellJ (k : ℕ) (m : ℤ) : center k m ∈ cellJ k m := by
  unfold center cellJ
  constructor <;> gcongr <;> linarith

lemma center_mem_Dmid (k : ℕ) (m : ℤ) : center k m ∈ Dmid := by
  refine ⟨⟨2 * m + 1, k + 1, by rw [center_eq]; push_cast; ring⟩, ?_⟩
  rintro ⟨n, hn⟩
  rw [center_eq, eq_div_iff (by positivity)] at hn
  have : (n : ℤ) * 2 ^ (k + 1) = 2 * m + 1 := by exact_mod_cast hn
  have hev : Even ((n : ℤ) * 2 ^ (k + 1)) := ⟨n * 2 ^ k, by rw [pow_succ]; ring⟩
  rw [this] at hev
  exact Int.not_even_iff_odd.2 ⟨m, rfl⟩ hev

lemma center_injective : Injective (fun p : ℕ × ℤ => center p.1 p.2) := by
  rintro ⟨k, m⟩ ⟨k', m'⟩ h
  simp only [center_eq] at h
  rw [div_eq_div_iff (by positivity) (by positivity)] at h
  have hz : (2 * m + 1) * (2 : ℤ) ^ (k' + 1) = (2 * m' + 1) * 2 ^ (k + 1) := by
    exact_mod_cast h
  have par : ∀ (a b : ℤ) (i d : ℕ), (2 * a + 1) * 2 ^ (i + d + 1 + 1) ≠
      (2 * b + 1) * 2 ^ (i + 1) := by
    intro a b i d habs
    have e : (2 * a + 1) * 2 ^ (i + d + 1 + 1) = ((2 * a + 1) * 2 ^ (d + 1)) * 2 ^ (i + 1) := by
      ring
    rw [e] at habs
    have := mul_right_cancel₀ (by positivity) habs
    have hev : Even ((2 * a + 1) * (2 : ℤ) ^ (d + 1)) := ⟨(2 * a + 1) * 2 ^ d, by ring⟩
    rw [this] at hev
    exact Int.not_even_iff_odd.2 ⟨b, rfl⟩ hev
  rcases lt_trichotomy k k' with hk | hk | hk
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hk
    exact absurd hz (par m m' k d)
  · subst hk
    have := mul_right_cancel₀ (by positivity) hz
    simp only [Prod.mk.injEq, true_and]
    omega
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hk
    exact absurd hz.symm (par m' m k' d)

lemma Dmid_subset_range_center : Dmid ⊆ range (fun p : ℕ × ℤ => center p.1 p.2) := by
  rintro x ⟨⟨j, K, rfl⟩, hnot⟩
  induction K generalizing j with
  | zero => exact absurd ⟨j, by simp⟩ hnot
  | succ K ih =>
    obtain ⟨i, hi | hi⟩ := Int.even_or_odd' j
    · subst hi
      have e : ((2 * i : ℤ) : ℝ) / 2 ^ (K + 1) = (i : ℝ) / 2 ^ K := by
        push_cast; rw [pow_succ]; field_simp
      rw [e] at hnot ⊢
      exact ih i hnot
    · subst hi
      exact ⟨(K, i), by simp only [center_eq]; push_cast; ring⟩

/-- **Lemma 3.1 (centers).** `(k,m) ↦ x₀(k,m)` is a bijection of `ℕ₀ × ℤ` onto `𝔻_mid`. -/
theorem center_bijOn : BijOn (fun p : ℕ × ℤ => center p.1 p.2) univ Dmid :=
  ⟨fun p _ => center_mem_Dmid p.1 p.2, center_injective.injOn,
    fun x hx => by obtain ⟨p, hp⟩ := Dmid_subset_range_center hx; exact ⟨p, trivial, hp⟩⟩

lemma range_center : range (fun p : ℕ × ℤ => center p.1 p.2) = Dmid := by
  rw [← image_univ]; exact center_bijOn.image_eq

/-- **Lemma 3.1 (density).** `𝔻_mid` is dense in `ℝ`. -/
theorem Dmid_dense : Dense Dmid := by
  rw [dense_iff_exists_between]
  intro a b hab
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (2 / (b - a)) (by norm_num : (1 : ℝ) < 2)
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  have hk' : 2 < (b - a) * 2 ^ k := by
    rw [div_lt_iff₀ (by linarith)] at hk; linarith
  set m := ⌊2 ^ k * a⌋ + 1 with hm
  have h1 : 2 ^ k * a < (m : ℝ) := by rw [hm]; push_cast; exact Int.lt_floor_add_one _
  have h2 : (m : ℝ) ≤ 2 ^ k * a + 1 := by rw [hm]; push_cast; linarith [Int.floor_le (2 ^ k * a)]
  refine ⟨center k m, center_mem_Dmid k m, ?_, ?_⟩
  · unfold center; rw [lt_div_iff₀ hp]; linarith
  · unfold center; rw [div_lt_iff₀ hp]; nlinarith

/-! ### Anchored lines and unpacking, Equations (12)–(13) -/

/-- Equation (13): `n ↦ (k, μ, r, t)` via three applications of `π⁻¹`. -/
def unpack (n : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  ((cunpair (cunpair n).1).1, (cunpair (cunpair n).1).2,
    (cunpair (cunpair n).2).1, (cunpair (cunpair n).2).2)

/-- The explicit inverse `(k, μ, r, t) ↦ π(π(k,μ), π(r,t))`. -/
def pack (q : ℕ × ℕ × ℕ × ℕ) : ℕ := cpair (cpair q.1 q.2.1) (cpair q.2.2.1 q.2.2.2)

lemma unpack_pack (q : ℕ × ℕ × ℕ × ℕ) : unpack (pack q) = q := by
  simp [unpack, pack, cunpair_cpair]

lemma pack_unpack (n : ℕ) : pack (unpack n) = n := by
  simp [unpack, pack, cpair_cunpair]

/-- **Lemma 3.2.** `n ↦ (k, μ, r, t)` is a bijection of `ℕ₀` onto `ℕ₀⁴`. -/
theorem unpack_bijective : Bijective unpack :=
  ⟨LeftInverse.injective pack_unpack, RightInverse.surjective unpack_pack⟩

/-! ### The data of address `n`, Equations (14)–(16) -/

/-- The scale `k(n)`. -/
def scale (n : ℕ) : ℕ := (unpack n).1

/-- The cell index `m(n) = Z(μ)`. -/
def cellIdx (n : ℕ) : ℤ := Zenum (unpack n).2.1

/-- The anchor `x_{0,n} = x₀(k,m)`. -/
noncomputable def x0n (n : ℕ) : ℝ := center (scale n) (cellIdx n)

/-- The anchored value `y_{0,n} = Q(r)`. -/
noncomputable def y0n (n : ℕ) : ℚ := Qenum (unpack n).2.2.1

/-- The slope `s_n = Q*(t)`. -/
noncomputable def sn (n : ℕ) : ℚ := (Qstar (unpack n).2.2.2).1

lemma sn_ne_zero (n : ℕ) : sn n ≠ 0 := (Qstar (unpack n).2.2.2).2

/-- Equation (15): `b_n = s_n`. -/
noncomputable def bn (n : ℕ) : ℝ := sn n

/-- Equation (15): `a_n = y_{0,n} - s_n x_{0,n}`. -/
noncomputable def an (n : ℕ) : ℝ := (y0n n : ℝ) - sn n * x0n n

/-- The line `ℓ_n(x) = a_n + b_n x`, Equation (12). -/
noncomputable def line (n : ℕ) (x : ℝ) : ℝ := an n + bn n * x

lemma line_eq_anchored (n : ℕ) (x : ℝ) : line n x = y0n n + sn n * (x - x0n n) := by
  unfold line an bn; ring

lemma bn_ne_zero (n : ℕ) : bn n ≠ 0 := by unfold bn; exact_mod_cast sn_ne_zero n

/-- Left end `x_L = m 2^{-k}` of the cell of address `n`. -/
noncomputable def xL (n : ℕ) : ℝ := (cellIdx n : ℝ) / 2 ^ scale n

/-- Right end `x_R = (m+1) 2^{-k}` of the cell of address `n`. -/
noncomputable def xR (n : ℕ) : ℝ := ((cellIdx n : ℝ) + 1) / 2 ^ scale n

/-- Equation (16): `c_n = min{ℓ_n(x_L), ℓ_n(x_R)}`. -/
noncomputable def cn (n : ℕ) : ℝ := min (line n (xL n)) (line n (xR n))

/-- Equation (16): `d_n = max{ℓ_n(x_L), ℓ_n(x_R)}`. -/
noncomputable def dn (n : ℕ) : ℝ := max (line n (xL n)) (line n (xR n))

lemma xL_lt_xR (n : ℕ) : xL n < xR n := by
  unfold xL xR; gcongr; linarith

lemma cellJ_eq (n : ℕ) : cellJ (scale n) (cellIdx n) = Icc (xL n) (xR n) := rfl

/-- The interval `[c_n, d_n]` is non-degenerate. -/
lemma cn_lt_dn (n : ℕ) : cn n < dn n := by
  unfold cn dn
  have h := xL_lt_xR n
  have hb := bn_ne_zero n
  have : line n (xL n) ≠ line n (xR n) := by
    unfold line; intro he
    exact hb (by
      have : bn n * (xR n - xL n) = 0 := by linarith
      rcases mul_eq_zero.1 this with h' | h'
      · exact h'
      · exact absurd h' (by linarith))
  rcases lt_or_gt_of_ne this with h' | h'
  · rw [min_eq_left h'.le, max_eq_right h'.le]; exact h'
  · rw [min_eq_right h'.le, max_eq_left h'.le]; exact h'

/-- **Definition 3.3 (generator), Equation (17).**
`Γ(n) = (a_n, b_n, [c_n, d_n])`. -/
noncomputable def Gamma (n : ℕ) : ℝ × ℝ × Set ℝ := (an n, bn n, Icc (cn n) (dn n))

/-- **Definition 3.3 (library).** `𝓛 = Γ(ℕ₀)`. -/
def Library : Set (ℝ × ℝ × Set ℝ) := range Gamma

/-- Every element of the library has nonzero slope and a non-degenerate closed interval. -/
theorem Gamma_wellformed (n : ℕ) :
    (Gamma n).2.1 ≠ 0 ∧ ∃ c d : ℝ, c < d ∧ (Gamma n).2.2 = Icc c d :=
  ⟨bn_ne_zero n, cn n, dn n, cn_lt_dn n, rfl⟩

/-- The spatial pre-image of a triple `(a, b, [c, d])`, Equation (18). -/
noncomputable def preimageX (a b c d : ℝ) : Set ℝ :=
  Icc (min ((c - a) / b) ((d - a) / b)) (max ((c - a) / b) ((d - a) / b))

/-- `I_n^x`, Equation (18). -/
noncomputable def Ix (n : ℕ) : Set ℝ := preimageX (an n) (bn n) (cn n) (dn n)

/-- **Lemma 3.4 (exact spatial validity).** `I_n^x = J_{k(n), m(n)}`. -/
theorem Ix_eq_cellJ (n : ℕ) : Ix n = cellJ (scale n) (cellIdx n) := by
  rw [cellJ_eq, Ix, preimageX]
  have hb := bn_ne_zero n
  have hlt := xL_lt_xR n
  have inv : ∀ x, (line n x - an n) / bn n = x := by
    intro x; unfold line; field_simp; ring
  rcases lt_or_gt_of_ne hb with hneg | hpos
  · have hle : line n (xR n) ≤ line n (xL n) := by unfold line; nlinarith
    rw [cn, dn, min_eq_right hle, max_eq_left hle, inv, inv,
      min_eq_right hlt.le, max_eq_left hlt.le]
  · have hle : line n (xL n) ≤ line n (xR n) := by unfold line; nlinarith
    rw [cn, dn, min_eq_left hle, max_eq_right hle, inv, inv,
      min_eq_left hlt.le, max_eq_right hlt.le]

lemma cellJ_inj {k k' : ℕ} {m m' : ℤ} (h : cellJ k m = cellJ k' m') : k = k' ∧ m = m' := by
  unfold cellJ at h
  rw [Set.Icc_eq_Icc_iff (by gcongr; linarith)] at h
  obtain ⟨h1, h2⟩ := h
  have hlen : (1 : ℝ) / 2 ^ k = 1 / 2 ^ k' := by
    have e1 : (1 : ℝ) / 2 ^ k = ((m : ℝ) + 1) / 2 ^ k - (m : ℝ) / 2 ^ k := by ring
    have e2 : (1 : ℝ) / 2 ^ k' = ((m' : ℝ) + 1) / 2 ^ k' - (m' : ℝ) / 2 ^ k' := by ring
    rw [e1, e2, h1, h2]
  have hk : k = k' := by
    have : (2 : ℝ) ^ k = 2 ^ k' := by
      have := congrArg (fun x : ℝ => 1 / x) hlen; simpa using this
    exact Nat.pow_right_injective (le_refl 2) (by exact_mod_cast this)
  subst hk
  refine ⟨rfl, ?_⟩
  have : (m : ℝ) = m' := by
    have := congrArg (fun x : ℝ => x * 2 ^ k) h1
    simpa [div_mul_cancel₀ _ (show (2 : ℝ) ^ k ≠ 0 by positivity)] using this
  exact_mod_cast this

/-- The data `(k, m, y₀, s)` determine the address. -/
lemma address_eq_of_data {n n' : ℕ} (hk : scale n = scale n') (hm : cellIdx n = cellIdx n')
    (hy : y0n n = y0n n') (hs : sn n = sn n') : n = n' := by
  apply unpack_bijective.1
  have h2 : (unpack n).2.1 = (unpack n').2.1 := Zenum_bijective.1 hm
  have h3 : (unpack n).2.2.1 = (unpack n').2.2.1 := Qenum.injective hy
  have h4 : (unpack n).2.2.2 = (unpack n').2.2.2 := Qstar.injective (Subtype.ext hs)
  exact Prod.ext hk (Prod.ext h2 (Prod.ext h3 h4))

/-- **Theorem 3.5 (uniqueness of the address).** `Γ` is injective. -/
theorem Gamma_injective : Injective Gamma := by
  intro n n' h
  simp only [Gamma, Prod.mk.injEq] at h
  obtain ⟨ha, hb, hI⟩ := h
  rw [Set.Icc_eq_Icc_iff (cn_lt_dn n).le] at hI
  have hIx : Ix n = Ix n' := by rw [Ix, Ix, ha, hb, hI.1, hI.2]
  rw [Ix_eq_cellJ, Ix_eq_cellJ] at hIx
  obtain ⟨hk, hm⟩ := cellJ_inj hIx
  have hx : x0n n = x0n n' := by rw [x0n, x0n, hk, hm]
  have hs : sn n = sn n' := by unfold bn at hb; exact_mod_cast hb
  have hy : y0n n = y0n n' := by
    have : (y0n n : ℝ) = y0n n' := by
      have e : ∀ j, (y0n j : ℝ) = an j + bn j * x0n j := by intro j; unfold an bn; ring
      rw [e, e, ha, hb, hx]
    exact_mod_cast this
  exact address_eq_of_data hk hm hy hs

/-- **Theorem 3.5 (bijection onto the library).** -/
theorem Gamma_bijOn : BijOn Gamma univ Library :=
  ⟨fun n _ => mem_range_self n, Gamma_injective.injOn, fun _ ⟨n, hn⟩ => ⟨n, trivial, hn⟩⟩

/-- Every datum `(k, m, y₀, s)` with `s ≠ 0` is realized by some address. -/
lemma exists_address (k : ℕ) (m : ℤ) (y : ℚ) (s : ℚ) (hs : s ≠ 0) :
    ∃ n, scale n = k ∧ cellIdx n = m ∧ y0n n = y ∧ sn n = s := by
  refine ⟨pack (k, Zinv m, Qenum.symm y, Qstar.symm ⟨s, hs⟩), ?_, ?_, ?_, ?_⟩ <;>
    simp [scale, cellIdx, y0n, sn, unpack_pack, Zenum_Zinv]

/-- The rational 1-jet `n ↦ (x_{0,n}, y_{0,n}, s_n)` of Equation (19). -/
noncomputable def jet (n : ℕ) : ℝ × ℝ × ℝ := (x0n n, (y0n n : ℝ), (sn n : ℝ))

/-- **Theorem 3.6 (dictionary, injectivity).** -/
theorem jet_injective : Injective jet := by
  intro n n' h
  simp only [jet, Prod.mk.injEq] at h
  obtain ⟨hx, hy, hs⟩ := h
  have hkm := center_injective (a₁ := (scale n, cellIdx n)) (a₂ := (scale n', cellIdx n')) hx
  simp only [Prod.mk.injEq] at hkm
  exact address_eq_of_data hkm.1 hkm.2 (by exact_mod_cast hy) (by exact_mod_cast hs)

/-- **Theorem 3.6 (dictionary, image).** The image of `n ↦ (x_{0,n}, y_{0,n}, s_n)` is
`𝔻_mid × ℚ × ℚ*`. -/
theorem range_jet : range jet =
    Dmid ×ˢ (range ((↑) : ℚ → ℝ) ×ˢ (range ((↑) : ℚ → ℝ) \ {0})) := by
  ext ⟨x, y, s⟩
  constructor
  · rintro ⟨n, hn⟩
    simp only [jet, Prod.mk.injEq] at hn
    obtain ⟨rfl, rfl, rfl⟩ := hn
    refine ⟨center_mem_Dmid _ _, mem_range_self _, mem_range_self _, ?_⟩
    simpa using sn_ne_zero n
  · rintro ⟨hx, ⟨q, rfl⟩, ⟨q', rfl⟩, hq'⟩
    have hq0 : q' ≠ 0 := by simpa using hq'
    obtain ⟨⟨k, m⟩, hkm⟩ := Dmid_subset_range_center hx
    obtain ⟨n, h1, h2, h3, h4⟩ := exists_address k m q q' hq0
    refine ⟨n, ?_⟩
    simp only [jet, x0n, h1, h2, h3, h4]
    simp only at hkm
    rw [hkm]

/-- **Theorem 3.6 (dictionary, bijection).** -/
theorem jet_bijOn : BijOn jet univ
    (Dmid ×ˢ (range ((↑) : ℚ → ℝ) ×ˢ (range ((↑) : ℚ → ℝ) \ {0}))) := by
  rw [← range_jet]
  exact ⟨fun n _ => mem_range_self n, jet_injective.injOn, fun x ⟨n, hn⟩ => ⟨n, trivial, hn⟩⟩

/-- **Theorem 3.6 (density).** The image of the dictionary is dense in `ℝ³`. -/
theorem jet_dense : Dense (range jet) := by
  rw [range_jet]
  refine Dmid_dense.prod (Rat.denseRange_cast.prod ?_)
  exact Rat.denseRange_cast.diff_singleton 0

end Dyadic2
