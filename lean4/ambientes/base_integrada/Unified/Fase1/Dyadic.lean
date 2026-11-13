module

public import Unified.Fase1.Indexing

/-!
# Section 3 — Células diádicas e operador gerador

Formalization of Section 3 of `artigo_fase1_autocontido.tex`:

* dyadic cells `J k m`, owned cells `Jown k m` (eq. (09)), centers `x0 k m` (eq. (10)),
  the sets `𝔻` and `𝔻_mid`, and Lemma 3.1 (dyadic structure);
* the decompression `n ↦ (k, μ, r, t)` (eq. (13)) and Lemma 3.2;
* the generator `Γ` (eqs. (14)–(17)), the spatial preimage `I_n^x` (eq. (18)),
  Lemma 3.4 (exact spatial validity), Theorem 3.5 (uniqueness of the address) and
  Theorem 3.6 (dictionary of rational jets).

Following the paper we write `m 2^{-k}` as `m / 2^k`.
-/

@[expose] public section

open Set

namespace Fase1

/-! ## Cells, ownership and centers -/

/-- The closed dyadic cell `J_{k,m} = [m 2^{-k}, (m+1) 2^{-k}]` (eq. (09)). -/
def J (k : ℕ) (m : ℤ) : Set ℝ := Icc ((m : ℝ) / 2 ^ k) (((m : ℝ) + 1) / 2 ^ k)

/-- The owned (half-open) dyadic cell `J^own_{k,m} = [m 2^{-k}, (m+1) 2^{-k})` (eq. (09)). -/
def Jown (k : ℕ) (m : ℤ) : Set ℝ := Ico ((m : ℝ) / 2 ^ k) (((m : ℝ) + 1) / 2 ^ k)

/-- The center `x₀(k,m) = (m + 1/2) 2^{-k} = (2m+1)/2^{k+1}` (eq. (10)). -/
noncomputable def x0 (k : ℕ) (m : ℤ) : ℝ := (2 * (m : ℝ) + 1) / 2 ^ (k + 1)

/-- The dyadic rationals `𝔻 = {j 2^{-K} : j ∈ ℤ, K ∈ ℕ₀}`. -/
def Dy : Set ℝ := {x | ∃ j : ℤ, ∃ K : ℕ, x = (j : ℝ) / 2 ^ K}

/-- The non-integer dyadic rationals `𝔻_mid = 𝔻 \ ℤ`. -/
def Dmid : Set ℝ := Dy \ range (Int.cast : ℤ → ℝ)

theorem x0_eq (k : ℕ) (m : ℤ) : x0 k m = ((m : ℝ) + 1 / 2) / 2 ^ k := by
  unfold x0; rw [pow_succ]; field_simp

/-- The owner index at scale `k` of a point `x` is `⌊2^k x⌋`. -/
theorem mem_Jown_iff (k : ℕ) (m : ℤ) (x : ℝ) : x ∈ Jown k m ↔ m = ⌊2 ^ k * x⌋ := by
  have h : (0:ℝ) < 2 ^ k := by positivity
  rw [eq_comm, Int.floor_eq_iff, Jown, mem_Ico, div_le_iff₀ h, lt_div_iff₀ h]
  constructor <;> rintro ⟨a, b⟩ <;> constructor <;> linarith

/-- **Lemma 3.1**, partition: for each `k`, the owned cells `J^own_{k,m}` partition `ℝ`;
the owner is `m = ⌊2^k x⌋`. -/
theorem Jown_partition (k : ℕ) (x : ℝ) : ∃! m : ℤ, x ∈ Jown k m :=
  ⟨⌊2 ^ k * x⌋, (mem_Jown_iff _ _ _).2 rfl, fun _ h => (mem_Jown_iff _ _ _).1 h⟩

/-- **Lemma 3.1**, refinement identity (11). -/
theorem J_refine (k : ℕ) (m : ℤ) : J k m = J (k + 1) (2 * m) ∪ J (k + 1) (2 * m + 1) := by
  have h : (0:ℝ) < 2 ^ k := by positivity
  unfold J
  have e1 : (((2 * m : ℤ) : ℝ)) / 2 ^ (k + 1) = (m : ℝ) / 2 ^ k := by
    push_cast; rw [pow_succ]; field_simp
  have e2 : (((2 * m : ℤ) : ℝ) + 1) / 2 ^ (k + 1) = (((2 * m + 1 : ℤ) : ℝ)) / 2 ^ (k + 1) := by
    push_cast; ring
  have e3 : (((2 * m + 1 : ℤ) : ℝ) + 1) / 2 ^ (k + 1) = ((m : ℝ) + 1) / 2 ^ k := by
    push_cast; rw [pow_succ]; field_simp; ring
  rw [e1, e3, e2, Icc_union_Icc_eq_Icc]
  · rw [← e1]; apply div_le_div_of_nonneg_right _ (by positivity); push_cast; linarith
  · rw [← e3]; apply div_le_div_of_nonneg_right _ (by positivity); push_cast; linarith

/-- **Lemma 3.1**, length `|J_{k,m}| = 2^{-k}` (eq. (11)). -/
theorem volume_J (k : ℕ) (m : ℤ) :
    MeasureTheory.volume (J k m) = ENNReal.ofReal ((2 : ℝ) ^ (-(k : ℤ))) := by
  rw [J, Real.volume_Icc]
  congr 1
  rw [zpow_neg, zpow_natCast]; field_simp; ring

lemma two_pow_ne_odd (k : ℕ) (m z : ℤ) : (2 * m + 1) ≠ z * 2 ^ (k + 1) := by
  intro h
  have : (2:ℤ) ∣ 2 * m + 1 := ⟨z * 2 ^ k, by rw [h]; ring⟩
  omega

theorem x0_mem_Dmid (k : ℕ) (m : ℤ) : x0 k m ∈ Dmid := by
  refine ⟨⟨2 * m + 1, k + 1, by unfold x0; push_cast; ring⟩, ?_⟩
  rintro ⟨z, hz⟩
  unfold x0 at hz
  rw [eq_div_iff (by positivity)] at hz
  apply two_pow_ne_odd k m z
  exact_mod_cast hz.symm

lemma x0_inj_aux {k k' : ℕ} {m m' : ℤ} (hk : k ≤ k') (h : x0 k m = x0 k' m') :
    k = k' ∧ m = m' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  unfold x0 at h
  rw [div_eq_div_iff (by positivity) (by positivity)] at h
  have h' : (2 * m + 1) * 2 ^ (k + d + 1) = (2 * m' + 1) * (2 ^ (k + 1) : ℤ) := by
    exact_mod_cast h
  have h'' : (2 * m + 1) * 2 ^ d = 2 * m' + 1 := by
    have hp : (2:ℤ) ^ (k + d + 1) = 2 ^ d * 2 ^ (k + 1) := by ring
    rw [hp, ← mul_assoc] at h'
    exact mul_right_cancel₀ (by positivity) h'
  rcases d with _ | d
  · simp at h''; exact ⟨rfl, by omega⟩
  · exfalso
    have : (2:ℤ) ∣ 2 * m' + 1 := ⟨(2 * m + 1) * 2 ^ d, by rw [← h'']; ring⟩
    omega

theorem x0_injective : Function.Injective (fun p : ℕ × ℤ => x0 p.1 p.2) := by
  rintro ⟨k, m⟩ ⟨k', m'⟩ h
  simp only at h
  rcases le_total k k' with hk | hk
  · obtain ⟨h1, h2⟩ := x0_inj_aux hk h; rw [h1, h2]
  · obtain ⟨h1, h2⟩ := x0_inj_aux hk h.symm; rw [h1, h2]

lemma dyadic_mem_range_x0 (K : ℕ) : ∀ j : ℤ, ((j : ℝ) / 2 ^ K) ∉ range (Int.cast : ℤ → ℝ) →
    ∃ k m, x0 k m = (j : ℝ) / 2 ^ K := by
  induction K with
  | zero => intro j hj; exact absurd ⟨j, by simp⟩ hj
  | succ K ih =>
    intro j hj
    obtain ⟨i, rfl | rfl⟩ := Int.even_or_odd' j
    · obtain ⟨k, m, h⟩ := ih i (by
        intro hm; apply hj
        convert hm using 1; push_cast; rw [pow_succ]; field_simp)
      exact ⟨k, m, by rw [h]; push_cast; rw [pow_succ]; field_simp⟩
    · exact ⟨K, i, by unfold x0; push_cast; ring⟩

theorem range_x0 : range (fun p : ℕ × ℤ => x0 p.1 p.2) = Dmid := by
  ext x
  constructor
  · rintro ⟨⟨k, m⟩, rfl⟩; exact x0_mem_Dmid k m
  · rintro ⟨⟨j, K, rfl⟩, hx⟩
    obtain ⟨k, m, h⟩ := dyadic_mem_range_x0 K j hx
    exact ⟨(k, m), h⟩

/-- **Lemma 3.1**, centers: `(k,m) ↦ x₀(k,m)` is a bijection of `ℕ₀ × ℤ` onto `𝔻_mid`. -/
theorem x0_bijOn : BijOn (fun p : ℕ × ℤ => x0 p.1 p.2) univ Dmid :=
  ⟨fun p _ => x0_mem_Dmid p.1 p.2, x0_injective.injOn,
    fun x hx => by rw [← range_x0] at hx; obtain ⟨p, hp⟩ := hx; exact ⟨p, trivial, hp⟩⟩

/-- **Lemma 3.1**, density of `𝔻_mid` in `ℝ`. -/
theorem Dmid_dense : Dense Dmid := by
  rw [Metric.dense_iff]
  intro x r hr
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hr (by norm_num : (1/2:ℝ) < 1)
  set m := ⌊2 ^ k * x⌋
  have h1 := Int.floor_le (2 ^ k * x)
  have h2 := Int.lt_floor_add_one (2 ^ k * x)
  have hp : (0:ℝ) < 2 ^ k := by positivity
  refine ⟨x0 k m, ?_, x0_mem_Dmid k m⟩
  rw [Metric.mem_ball, Real.dist_eq, x0_eq, abs_lt]
  rw [one_div_pow] at hk
  have e : ((m : ℝ) + 1 / 2) / 2 ^ k - x = (((m:ℝ) + 1/2) - 2 ^ k * x) / 2 ^ k := by
    field_simp
  rw [e]
  have hk' : 1 < r * 2 ^ k := by rwa [div_lt_iff₀ hp] at hk
  constructor
  · rw [lt_div_iff₀ hp]; nlinarith
  · rw [div_lt_iff₀ hp]; nlinarith

/-! ## Anchored lines and decompression -/

/-- The anchored line `ℓ(x) = y₀ + s (x - x₀)` (eq. (12)). -/
def anchoredLine (x₀ y₀ s : ℝ) (x : ℝ) : ℝ := y₀ + s * (x - x₀)

/-- Eq. (12): `ℓ(x) = a + b x` with `b = s`, `a = y₀ - s x₀`. -/
theorem anchoredLine_eq (x₀ y₀ s x : ℝ) :
    anchoredLine x₀ y₀ s x = (y₀ - s * x₀) + s * x := by
  unfold anchoredLine; ring

/-- The decompression `n ↦ (k, μ, r, t)` of eq. (13). -/
noncomputable def decode (n : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  let uv := cantorUnpair n
  let kμ := cantorUnpair uv.1
  let rt := cantorUnpair uv.2
  (kμ.1, kμ.2, rt.1, rt.2)

/-- The explicit inverse `(k, μ, r, t) ↦ π(π(k,μ), π(r,t))`. -/
def encode (q : ℕ × ℕ × ℕ × ℕ) : ℕ :=
  cantorPair (cantorPair (q.1, q.2.1), cantorPair (q.2.2.1, q.2.2.2))

theorem encode_decode (n : ℕ) : encode (decode n) = n := by
  simp [encode, decode, cantorPair_cantorUnpair]

theorem decode_encode (q : ℕ × ℕ × ℕ × ℕ) : decode (encode q) = q := by
  simp [encode, decode, cantorUnpair_cantorPair]

/-- **Lemma 3.2**: `n ↦ (k, μ, r, t)` is a bijection of `ℕ₀` onto `ℕ₀⁴`. -/
theorem decode_bijective : Function.Bijective decode :=
  Function.bijective_iff_has_inverse.2 ⟨encode, encode_decode, decode_encode⟩

/-! ## The generator `Γ` -/

/-- Scale `k(n)`. -/
noncomputable def kOf (n : ℕ) : ℕ := (decode n).1
/-- Position `m(n) = Z(μ)` (eq. (14)). -/
noncomputable def mOf (n : ℕ) : ℤ := Zenum (decode n).2.1
/-- Center `x_{0,n} = x₀(k,m)` (eq. (14)). -/
noncomputable def x0n (n : ℕ) : ℝ := x0 (kOf n) (mOf n)
/-- Anchored value `y_{0,n} = Q(r)` (eq. (14)). -/
noncomputable def y0n (n : ℕ) : ℚ := Q (decode n).2.2.1
/-- Slope `s_n = Q*(t)` (eq. (14)). -/
noncomputable def sn (n : ℕ) : QStar := Qstar (decode n).2.2.2
/-- `b_n = s_n` (eq. (15)). -/
noncomputable def bn (n : ℕ) : ℝ := ((sn n : ℚ) : ℝ)
/-- `a_n = y_{0,n} - s_n x_{0,n}` (eq. (15)). -/
noncomputable def an (n : ℕ) : ℝ := (y0n n : ℝ) - bn n * x0n n
/-- The line `ℓ_n(x) = a_n + b_n x`. -/
noncomputable def ell (n : ℕ) (x : ℝ) : ℝ := an n + bn n * x
/-- Left endpoint `x_L = m 2^{-k}`. -/
noncomputable def xL (n : ℕ) : ℝ := (mOf n : ℝ) / 2 ^ kOf n
/-- Right endpoint `x_R = (m+1) 2^{-k}`. -/
noncomputable def xR (n : ℕ) : ℝ := ((mOf n : ℝ) + 1) / 2 ^ kOf n
/-- `c_n = min{ℓ_n(x_L), ℓ_n(x_R)}` (eq. (16)). -/
noncomputable def cn (n : ℕ) : ℝ := min (ell n (xL n)) (ell n (xR n))
/-- `d_n = max{ℓ_n(x_L), ℓ_n(x_R)}` (eq. (16)). -/
noncomputable def dn (n : ℕ) : ℝ := max (ell n (xL n)) (ell n (xR n))

/-- The generator `Γ(n) = (a_n, b_n, [c_n, d_n])` of eq. (17); the closed interval
`[c_n, d_n]` is encoded by the pair of its endpoints. -/
noncomputable def Γ (n : ℕ) : ℝ × ℝ × (ℝ × ℝ) := (an n, bn n, (cn n, dn n))

/-- The library `𝓛 = Γ(ℕ₀)`. -/
def library : Set (ℝ × ℝ × (ℝ × ℝ)) := range Γ

/-- `ℓ_n` is the anchored line through `(x_{0,n}, y_{0,n})` with slope `s_n`. -/
theorem ell_eq_anchoredLine (n : ℕ) (x : ℝ) :
    ell n x = anchoredLine (x0n n) (y0n n) (bn n) x := by
  unfold ell an anchoredLine; ring

/-- The slope `b_n` is nonzero, so `Γ(n) ∈ ℝ × (ℝ \ {0}) × 𝓘`. -/
theorem bn_ne_zero (n : ℕ) : bn n ≠ 0 := by
  unfold bn; exact_mod_cast (sn n).2

lemma xL_lt_xR (n : ℕ) : xL n < xR n := by
  unfold xL xR; apply div_lt_div_of_pos_right _ (by positivity); linarith

lemma ell_inv (n : ℕ) (x : ℝ) : (ell n x - an n) / bn n = x := by
  unfold ell; field_simp [bn_ne_zero n]; ring

/-- The interval `[c_n, d_n]` of eq. (16) is nondegenerate. -/
theorem cn_lt_dn (n : ℕ) : cn n < dn n := by
  unfold cn dn
  rw [min_lt_max]
  intro h
  have := congrArg (fun y => (y - an n) / bn n) h
  simp only [ell_inv] at this
  exact (xL_lt_xR n).ne this

/-- The spatial preimage `I^x` of eq. (18) of a triple `(a, b, [c, d])`. -/
noncomputable def Ix (g : ℝ × ℝ × (ℝ × ℝ)) : Set ℝ :=
  Icc (min ((g.2.2.1 - g.1) / g.2.1) ((g.2.2.2 - g.1) / g.2.1))
    (max ((g.2.2.1 - g.1) / g.2.1) ((g.2.2.2 - g.1) / g.2.1))

/-- **Lemma 3.4 (validade espacial exata)**: `I_n^x = J_{k(n), m(n)}`. -/
theorem Ix_Γ (n : ℕ) : Ix (Γ n) = J (kOf n) (mOf n) := by
  have hJ : J (kOf n) (mOf n) = Icc (xL n) (xR n) := rfl
  rw [hJ]
  simp only [Ix, Γ]
  have hlt := xL_lt_xR n
  rcases lt_or_gt_of_ne (bn_ne_zero n) with hb | hb
  · have hle : ell n (xR n) ≤ ell n (xL n) := by
      unfold ell; nlinarith
    rw [cn, dn, min_eq_right hle, max_eq_left hle, ell_inv, ell_inv,
      min_eq_right hlt.le, max_eq_left hlt.le]
  · have hle : ell n (xL n) ≤ ell n (xR n) := by
      unfold ell; nlinarith
    rw [cn, dn, min_eq_left hle, max_eq_right hle, ell_inv, ell_inv,
      min_eq_left hlt.le, max_eq_right hlt.le]

theorem J_injective {k k' : ℕ} {m m' : ℤ} (h : J k m = J k' m') : k = k' ∧ m = m' := by
  have hp : (0:ℝ) < 2 ^ k := by positivity
  have hp' : (0:ℝ) < 2 ^ k' := by positivity
  unfold J at h
  rw [Icc_eq_Icc_iff (div_le_div_of_nonneg_right (by linarith) hp.le)] at h
  obtain ⟨h1, h2⟩ := h
  have h3 : (1:ℝ) / 2 ^ k = 1 / 2 ^ k' := by
    have : ((m:ℝ) + 1) / 2 ^ k - (m:ℝ) / 2 ^ k = ((m':ℝ) + 1) / 2 ^ k' - (m':ℝ) / 2 ^ k' := by
      rw [h1, h2]
    rwa [← sub_div, ← sub_div, add_sub_cancel_left, add_sub_cancel_left] at this
  have h4 : (2:ℝ) ^ k = 2 ^ k' := by
    rw [div_eq_div_iff hp.ne' hp'.ne'] at h3; linarith
  have hk : k = k' := by
    have : (2:ℕ) ^ k = 2 ^ k' := by exact_mod_cast h4
    exact Nat.pow_right_injective le_rfl this
  subst hk
  refine ⟨rfl, ?_⟩
  rw [div_left_inj' hp.ne'] at h1
  exact_mod_cast h1

/-- The rational 1-jet map `n ↦ (x_{0,n}, y_{0,n}, s_n)` of eq. (19), with values in
`𝔻_mid × ℚ × ℚ*`. -/
noncomputable def jet (n : ℕ) : Dmid × ℚ × QStar :=
  (⟨x0n n, x0_mem_Dmid _ _⟩, y0n n, sn n)

/-- **Theorem 3.6 (dicionário de jatos racionais)**, bijectivity. -/
lemma Q_injective : Function.Injective Q :=
  (Equiv.ofBijective htRank htRank_bijective).symm.injective

lemma Qstar_injective : Function.Injective Qstar :=
  (Equiv.ofBijective htRankStar htRankStar_bijective).symm.injective

theorem jet_bijective : Function.Bijective jet := by
  constructor
  · intro n n' h
    simp only [jet, Prod.mk.injEq, Subtype.mk.injEq] at h
    obtain ⟨hx, hy, hs⟩ := h
    have hkm := x0_injective (a₁ := (kOf n, mOf n)) (a₂ := (kOf n', mOf n')) hx
    simp only [Prod.mk.injEq] at hkm
    apply decode_bijective.1
    have e1 : (decode n).1 = (decode n').1 := hkm.1
    have e2 : (decode n).2.1 = (decode n').2.1 := Zenum_bijective.1 hkm.2
    have e3 : (decode n).2.2.1 = (decode n').2.2.1 := Q_injective hy
    have e4 : (decode n).2.2.2 = (decode n').2.2.2 := Qstar_injective hs
    exact Prod.ext e1 (Prod.ext e2 (Prod.ext e3 e4))
  · rintro ⟨⟨x, hx⟩, y, s⟩
    rw [← range_x0] at hx
    obtain ⟨⟨k, m⟩, rfl⟩ := hx
    refine ⟨encode (k, ZenumInv m, htRank y, htRankStar s), ?_⟩
    simp only [jet, x0n, kOf, mOf, y0n, sn, decode_encode, Zenum_ZenumInv, Q_htRank,
      Qstar_htRankStar]

/-- **Theorem 3.5 (unicidade do endereço)**: `Γ` is injective. -/
theorem Γ_injective : Function.Injective Γ := by
  intro n n' h
  have hI := congrArg Ix h
  rw [Ix_Γ, Ix_Γ] at hI
  obtain ⟨hk, hm⟩ := J_injective hI
  simp only [Γ, Prod.mk.injEq] at h
  obtain ⟨ha, hb, -⟩ := h
  have hx : x0n n = x0n n' := by unfold x0n; rw [hk, hm]
  have hs : sn n = sn n' := by
    apply Subtype.ext; unfold bn at hb; exact_mod_cast hb
  have hy : y0n n = y0n n' := by
    unfold an at ha; rw [hb, hx] at ha
    exact_mod_cast (sub_left_inj.1 ha)
  apply jet_bijective.1
  simp only [jet, hx, hy, hs]

/-- **Theorem 3.5**: `Γ` is a bijection of `ℕ₀` onto the library `𝓛`, i.e. every atom has a
unique address. -/
theorem Γ_bijective_onto_library : Function.Bijective (rangeFactorization Γ) :=
  ⟨fun _ _ h => Γ_injective (congrArg Subtype.val h), rangeFactorization_surjective⟩

/-- **Theorem 3.6**, density: the image of `n ↦ (x_{0,n}, y_{0,n}, s_n)` is dense in `ℝ³`. -/
theorem jet_range_dense :
    Dense (range (fun n => (x0n n, ((y0n n : ℚ) : ℝ), (((sn n : QStar) : ℚ) : ℝ)))) := by
  have hrange : range (fun n => (x0n n, ((y0n n : ℚ) : ℝ), (((sn n : QStar) : ℚ) : ℝ))) =
      Dmid ×ˢ (range (Rat.cast : ℚ → ℝ) ×ˢ (range (Rat.cast : ℚ → ℝ) \ {0})) := by
    ext ⟨x, y, z⟩
    constructor
    · rintro ⟨n, hn⟩
      simp only [Prod.mk.injEq] at hn
      obtain ⟨rfl, rfl, rfl⟩ := hn
      refine ⟨x0_mem_Dmid _ _, ⟨_, rfl⟩, ⟨_, rfl⟩, ?_⟩
      simp only [mem_singleton_iff, Rat.cast_eq_zero]
      exact (sn n).2
    · rintro ⟨hx, ⟨y', rfl⟩, ⟨z', rfl⟩, hz⟩
      have hz' : z' ≠ 0 := by
        simpa only [mem_singleton_iff, Rat.cast_eq_zero] using hz
      obtain ⟨n, hn⟩ := jet_bijective.2 (⟨x, hx⟩, y', ⟨z', hz'⟩)
      refine ⟨n, ?_⟩
      simp only [jet, Prod.mk.injEq, Subtype.mk.injEq] at hn
      obtain ⟨h1, h2, h3⟩ := hn
      simp only [h1, h2, h3]
  rw [hrange]
  exact Dmid_dense.prod (Rat.denseRange_cast.prod (Rat.denseRange_cast.diff_singleton 0))

end Fase1
