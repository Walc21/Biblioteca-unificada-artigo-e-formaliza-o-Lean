import Mathlib

/-!
# The dyadic sawtooth `N² B / 4^{⌊log₂(N/M)⌋}`

Accumulation points, `liminf` and `limsup` of sequences that eventually coincide with
`N ↦ N² B / 4^{⌊log₂ ⌊N/M⌋⌋}`; used for the exact dyadic laws of Section 12.
-/

namespace Artigo

open Filter Topology Set

lemma liminf_le_of_mapClusterPt' {u : ℕ → ℝ} {x : ℝ} (h : MapClusterPt x atTop u)
    (hb : IsBoundedUnder (· ≥ ·) atTop u) : liminf u atTop ≤ x := by
  refine le_of_forall_pos_lt_add fun η hη => ?_
  have hfr := (mapClusterPt_iff_frequently.mp h) (Iio (x + η / 2)) (Iio_mem_nhds (by linarith))
  have := liminf_le_of_frequently_le (hfr.mono fun n hn => le_of_lt hn) hb
  linarith

lemma le_limsup_of_mapClusterPt' {u : ℕ → ℝ} {x : ℝ} (h : MapClusterPt x atTop u)
    (hb : IsBoundedUnder (· ≤ ·) atTop u) : x ≤ limsup u atTop := by
  refine le_of_forall_pos_lt_add fun η hη => ?_
  have hfr := (mapClusterPt_iff_frequently.mp h) (Ioi (x - η / 2)) (Ioi_mem_nhds (by linarith))
  have := le_limsup_of_frequently_le (hfr.mono fun n hn => le_of_lt hn) hb
  linarith

lemma four_pow_eq (R : ℕ) : (4 : ℝ) ^ R = (2 ^ R) ^ 2 := by
  rw [← pow_mul, mul_comm, pow_mul]; norm_num

lemma saw_bracket {M N : ℕ} (hM : 1 ≤ M) (hN : M ≤ N) :
    (M : ℝ) * 2 ^ Nat.log 2 (N / M) ≤ N ∧ (N : ℝ) < M * 2 ^ (Nat.log 2 (N / M) + 1) := by
  have hn : N / M ≠ 0 := (Nat.div_pos hN (by omega)).ne'
  have h1 := Nat.pow_log_le_self 2 hn
  have h2 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (N / M)
  have h3 : M * (N / M) ≤ N := Nat.mul_div_le N M
  have h4 : N < M * (N / M + 1) := Nat.lt_mul_div_succ N (by omega)
  constructor
  · have : M * 2 ^ Nat.log 2 (N / M) ≤ N := le_trans (Nat.mul_le_mul_left _ h1) h3
    exact_mod_cast this
  · have : N < M * 2 ^ (Nat.log 2 (N / M) + 1) := lt_of_lt_of_le h4 (Nat.mul_le_mul_left _ h2)
    exact_mod_cast this

lemma saw_value_bounds {M N : ℕ} (hM : 1 ≤ M) (hN : M ≤ N) {B : ℝ} (hB : 0 < B) :
    (M : ℝ) ^ 2 * B ≤ (N : ℝ) ^ 2 * B / 4 ^ Nat.log 2 (N / M) ∧
      (N : ℝ) ^ 2 * B / 4 ^ Nat.log 2 (N / M) ≤ 4 * M ^ 2 * B := by
  obtain ⟨h1, h2⟩ := saw_bracket hM hN
  set x : ℝ := 2 ^ Nat.log 2 (N / M)
  have hx : 0 < x := by positivity
  rw [four_pow_eq, pow_succ] at *
  have hM0 : (0 : ℝ) ≤ M := by positivity
  constructor
  · rw [le_div_iff₀ (by positivity)]
    have : ((M : ℝ) * x) ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    nlinarith
  · rw [div_le_iff₀ (by positivity)]
    have : (N : ℝ) ^ 2 ≤ ((M : ℝ) * (x * 2)) ^ 2 := pow_le_pow_left₀ (by positivity) h2.le 2
    nlinarith

/-- a subsequence along which `N / (M 2^R) → t` with `⌊log₂ ⌊N/M⌋⌋ = R` -/
lemma saw_tendsto_sub {u : ℕ → ℝ} {M : ℕ} (hM : 1 ≤ M) {B : ℝ}
    (hu : ∀ᶠ N in atTop, u N = (N : ℝ) ^ 2 * B / 4 ^ Nat.log 2 (N / M))
    {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    (hlog : ∀ᶠ R in atTop, Nat.log 2 (φ R / M) = R) {t : ℝ}
    (hlim : Tendsto (fun R => (φ R : ℝ) / (M * 2 ^ R)) atTop (𝓝 t)) :
    MapClusterPt ((M : ℝ) ^ 2 * B * t ^ 2) atTop u := by
  refine MapClusterPt.of_comp hφ (Tendsto.mapClusterPt ?_)
  have hlim2 : Tendsto (fun R => (M : ℝ) ^ 2 * B * ((φ R : ℝ) / (M * 2 ^ R)) ^ 2) atTop
      (𝓝 ((M : ℝ) ^ 2 * B * t ^ 2)) := (hlim.pow 2).const_mul _
  refine hlim2.congr' ?_
  filter_upwards [hφ.eventually hu, hlog] with R h1 h2
  simp only [Function.comp, h1, h2, four_pow_eq]
  have hM0 : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

/-- **sawtooth law**: if `u N = N² B / 4^{⌊log₂⌊N/M⌋⌋}` eventually (`M ≥ 1`, `B > 0`), then the
accumulation points of `u` form `[M²B, 4M²B]`, `liminf u = M²B` and `limsup u = 4M²B`. -/
theorem sawtooth {u : ℕ → ℝ} {M : ℕ} (hM : 1 ≤ M) {B : ℝ} (hB : 0 < B)
    (hu : ∀ᶠ N in atTop, u N = (N : ℝ) ^ 2 * B / 4 ^ Nat.log 2 (N / M)) :
    {x | MapClusterPt x atTop u} = Icc ((M : ℝ) ^ 2 * B) (4 * M ^ 2 * B) ∧
    liminf u atTop = (M : ℝ) ^ 2 * B ∧ limsup u atTop = 4 * (M : ℝ) ^ 2 * B := by
  have hbd : ∀ᶠ N in atTop, u N ∈ Icc ((M : ℝ) ^ 2 * B) (4 * M ^ 2 * B) := by
    filter_upwards [hu, eventually_ge_atTop M] with N h hN
    rw [h]; exact saw_value_bounds hM hN hB
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hpow : Tendsto (fun R : ℕ => (2 : ℝ) ^ R) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hcl : ∀ x ∈ Icc ((M : ℝ) ^ 2 * B) (4 * M ^ 2 * B), MapClusterPt x atTop u := by
    intro x hx
    have hL : 0 < (M : ℝ) ^ 2 * B := by positivity
    set t := Real.sqrt (x / ((M : ℝ) ^ 2 * B)) with ht
    have hxt : x = (M : ℝ) ^ 2 * B * t ^ 2 := by
      rw [ht, Real.sq_sqrt (div_nonneg (hL.le.trans hx.1) hL.le)]; field_simp
    have ht1 : 1 ≤ t := by
      rw [ht, Real.le_sqrt (by norm_num) (div_nonneg (hL.le.trans hx.1) hL.le), le_div_iff₀ hL]
      linarith [hx.1]
    have ht2 : t ≤ 2 := by
      rw [ht, Real.sqrt_le_left (by norm_num), div_le_iff₀ hL]; linarith [hx.2]
    rw [hxt]
    rcases ht2.lt_or_eq with ht2 | ht2
    · -- `φ R = M ⌈t 2^R⌉`
      refine saw_tendsto_sub hM hu (φ := fun R => M * ⌈t * 2 ^ R⌉₊) ?_ ?_ ?_
      · refine tendsto_atTop_mono (f := fun R : ℕ => 2 ^ R) (fun R => ?_)
          (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
        have h1 : (2 : ℝ) ^ R ≤ t * 2 ^ R := by nlinarith [pow_pos (two_pos (α := ℝ)) R]
        have h2 : (2 ^ R : ℕ) ≤ ⌈t * 2 ^ R⌉₊ := by
          have := h1.trans (Nat.le_ceil (t * 2 ^ R))
          exact_mod_cast this
        exact h2.trans (Nat.le_mul_of_pos_left _ (by omega))
      · have hev : ∀ᶠ R : ℕ in atTop, (1 : ℝ) ≤ (2 - t) * 2 ^ R :=
          (hpow.const_mul_atTop (by linarith)).eventually_ge_atTop 1
        filter_upwards [hev] with R hR
        rw [Nat.mul_div_cancel_left _ (by omega)]
        apply Nat.log_eq_of_pow_le_of_lt_pow
        · have h1 : (2 : ℝ) ^ R ≤ t * 2 ^ R := by nlinarith [pow_pos (two_pos (α := ℝ)) R]
          have := h1.trans (Nat.le_ceil (t * 2 ^ R))
          exact_mod_cast this
        · have h1 := Nat.ceil_lt_add_one (show 0 ≤ t * 2 ^ R by positivity)
          have : (⌈t * 2 ^ R⌉₊ : ℝ) < 2 ^ (R + 1) := by rw [pow_succ]; linarith
          exact_mod_cast this
      · -- `⌈t 2^R⌉ / 2^R → t`
        have hlow : ∀ R : ℕ, t ≤ ((M * ⌈t * 2 ^ R⌉₊ : ℕ) : ℝ) / (M * 2 ^ R) := by
          intro R
          push_cast
          rw [le_div_iff₀ (by positivity)]
          have := Nat.le_ceil (t * 2 ^ R)
          nlinarith
        have hup : ∀ R : ℕ, ((M * ⌈t * 2 ^ R⌉₊ : ℕ) : ℝ) / (M * 2 ^ R) ≤ t + 1 / 2 ^ R := by
          intro R
          push_cast
          rw [div_le_iff₀ (by positivity)]
          have := (Nat.ceil_lt_add_one (show 0 ≤ t * 2 ^ R by positivity)).le
          have h2R : (0 : ℝ) < 2 ^ R := by positivity
          field_simp
          nlinarith
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ hlow hup
        have : Tendsto (fun R : ℕ => t + 1 / (2 : ℝ) ^ R) atTop (𝓝 (t + 0)) :=
          tendsto_const_nhds.add (by
            simpa using (tendsto_inv_atTop_zero.comp hpow))
        simpa using this
    · -- `φ R = M 2^{R+1} - 1`
      rw [ht2]
      refine saw_tendsto_sub hM hu (φ := fun R => M * 2 ^ (R + 1) - 1) ?_ ?_ ?_
      · refine tendsto_atTop_mono (f := fun R : ℕ => 2 ^ R) (fun R => ?_)
          (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
        have h1 : 2 ^ R ≤ M * 2 ^ R := Nat.le_mul_of_pos_left _ (by omega)
        have h2 : M * 2 ^ (R + 1) = M * 2 ^ R + M * 2 ^ R := by ring
        have : 1 ≤ M * 2 ^ R := le_trans (Nat.one_le_two_pow) h1
        show 2 ^ R ≤ M * 2 ^ (R + 1) - 1
        omega
      · refine Eventually.of_forall fun R => ?_
        have hdiv : (M * 2 ^ (R + 1) - 1) / M = 2 ^ (R + 1) - 1 := by
          apply Nat.div_eq_of_lt_le
          · have hc : M * 2 ^ (R + 1) = 2 ^ (R + 1) * M := mul_comm _ _
            rw [Nat.sub_mul, one_mul]
            omega
          · have hP : 1 ≤ 2 ^ (R + 1) := Nat.one_le_two_pow
            have hc : M * 2 ^ (R + 1) = 2 ^ (R + 1) * M := mul_comm _ _
            have : 1 ≤ M * 2 ^ (R + 1) := le_trans hP (Nat.le_mul_of_pos_left _ (by omega))
            rw [Nat.sub_add_cancel hP]
            omega
        rw [hdiv]
        apply Nat.log_eq_of_pow_le_of_lt_pow
        · rw [pow_succ]; have := Nat.one_le_two_pow (n := R); omega
        · have := Nat.one_le_two_pow (n := R + 1); omega
      · have heq : ∀ R : ℕ, ((M * 2 ^ (R + 1) - 1 : ℕ) : ℝ) / (M * 2 ^ R) = 2 - 1 / (M * 2 ^ R) := by
          intro R
          have : 1 ≤ M * 2 ^ (R + 1) :=
            le_trans Nat.one_le_two_pow (Nat.le_mul_of_pos_left _ (by omega))
          rw [Nat.cast_sub this]
          push_cast
          field_simp
          ring
        simp_rw [heq]
        have : Tendsto (fun R : ℕ => (2 : ℝ) - 1 / (M * 2 ^ R)) atTop (𝓝 (2 - 0)) :=
          tendsto_const_nhds.sub ((tendsto_inv_atTop_zero.comp
              (Tendsto.const_mul_atTop (show (0 : ℝ) < M by linarith) hpow)).congr
              (fun R => by simp [Function.comp, one_div]))
        simpa using this
  have hset : {x | MapClusterPt x atTop u} = Icc ((M : ℝ) ^ 2 * B) (4 * M ^ 2 * B) := by
    ext x
    exact ⟨fun h => isClosed_Icc.mem_of_mapClusterPt h hbd, hcl x⟩
  have hb1 : IsBoundedUnder (· ≤ ·) atTop u :=
    isBoundedUnder_of_eventually_le (hbd.mono fun _ h => h.2)
  have hb2 : IsBoundedUnder (· ≥ ·) atTop u :=
    isBoundedUnder_of_eventually_ge (hbd.mono fun _ h => h.1)
  have hle : (M : ℝ) ^ 2 * B ≤ 4 * M ^ 2 * B := by nlinarith [sq_nonneg (M : ℝ)]
  refine ⟨hset, le_antisymm ?_ ?_, le_antisymm ?_ ?_⟩
  · exact liminf_le_of_mapClusterPt' (hcl _ ⟨le_rfl, hle⟩) hb2
  · exact le_liminf_of_le hb1.isCoboundedUnder_ge (hbd.mono fun _ h => h.1)
  · exact limsup_le_of_le hb2.isCoboundedUnder_le (hbd.mono fun _ h => h.2)
  · exact le_limsup_of_mapClusterPt' (hcl _ ⟨hle, le_rfl⟩) hb1

end Artigo
