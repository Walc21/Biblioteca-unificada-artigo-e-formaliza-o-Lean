import Pendencias.Agenda
import Pendencias.Ponte

/-!
# IV.4.5 — endpoint `C²`

Na raiz `K = [0,1]`, com `𝓕_{R,M} = FRMIcc R M` (C² só em `[0,1]`),
`C_H = max{4(R+1), 2(4R+M/2+1)}` (`Artigo.CH`) e `H₂(N) = ⌈C_H N²⌉`:

* `sup_{f ∈ 𝓕_{R,M}} 𝔞_{2,∞}^{𝓛,H₂}(f) ≤ max{R, (M+4)/2}` (`c2_endpoint`);
* para `N ≥ 2` a cota é realizada por uma montagem admissível cujos três comprimentos
  de código são `≤ C_b N log₂(2N)` (`c2_endpoint_bits`).
-/

namespace Pendencias.Agenda

open Set Artigo LTree Pendencias

/-- funcional de taxa `𝔞_{α,∞}^{𝓛,H}(f) = sup_{N ≥ 1} N^α e_N^{𝓛,H}(f)` -/
noncomputable def rateInf (α : ℝ) (H : ℕ → ℕ) (f : ℝ → ℝ) : ENNReal :=
  ⨆ N : ℕ, ⨆ (_ : 1 ≤ N), ENNReal.ofReal ((N : ℝ) ^ α) * pErr H N f

/-- a agenda `H₂(N) = ⌈C_H N²⌉` -/
noncomputable def H2 (R M : ℝ) (N : ℕ) : ℕ := ⌈CH R M * (N : ℝ) ^ 2⌉₊

lemma distInf_zero_le {R : ℝ} {f : ℝ → ℝ} (h : ∀ x ∈ Icc (0 : ℝ) 1, |f x| ≤ R) :
    distInf f 0 ≤ ENNReal.ofReal R :=
  iSup₂_le fun x hx => ENNReal.ofReal_le_ofReal (by simpa using h x hx)

/-- **Corolário IV.4.5 (endpoint `C²`)**. -/
theorem c2_endpoint {R M : ℝ} :
    ∀ f ∈ FRMIcc R M, rateInf 2 (H2 R M) f ≤ ENNReal.ofReal (max R ((M + 4) / 2)) := by
  intro f hf
  refine iSup₂_le fun N hN => ?_
  rw [Real.rpow_two]
  rcases Nat.lt_or_ge N 2 with h | h
  · obtain rfl : N = 1 := by omega
    simp only [Nat.cast_one, one_pow, ENNReal.ofReal_one, one_mul]
    rw [pErr_eq_min]
    exact (min_le_left _ _).trans ((distInf_zero_le hf.2.1).trans
      (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  · have hp : pErr (H2 R M) N f ≤ ENNReal.ofReal ((M + 4) / (2 * (N : ℝ) ^ 2)) := by
      rw [pErr_eq_min]
      exact (min_le_right _ _).trans (joint_all_N_Icc hf N h).le
    have hN0 : (N : ℝ) ^ 2 ≠ 0 := by positivity
    calc ENNReal.ofReal ((N : ℝ) ^ 2) * pErr (H2 R M) N f
        ≤ ENNReal.ofReal ((N : ℝ) ^ 2) * ENNReal.ofReal ((M + 4) / (2 * (N : ℝ) ^ 2)) :=
          by gcongr
      _ = ENNReal.ofReal ((N : ℝ) ^ 2 * ((M + 4) / (2 * (N : ℝ) ^ 2))) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ = ENNReal.ofReal ((M + 4) / 2) := by congr 1; field_simp
      _ ≤ ENNReal.ofReal (max R ((M + 4) / 2)) := ENNReal.ofReal_le_ofReal (le_max_right _ _)

/-- **Corolário IV.4.5**, bits: para `N ≥ 2` há uma montagem admissível para `(N, H₂(N))` com
erro `≤ (M+4)/(2N²)` e os três comprimentos de código `≤ C_b N log₂(2N)`. -/
theorem c2_endpoint_bits (R M : ℝ) : ∃ Cb : ℕ, ∀ f ∈ FRMIcc R M, ∀ N : ℕ, 2 ≤ N →
    ∃ T : LTree, AdmNH N (H2 R M N) T ∧
      supDist f T ≤ ENNReal.ofReal ((M + 4) / (2 * (N : ℝ) ^ 2)) ∧
      Latom T.leaves ≤ Cb * N * Nat.log 2 (2 * N) ∧
      Lstr T.leaves ≤ Cb * N * Nat.log 2 (2 * N) ∧
      Lrat T.leaves ≤ Cb * N * Nat.log 2 (2 * N) := by
  obtain ⟨Cb, hCb⟩ := joint_budget_Icc R M
  refine ⟨Cb, fun f hf N hN => ?_⟩
  have hR : 0 ≤ R := (abs_nonneg _).trans (hf.2.1 0 ⟨le_rfl, zero_le_one⟩)
  have hM : 0 ≤ M := (abs_nonneg _).trans (hf.2.2 0 ⟨le_rfl, zero_le_one⟩)
  have hCH : 0 ≤ CH R M := le_trans (by linarith) (le_max_left _ _)
  set r := Nat.log 2 N
  have hr : 1 ≤ r := Nat.le_log_of_pow_le (by norm_num) (by simpa using hN)
  have h1 : 2 ^ r ≤ N := Nat.pow_log_le_self 2 (by omega)
  have h2 : N < 2 ^ (r + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have h1' : ((2 : ℝ) ^ r) ≤ N := by exact_mod_cast h1
  have h2' : (N : ℝ) < 2 * 2 ^ r := by rw [← pow_succ']; exact_mod_cast h2
  have hpos : (0 : ℝ) < 2 ^ r := by positivity
  obtain ⟨T, -, hw, hn, herr, hh, hA, hS, hQ⟩ := hCb r hr f hf
  have hlog : Cb * 2 ^ r * Nat.log 2 (2 * 2 ^ r) ≤ Cb * N * Nat.log 2 (2 * N) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left Cb h1) (Nat.log_mono_right (by omega))
  refine ⟨T, ⟨hw, by rw [hn]; exact h1, ?_⟩, (supDist_le herr).trans ?_, hA.trans hlog,
    hS.trans hlog, hQ.trans hlog⟩
  · show T.maxHeight ≤ ⌈CH R M * (N : ℝ) ^ 2⌉₊
    have : (T.maxHeight : ℝ) ≤ ⌈CH R M * (N : ℝ) ^ 2⌉₊ :=
      hh.trans (le_trans (by gcongr) (Nat.le_ceil _))
    exact_mod_cast this
  · exact ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_left (by linarith) (by positivity) (by nlinarith))

end Pendencias.Agenda
