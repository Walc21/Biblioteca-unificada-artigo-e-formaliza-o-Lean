import Pendencias.Endpoint

/-!
# IV.3.2 (redução às escalas diádicas) e IV.3.3 (falha de homogeneidade)

Funcional de taxa do Artigo 3, eq. (rate-functional-finite), para `0 < q < ∞`:
`𝔞_{α,q}(f) = (∑_{N ≥ 1} [N^α e_N(f)]^q / N)^{1/q}` (em `ENNReal`; o termo `N = 0` é nulo
automaticamente para `α, q > 0`). O caso `q = ∞` é `rateInf` (`Endpoint.lean`).
-/

namespace Pendencias.Agenda

open Set Artigo LTree Pendencias Finset

/-- termo `[N^α e_N(f)]^q / N` -/
noncomputable def rterm (α q : ℝ) (H : ℕ → ℕ) (f : ℝ → ℝ) (N : ℕ) : ENNReal :=
  (ENNReal.ofReal ((N : ℝ) ^ α) * pErr H N f) ^ q * (N : ENNReal)⁻¹

/-- `𝔞_{α,q}^{𝓛,H}(f)`, `0 < q < ∞` -/
noncomputable def rateQ (α q : ℝ) (H : ℕ → ℕ) (f : ℝ → ℝ) : ENNReal :=
  (∑' N : ℕ, rterm α q H f N) ^ (1 / q)

/-- termo diádico `(2^{rα} e_{2^r}(f))^q` -/
noncomputable def dterm (α q : ℝ) (H : ℕ → ℕ) (f : ℝ → ℝ) (r : ℕ) : ENNReal :=
  (ENNReal.ofReal (((2 : ℝ) ^ r) ^ α) * pErr H (2 ^ r) f) ^ q

/-- `‖(2^{rα} e_{2^r}(f))_r‖_{ℓ^q}` -/
noncomputable def dyadQ (α q : ℝ) (H : ℕ → ℕ) (f : ℝ → ℝ) : ENNReal :=
  (∑' r : ℕ, dterm α q H f r) ^ (1 / q)

/-- `‖(2^{rα} e_{2^r}(f))_r‖_{ℓ^∞}` -/
noncomputable def dyadInf (α : ℝ) (H : ℕ → ℕ) (f : ℝ → ℝ) : ENNReal :=
  ⨆ r : ℕ, ENNReal.ofReal (((2 : ℝ) ^ r) ^ α) * pErr H (2 ^ r) f

lemma pErr_antitone {H : ℕ → ℕ} (hH : Monotone H) (f : ℝ → ℝ) :
    Antitone (fun N => pErr H N f) :=
  antitone_nat_of_succ_le fun N => (schedule_nesting hH N f).2.1

lemma rterm_zero {α q : ℝ} (hα : 0 < α) (hq : 0 < q) (H : ℕ → ℕ) (f : ℝ → ℝ) :
    rterm α q H f 0 = 0 := by
  simp [rterm, Real.zero_rpow hα.ne', ENNReal.zero_rpow_of_pos hq]

/-! ## Blocos diádicos -/

lemma card_Ico_pow (r : ℕ) : (Finset.Ico (2 ^ r) (2 ^ (r + 1))).card = 2 ^ r := by
  rw [Nat.card_Ico, pow_succ]; omega

lemma sum_Ico_one_pow (u : ℕ → ENNReal) (R : ℕ) :
    ∑ n ∈ Finset.Ico 1 (2 ^ R), u n = ∑ r ∈ range R, ∑ n ∈ Finset.Ico (2 ^ r) (2 ^ (r + 1)), u n := by
  induction R with
  | zero => simp
  | succ R ih =>
      rw [← Finset.sum_Ico_consecutive u (Nat.one_le_two_pow) (Nat.pow_le_pow_right (by norm_num)
        (Nat.le_succ R)), ih, Finset.sum_range_succ]

lemma tsum_blocks (u : ℕ → ENNReal) (hu : u 0 = 0) :
    ∑' r, ∑ n ∈ Finset.Ico (2 ^ r) (2 ^ (r + 1)), u n = ∑' n, u n := by
  rw [ENNReal.tsum_eq_iSup_nat, ENNReal.tsum_eq_iSup_nat]
  have e : ∀ m, ∑ n ∈ range m, u n = ∑ n ∈ Finset.Ico 1 m, u n := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hm, hu, zero_add]
  simp_rw [← sum_Ico_one_pow, ← e]
  apply le_antisymm
  · exact iSup_le fun R => le_iSup (fun n => ∑ k ∈ range n, u k) (2 ^ R)
  · refine iSup_le fun n => le_trans ?_ (le_iSup _ n)
    exact Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.lt_two_pow_self).le)

/-! ## Comparações em cada bloco -/

lemma two_pow_rpow_succ (α : ℝ) (r : ℕ) : ((2 : ℝ) ^ (r + 1)) ^ α = 2 ^ α * ((2 : ℝ) ^ r) ^ α := by
  rw [pow_succ, Real.mul_rpow (by positivity) (by norm_num), mul_comm]

section bounds

variable {α q : ℝ} (hα : 0 < α) (hq : 0 < q) {H : ℕ → ℕ} (hH : Monotone H) (f : ℝ → ℝ)
include hα hq hH

/-- bloco `r`: `∑_{2^r ≤ N < 2^{r+1}} rterm N ≤ (2^α)^q · dterm r` -/
lemma block_le (r : ℕ) :
    ∑ n ∈ Finset.Ico (2 ^ r) (2 ^ (r + 1)), rterm α q H f n ≤
      ENNReal.ofReal (2 ^ α) ^ q * dterm α q H f r := by
  set X := ENNReal.ofReal (2 ^ α) * (ENNReal.ofReal (((2 : ℝ) ^ r) ^ α) * pErr H (2 ^ r) f)
  have hterm : ∀ n ∈ Finset.Ico (2 ^ r) (2 ^ (r + 1)), rterm α q H f n ≤ X ^ q * ((2 ^ r : ℕ) : ENNReal)⁻¹ := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hn1 : ((2 : ℝ) ^ r) ≤ n := by exact_mod_cast hn.1
    have hn2 : (n : ℝ) ≤ 2 ^ (r + 1) := by exact_mod_cast hn.2.le
    have hA : ENNReal.ofReal ((n : ℝ) ^ α) * pErr H n f ≤ X := by
      simp only [X]
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← two_pow_rpow_succ α r]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by positivity) hn2 hα.le))
        (pErr_antitone hH f hn.1)
    have hB : (n : ENNReal)⁻¹ ≤ ((2 ^ r : ℕ) : ENNReal)⁻¹ :=
      ENNReal.inv_le_inv.mpr (by exact_mod_cast hn.1)
    exact mul_le_mul' (ENNReal.rpow_le_rpow hA hq.le) hB
  refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
  rw [card_Ico_pow, nsmul_eq_mul, mul_comm, mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp),
    mul_one, ENNReal.mul_rpow_of_nonneg _ _ hq.le]
  rfl

/-- bloco `r`: `dterm (r+1) ≤ 2 (2^α)^q · ∑_{2^r ≤ N < 2^{r+1}} rterm N` -/
lemma dterm_succ_le (r : ℕ) :
    dterm α q H f (r + 1) ≤
      2 * ENNReal.ofReal (2 ^ α) ^ q * ∑ n ∈ Finset.Ico (2 ^ r) (2 ^ (r + 1)), rterm α q H f n := by
  set Y := (ENNReal.ofReal (((2 : ℝ) ^ r) ^ α) * pErr H (2 ^ (r + 1)) f) ^ q
  have hd : dterm α q H f (r + 1) = ENNReal.ofReal (2 ^ α) ^ q * Y := by
    unfold dterm
    rw [two_pow_rpow_succ α r, ENNReal.ofReal_mul (by positivity), mul_assoc,
      ENNReal.mul_rpow_of_nonneg _ _ hq.le]
  have hterm : ∀ n ∈ Finset.Ico (2 ^ r) (2 ^ (r + 1)), Y * ((2 ^ (r + 1) : ℕ) : ENNReal)⁻¹ ≤
      rterm α q H f n := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hn1 : ((2 : ℝ) ^ r) ≤ n := by exact_mod_cast hn.1
    exact mul_le_mul' (ENNReal.rpow_le_rpow (mul_le_mul'
      (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by positivity) hn1 hα.le))
      (pErr_antitone hH f hn.2.le)) hq.le) (ENNReal.inv_le_inv.mpr (by exact_mod_cast hn.2.le))
  have hsum := Finset.card_nsmul_le_sum _ _ _ hterm
  rw [card_Ico_pow, nsmul_eq_mul] at hsum
  -- `2^r · (2^{r+1})⁻¹ = 2⁻¹`
  have h2 : ((2 ^ r : ℕ) : ENNReal) * ((2 ^ (r + 1) : ℕ) : ENNReal)⁻¹ = 2⁻¹ := by
    rw [pow_succ, Nat.cast_mul, ENNReal.mul_inv (by simp) (by simp), ← mul_assoc,
      ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]
    norm_num
  have hY : Y ≤ 2 * ∑ n ∈ Finset.Ico (2 ^ r) (2 ^ (r + 1)), rterm α q H f n := by
    have e : 2 * (((2 ^ r : ℕ) : ENNReal) * (Y * ((2 ^ (r + 1) : ℕ) : ENNReal)⁻¹)) = Y := by
      calc _ = 2 * (((2 ^ r : ℕ) : ENNReal) * ((2 ^ (r + 1) : ℕ) : ENNReal)⁻¹) * Y := by ring
        _ = Y := by rw [h2, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
    calc Y = _ := e.symm
      _ ≤ _ := mul_le_mul_left' hsum 2
  rw [hd, mul_comm 2, mul_assoc]
  exact mul_le_mul_left' hY _

end bounds

/-- **Teorema IV.3.2 (redução exata às escalas diádicas)**, `0 < q < ∞`: com
`C = 2^α` e `K = (1 + 2·(2^α)^q)^{1/q}`, para toda agenda não decrescente e toda `f`,
`𝔞_{α,q}(f) ≤ C ‖(2^{rα}e_{2^r})‖_{ℓ^q}` e `‖(2^{rα}e_{2^r})‖_{ℓ^q} ≤ K 𝔞_{α,q}(f)`.
As constantes só dependem de `α, q`. -/
theorem dyadic_reduction {α q : ℝ} (hα : 0 < α) (hq : 0 < q) {H : ℕ → ℕ} (hH : Monotone H)
    (f : ℝ → ℝ) :
    rateQ α q H f ≤ ENNReal.ofReal (2 ^ α) * dyadQ α q H f ∧
    dyadQ α q H f ≤ (1 + 2 * ENNReal.ofReal (2 ^ α) ^ q) ^ (1 / q) * rateQ α q H f := by
  set A := ENNReal.ofReal (2 ^ α)
  set S := ∑' N : ℕ, rterm α q H f N
  set T := ∑' r : ℕ, dterm α q H f r
  have hS : S = ∑' r, ∑ n ∈ Finset.Ico (2 ^ r) (2 ^ (r + 1)), rterm α q H f n :=
    (tsum_blocks _ (rterm_zero hα hq H f)).symm
  have hq' : 0 ≤ 1 / q := by positivity
  constructor
  · -- `S ≤ A^q T`
    have h1 : S ≤ A ^ q * T := by
      rw [hS, ← ENNReal.tsum_mul_left]
      exact ENNReal.tsum_le_tsum fun r => block_le hα hq hH f r
    calc rateQ α q H f = S ^ (1 / q) := rfl
      _ ≤ (A ^ q * T) ^ (1 / q) := ENNReal.rpow_le_rpow h1 hq'
      _ = A * dyadQ α q H f := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hq', ← ENNReal.rpow_mul, mul_one_div_cancel hq.ne',
            ENNReal.rpow_one]
          rfl
  · -- `T ≤ (1 + 2 A^q) S`
    have ht0 : dterm α q H f 0 ≤ S := by
      have : dterm α q H f 0 = rterm α q H f 1 := by simp [dterm, rterm]
      rw [this]
      exact ENNReal.le_tsum 1
    have htail : ∑' r, dterm α q H f (r + 1) ≤ 2 * A ^ q * S := by
      rw [hS, ← ENNReal.tsum_mul_left]
      exact ENNReal.tsum_le_tsum fun r => dterm_succ_le hα hq hH f r
    have h2 : T ≤ (1 + 2 * A ^ q) * S := by
      rw [show T = dterm α q H f 0 + ∑' r, dterm α q H f (r + 1) from
        tsum_eq_zero_add' ENNReal.summable]
      rw [add_mul, one_mul]
      exact add_le_add ht0 htail
    calc dyadQ α q H f = T ^ (1 / q) := rfl
      _ ≤ ((1 + 2 * A ^ q) * S) ^ (1 / q) := ENNReal.rpow_le_rpow h2 hq'
      _ = (1 + 2 * A ^ q) ^ (1 / q) * rateQ α q H f := ENNReal.mul_rpow_of_nonneg _ _ hq'

/-- **Teorema IV.3.2**, `q = ∞`: `‖(2^{rα}e_{2^r})‖_{ℓ^∞} ≤ 𝔞_{α,∞}(f) ≤ 2^α ‖(2^{rα}e_{2^r})‖_{ℓ^∞}`. -/
theorem dyadic_reduction_inf {α : ℝ} (hα : 0 < α) {H : ℕ → ℕ} (hH : Monotone H) (f : ℝ → ℝ) :
    dyadInf α H f ≤ rateInf α H f ∧ rateInf α H f ≤ ENNReal.ofReal (2 ^ α) * dyadInf α H f := by
  constructor
  · refine iSup_le fun r => ?_
    have := le_iSup₂ (f := fun (N : ℕ) (_ : 1 ≤ N) => ENNReal.ofReal ((N : ℝ) ^ α) * pErr H N f)
      (2 ^ r) Nat.one_le_two_pow
    simpa using this
  · refine iSup₂_le fun N hN => ?_
    set r := Nat.log 2 N
    have h1 : 2 ^ r ≤ N := Nat.pow_log_le_self 2 (by omega)
    have h2 : N < 2 ^ (r + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
    have h2' : (N : ℝ) ≤ 2 ^ (r + 1) := by exact_mod_cast h2.le
    calc ENNReal.ofReal ((N : ℝ) ^ α) * pErr H N f
        ≤ ENNReal.ofReal (2 ^ α) * (ENNReal.ofReal (((2 : ℝ) ^ r) ^ α) * pErr H (2 ^ r) f) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← two_pow_rpow_succ α r]
          exact mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by positivity) h2' hα.le))
            (pErr_antitone hH f h1)
      _ ≤ ENNReal.ofReal (2 ^ α) * dyadInf α H f := by
          exact mul_le_mul_left'
            (le_iSup (fun r : ℕ => ENNReal.ofReal (((2 : ℝ) ^ r) ^ α) * pErr H (2 ^ r) f) r) _

/-! ## IV.3.3 -/

/-- o átomo `ℓ(x) = 1/2 + (x - 1/2) = x` em `J_{0,0}` -/
def atomId : Atom := ⟨0, 0, 1 / 2, 1, one_ne_zero⟩

lemma atomId_height : atomId.height = 2 := by simp [Atom.height, atomId, ht, one_div]; decide

lemma atomId_eval (x : ℝ) : (leaf atomId).eval 0 0 x = x := by
  simp [eval, atomId, Atom.eval, Atom.x0]

lemma distInf_eq_zero_iff {f g : ℝ → ℝ} : distInf f g = 0 ↔ ∀ x ∈ Icc (0 : ℝ) 1, f x = g x := by
  unfold distInf
  simp only [ENNReal.iSup_eq_zero, ENNReal.ofReal_eq_zero, abs_nonpos_iff, sub_eq_zero]

/-- `e_N(x) = 0` para todo `N ≥ 1` -/
lemma pErr_id {H : ℕ → ℕ} (hH : Monotone H) (h1 : 2 ≤ H 1) {N : ℕ} (hN : 1 ≤ N) :
    pErr H N (fun x => x) = 0 := by
  refine le_antisymm ?_ bot_le
  have hadm : AdmNH N (H N) (leaf atomId) := by
    refine ⟨by simp [WF, atomId], by simpa [numLeaves, leaves] using hN, ?_⟩
    simp only [maxHeight, leaves, List.foldr, atomId_height]
    have := hH hN
    omega
  calc pErr H N (fun x => x) ≤ distInf (fun x => x) ((leaf atomId).eval 0 0) :=
        by unfold pErr; exact iInf₂_le ((leaf atomId).eval 0 0) (Or.inr ⟨leaf atomId, hadm, rfl⟩)
    _ = 0 := distInf_eq_zero_iff.mpr fun x _ => (atomId_eval x).symm

/-- `e_1(√2 x) > 0` -/
lemma pErr_sqrt2_pos {H : ℕ → ℕ} (hH : Monotone H) :
    0 < pErr H 1 (fun x => Real.sqrt 2 * x) := by
  obtain ⟨-, -, -, g, hg, heq⟩ := schedule_nesting hH 1 (fun x => Real.sqrt 2 * x)
  rw [heq, pos_iff_ne_zero]
  intro h0
  have hx := distInf_eq_zero_iff.mp h0
  rcases hg with rfl | ⟨T, ⟨hw, hn, -⟩, rfl⟩
  · have := hx 1 ⟨zero_le_one, le_rfl⟩
    simp at this
  · cases T with
    | node l r =>
        have := numLeaves_pos l; have := numLeaves_pos r
        rw [numLeaves_node] at hn; omega
    | leaf a =>
        obtain ⟨hk, hm⟩ := hw
        have e0 := hx 0 ⟨le_rfl, zero_le_one⟩
        have e1 := hx 1 ⟨zero_le_one, le_rfl⟩
        simp only [eval, Atom.eval] at e0 e1
        have : Real.sqrt 2 = (a.s : ℝ) := by linear_combination e1 - e0
        exact irrational_sqrt_two ⟨a.s, this.symm⟩

/-- **Proposição IV.3.3 (falha exata de homogeneidade)**, `0 < q < ∞`: com `H(1) ≥ 2`,
`𝔞_{α,q}(x) = 0` e `𝔞_{α,q}(√2 x) > 0`. -/
theorem homogeneity_failure {α q : ℝ} (hα : 0 < α) (hq : 0 < q) {H : ℕ → ℕ} (hH : Monotone H)
    (h1 : 2 ≤ H 1) :
    rateQ α q H (fun x => x) = 0 ∧ 0 < rateQ α q H (fun x => Real.sqrt 2 * x) := by
  constructor
  · have : ∀ N, rterm α q H (fun x => x) N = 0 := by
      intro N
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · exact rterm_zero hα hq H _
      · simp [rterm, pErr_id hH h1 hN, ENNReal.zero_rpow_of_pos hq]
    simpa [rateQ, this] using hq
  · have hpos : 0 < rterm α q H (fun x => Real.sqrt 2 * x) 1 := by
      simp only [rterm, Nat.cast_one, Real.one_rpow, ENNReal.ofReal_one, one_mul, inv_one, mul_one]
      exact ENNReal.rpow_pos_of_nonneg (pErr_sqrt2_pos hH) hq.le
    exact ENNReal.rpow_pos_of_nonneg (hpos.trans_le (ENNReal.le_tsum 1)) (by positivity)

/-- **Proposição IV.3.3**, `q = ∞`. -/
theorem homogeneity_failure_inf {α : ℝ} {H : ℕ → ℕ} (hH : Monotone H) (h1 : 2 ≤ H 1) :
    rateInf α H (fun x => x) = 0 ∧ 0 < rateInf α H (fun x => Real.sqrt 2 * x) := by
  constructor
  · refine le_antisymm (iSup₂_le fun N hN => ?_) bot_le
    rw [pErr_id hH h1 hN, mul_zero]
  · refine lt_of_lt_of_le ?_ (le_iSup₂ (f := fun (N : ℕ) (_ : 1 ≤ N) =>
      ENNReal.ofReal ((N : ℝ) ^ α) * pErr H N (fun x => Real.sqrt 2 * x)) 1 le_rfl)
    simpa using pErr_sqrt2_pos hH

end Pendencias.Agenda
