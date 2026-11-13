import Pendencias.Jackson

/-!
# IV.4.2 (direção direta com altura aritmética) e IV.4.3 (imersões uniformes sobre bolas)

-- ITEM: IV.4.2
-- ITEM: IV.4.3

Sobre uma raiz diádica geral `K = J_{k₀,m₀}`:

* `SigmaK`, `pErrK`: o catálogo apontado `Σ_N^{𝓛,H}(K)` e o erro `e_N^{𝓛,H}(f)` da
  eq. (pointed-error); `rateInfK`, `rateQK`: o funcional de taxa `𝔞_{α,q}^{𝓛,H}`
  (eqs. rate-functional-finite/infty); `AclassInf`, `AclassQ`: os estratos
  `𝒜_q^α(𝓛,H) ⊂ C(K)` (eq. approximation-stratum);
* `HskK`: a agenda `H_{s,κ}` (eq. corrected-height-schedule); `HtilK`: a agenda com folga
  polinomial `H̃_{s,η}` (eq. polynomial-slack-schedule); `HhatK`: a agenda calibrada pela bola
  `Ĥ^{[B]}_{s,κ}` (eq. ball-calibrated-height-schedule), com a constante `A` do Lema IV.4.1.

Em `K = [0,1]` esses objetos coincidem com `Agenda.Sigma`, `pErr`, `rateInf`, `rateQ`, `Hsk`.
-/

namespace Pendencias.Jackson

open Set Artigo LTree Pendencias Pendencias.Agenda

/-! ## Catálogo apontado, erro e funcional de taxa sobre `K` -/

/-- `Σ_N^{𝓛,H}(K) = {0} ∪ 𝒜_{N,H(N)}(K)` -/
def SigmaK (k0 : ℕ) (m0 : ℤ) (H : ℕ → ℕ) (N : ℕ) : Set (ℝ → ℝ) :=
  {g | g = 0 ∨ ∃ T, AdmK k0 m0 N (H N) T ∧ g = T.eval k0 m0}

/-- erro apontado `e_N^{𝓛,H}(f) = inf_{g ∈ Σ_N} ‖f - g‖_{∞,K}` -/
noncomputable def pErrK (k0 : ℕ) (m0 : ℤ) (H : ℕ → ℕ) (N : ℕ) (f : ℝ → ℝ) : ENNReal :=
  ⨅ g ∈ SigmaK k0 m0 H N, distK k0 m0 f g

/-- `𝔞_{α,∞}^{𝓛,H}(f) = sup_{N ≥ 1} N^α e_N(f)` -/
noncomputable def rateInfK (k0 : ℕ) (m0 : ℤ) (α : ℝ) (H : ℕ → ℕ) (f : ℝ → ℝ) : ENNReal :=
  ⨆ N : ℕ, ⨆ (_ : 1 ≤ N), ENNReal.ofReal ((N : ℝ) ^ α) * pErrK k0 m0 H N f

/-- `𝔞_{α,q}^{𝓛,H}(f) = (∑_{N ≥ 1} [N^α e_N(f)]^q / N)^{1/q}`, `0 < q < ∞` (o termo `N = 0` é
nulo para `α, q > 0`) -/
noncomputable def rateQK (k0 : ℕ) (m0 : ℤ) (α q : ℝ) (H : ℕ → ℕ) (f : ℝ → ℝ) : ENNReal :=
  (∑' N : ℕ, (ENNReal.ofReal ((N : ℝ) ^ α) * pErrK k0 m0 H N f) ^ q * (N : ENNReal)⁻¹) ^ (1 / q)

/-- estrato `𝒜_∞^α(𝓛,H) = {f ∈ C(K) : 𝔞_{α,∞}(f) < ∞}` -/
def AclassInf (k0 : ℕ) (m0 : ℤ) (α : ℝ) (H : ℕ → ℕ) : Set (ℝ → ℝ) :=
  {f | ContinuousOn f (cellIcc k0 m0) ∧ rateInfK k0 m0 α H f < ⊤}

/-- estrato `𝒜_q^α(𝓛,H) = {f ∈ C(K) : 𝔞_{α,q}(f) < ∞}`, `0 < q < ∞` -/
def AclassQ (k0 : ℕ) (m0 : ℤ) (α q : ℝ) (H : ℕ → ℕ) : Set (ℝ → ℝ) :=
  {f | ContinuousOn f (cellIcc k0 m0) ∧ rateQK k0 m0 α q H f < ⊤}

lemma zero_mem_SigmaK (k0 : ℕ) (m0 : ℤ) (H : ℕ → ℕ) (N : ℕ) : (0 : ℝ → ℝ) ∈ SigmaK k0 m0 H N :=
  Or.inl rfl

lemma pErrK_le_dist0 (k0 : ℕ) (m0 : ℤ) (H : ℕ → ℕ) (N : ℕ) (f : ℝ → ℝ) :
    pErrK k0 m0 H N f ≤ distK k0 m0 f 0 :=
  iInf₂_le (0 : ℝ → ℝ) (zero_mem_SigmaK k0 m0 H N)

lemma pErrK_le_of_adm {k0 : ℕ} {m0 : ℤ} {H : ℕ → ℕ} {N : ℕ} {T : LTree}
    (hT : AdmK k0 m0 N (H N) T) (f : ℝ → ℝ) :
    pErrK k0 m0 H N f ≤ distK k0 m0 f (T.eval k0 m0) :=
  iInf₂_le (T.eval k0 m0) (Or.inr ⟨T, hT, rfl⟩)

lemma SigmaK_mono {k0 : ℕ} {m0 : ℤ} {H : ℕ → ℕ} (hH : Monotone H) {N M : ℕ} (hNM : N ≤ M) :
    SigmaK k0 m0 H N ⊆ SigmaK k0 m0 H M := by
  rintro g (rfl | ⟨T, ⟨hw, hn, hh⟩, rfl⟩)
  · exact Or.inl rfl
  · exact Or.inr ⟨T, ⟨hw, hn.trans hNM, hh.trans (hH hNM)⟩, rfl⟩

lemma pErrK_antitone {k0 : ℕ} {m0 : ℤ} {H : ℕ → ℕ} (hH : Monotone H) (f : ℝ → ℝ) :
    Antitone (fun N => pErrK k0 m0 H N f) := fun _ _ hNM =>
  biInf_mono fun _ hg => SigmaK_mono hH hNM hg

/-! ### Caso `K = [0,1]` -/

lemma SigmaK_zero (H : ℕ → ℕ) (N : ℕ) : SigmaK 0 0 H N = Sigma H N := rfl

lemma pErrK_zero (H : ℕ → ℕ) (N : ℕ) (f : ℝ → ℝ) : pErrK 0 0 H N f = pErr H N f := by
  unfold pErrK pErr; simp only [distK_zero, SigmaK_zero]

lemma rateInfK_zero (α : ℝ) (H : ℕ → ℕ) (f : ℝ → ℝ) : rateInfK 0 0 α H f = rateInf α H f := by
  unfold rateInfK rateInf; simp only [pErrK_zero]

lemma rateQK_zero (α q : ℝ) (H : ℕ → ℕ) (f : ℝ → ℝ) : rateQK 0 0 α q H f = rateQ α q H f := by
  unfold rateQK rateQ rterm; simp only [pErrK_zero]

/-! ## Redução às escalas diádicas (IV.3.2) para uma sequência não crescente qualquer -/

lemma block_le_gen {α q : ℝ} (hα : 0 < α) (hq : 0 < q) {e : ℕ → ENNReal} (he : Antitone e)
    (r : ℕ) :
    ∑ n ∈ Finset.Ico (2 ^ r : ℕ) (2 ^ (r + 1)),
        (ENNReal.ofReal ((n : ℝ) ^ α) * e n) ^ q * (n : ENNReal)⁻¹ ≤
      ENNReal.ofReal (2 ^ α) ^ q * (ENNReal.ofReal (((2 : ℝ) ^ r) ^ α) * e (2 ^ r)) ^ q := by
  have hterm : ∀ n ∈ Finset.Ico (2 ^ r : ℕ) (2 ^ (r + 1)),
      (ENNReal.ofReal ((n : ℝ) ^ α) * e n) ^ q * (n : ENNReal)⁻¹ ≤
        (ENNReal.ofReal (2 ^ α) * (ENNReal.ofReal (((2 : ℝ) ^ r) ^ α) * e (2 ^ r))) ^ q *
          ((2 ^ r : ℕ) : ENNReal)⁻¹ := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hn2 : (n : ℝ) ≤ 2 ^ (r + 1) := by exact_mod_cast hn.2.le
    have hA : ENNReal.ofReal ((n : ℝ) ^ α) * e n ≤
        ENNReal.ofReal (2 ^ α) * (ENNReal.ofReal (((2 : ℝ) ^ r) ^ α) * e (2 ^ r)) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← two_pow_rpow_succ α r]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by positivity) hn2 hα.le))
        (he hn.1)
    have hB : (n : ENNReal)⁻¹ ≤ ((2 ^ r : ℕ) : ENNReal)⁻¹ :=
      ENNReal.inv_le_inv.mpr (by exact_mod_cast hn.1)
    exact mul_le_mul' (ENNReal.rpow_le_rpow hA hq.le) hB
  refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans (le_of_eq ?_)
  rw [card_Ico_pow, nsmul_eq_mul, mul_comm, mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp),
    mul_one, ENNReal.mul_rpow_of_nonneg _ _ hq.le]

/-- `(∑_N [N^α e_N]^q/N)^{1/q} ≤ 2^α ‖(2^{rα} e_{2^r})_r‖_{ℓ^q}` -/
lemma rate_q_le_dyadic {α q : ℝ} (hα : 0 < α) (hq : 0 < q) {e : ℕ → ENNReal} (he : Antitone e) :
    (∑' N : ℕ, (ENNReal.ofReal ((N : ℝ) ^ α) * e N) ^ q * (N : ENNReal)⁻¹) ^ (1 / q) ≤
      ENNReal.ofReal (2 ^ α) *
        (∑' r : ℕ, (ENNReal.ofReal (((2 : ℝ) ^ r) ^ α) * e (2 ^ r)) ^ q) ^ (1 / q) := by
  have hz : (fun N : ℕ => (ENNReal.ofReal ((N : ℝ) ^ α) * e N) ^ q * (N : ENNReal)⁻¹) 0 = 0 := by
    simp [Real.zero_rpow hα.ne', ENNReal.zero_rpow_of_pos hq]
  have hq' : 0 ≤ 1 / q := by positivity
  have h1 : (∑' N : ℕ, (ENNReal.ofReal ((N : ℝ) ^ α) * e N) ^ q * (N : ENNReal)⁻¹) ≤
      ENNReal.ofReal (2 ^ α) ^ q *
        ∑' r : ℕ, (ENNReal.ofReal (((2 : ℝ) ^ r) ^ α) * e (2 ^ r)) ^ q := by
    rw [← tsum_blocks _ hz, ← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun r => block_le_gen hα hq he r
  calc _ ≤ (ENNReal.ofReal (2 ^ α) ^ q *
        ∑' r : ℕ, (ENNReal.ofReal (((2 : ℝ) ^ r) ^ α) * e (2 ^ r)) ^ q) ^ (1 / q) :=
        ENNReal.rpow_le_rpow h1 hq'
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hq', ← ENNReal.rpow_mul, mul_one_div_cancel hq.ne',
          ENNReal.rpow_one]

/-- `sup_{N≥1} N^α e_N ≤ 2^α sup_r 2^{rα} e_{2^r}` -/
lemma rate_inf_le_dyadic {α : ℝ} (hα : 0 < α) {e : ℕ → ENNReal} (he : Antitone e) :
    (⨆ N : ℕ, ⨆ (_ : 1 ≤ N), ENNReal.ofReal ((N : ℝ) ^ α) * e N) ≤
      ENNReal.ofReal (2 ^ α) * ⨆ r : ℕ, ENNReal.ofReal (((2 : ℝ) ^ r) ^ α) * e (2 ^ r) := by
  refine iSup₂_le fun N hN => ?_
  have h1 : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)
  have h2 : N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have h2' : (N : ℝ) ≤ 2 ^ (Nat.log 2 N + 1) := by exact_mod_cast h2.le
  calc ENNReal.ofReal ((N : ℝ) ^ α) * e N
      ≤ ENNReal.ofReal (2 ^ α) *
          (ENNReal.ofReal (((2 : ℝ) ^ Nat.log 2 N) ^ α) * e (2 ^ Nat.log 2 N)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← two_pow_rpow_succ α _]
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by positivity) h2' hα.le))
          (he h1)
    _ ≤ _ := mul_le_mul_right
        (le_iSup (fun r : ℕ => ENNReal.ofReal (((2 : ℝ) ^ r) ^ α) * e (2 ^ r)) _) _

/-! ## Lemas de sequências em `ENNReal` -/

lemma add_rpow_le (x y : ENNReal) {q : ℝ} (hq : 0 ≤ q) :
    (x + y) ^ q ≤ (2 : ENNReal) ^ q * (x ^ q + y ^ q) := by
  rcases le_total x y with h | h
  · calc (x + y) ^ q ≤ (2 * y) ^ q :=
          ENNReal.rpow_le_rpow (by rw [two_mul]; exact add_le_add h le_rfl) hq
      _ = 2 ^ q * y ^ q := ENNReal.mul_rpow_of_nonneg _ _ hq
      _ ≤ _ := mul_le_mul_right le_add_self _
  · calc (x + y) ^ q ≤ (2 * x) ^ q :=
          ENNReal.rpow_le_rpow (by rw [two_mul]; exact add_le_add le_rfl h) hq
      _ = 2 ^ q * x ^ q := ENNReal.mul_rpow_of_nonneg _ _ hq
      _ ≤ _ := mul_le_mul_right le_self_add _

lemma tsum_tail_le (u : ℕ → ENNReal) (r0 : ℕ) : ∑' i, u (i + r0) ≤ ∑' i, u i :=
  ENNReal.tsum_comp_le_tsum_of_injective (add_left_injective r0) u

/-- se `a_r ≤ c₁ t_r + c₂ γ_r` para `r ≥ r₀`, então
`∑ a_r^q ≤ ∑_{r<r₀} a_r^q + 2^q (c₁^q ∑ t_r^q + c₂^q ∑ γ_r^q)` -/
lemma tsum_rpow_le_of_tail {a t γ : ℕ → ENNReal} {c1 c2 : ENNReal} {q : ℝ} (hq : 0 < q) (r0 : ℕ)
    (h : ∀ r, r0 ≤ r → a r ≤ c1 * t r + c2 * γ r) :
    ∑' r, a r ^ q ≤ ∑ r ∈ Finset.range r0, a r ^ q +
      (2 : ENNReal) ^ q * (c1 ^ q * ∑' r, t r ^ q + c2 ^ q * ∑' r, γ r ^ q) := by
  have hsplit : ∑' r, a r ^ q = ∑ r ∈ Finset.range r0, a r ^ q + ∑' i, a (i + r0) ^ q :=
    (Summable.sum_add_tsum_nat_add' (f := fun r => a r ^ q) (k := r0) ENNReal.summable).symm
  refine le_of_eq_of_le hsplit (add_le_add le_rfl ?_)
  calc ∑' i, a (i + r0) ^ q
      ≤ ∑' i, (2 : ENNReal) ^ q * (c1 ^ q * t (i + r0) ^ q + c2 ^ q * γ (i + r0) ^ q) := by
        refine ENNReal.tsum_le_tsum fun i => ?_
        calc a (i + r0) ^ q ≤ (c1 * t (i + r0) + c2 * γ (i + r0)) ^ q :=
              ENNReal.rpow_le_rpow (h _ (Nat.le_add_left _ _)) hq.le
          _ ≤ 2 ^ q * ((c1 * t (i + r0)) ^ q + (c2 * γ (i + r0)) ^ q) := add_rpow_le _ _ hq.le
          _ = _ := by
              rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le, ENNReal.mul_rpow_of_nonneg _ _ hq.le]
    _ = 2 ^ q * (c1 ^ q * ∑' i, t (i + r0) ^ q + c2 ^ q * ∑' i, γ (i + r0) ^ q) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
    _ ≤ _ := by
        refine mul_le_mul_right (add_le_add (mul_le_mul_right ?_ _) (mul_le_mul_right ?_ _)) _
        · exact tsum_tail_le (fun r => t r ^ q) r0
        · exact tsum_tail_le (fun r => γ r ^ q) r0

/-! ## A sequência de quantização `γ_r = n^σ / [log(en)]^κ`, `n = 2^r` -/

/-- `γ_r = n^σ / [log(en)]^κ`, `n = 2^r` -/
noncomputable def gam (σ κ : ℝ) (r : ℕ) : ℝ :=
  ((2 : ℝ) ^ r) ^ σ / Real.log (Real.exp 1 * 2 ^ r) ^ κ

lemma log_e2r (r : ℕ) : Real.log (Real.exp 1 * 2 ^ r) = 1 + r * Real.log 2 := by
  rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp, Real.log_pow]

lemma one_le_log_e2r (r : ℕ) : 1 ≤ Real.log (Real.exp 1 * 2 ^ r) := by
  rw [log_e2r]
  have : 0 ≤ (r : ℝ) * Real.log 2 := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  linarith

lemma gam_nonneg (σ κ : ℝ) (r : ℕ) : 0 ≤ gam σ κ r := by
  unfold gam
  have := one_le_log_e2r r
  positivity

lemma two_pow_rpow_le_one {σ : ℝ} (hσ : σ ≤ 0) (r : ℕ) : ((2 : ℝ) ^ r) ^ σ ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (one_le_pow₀ (by norm_num)) hσ

lemma gam_le_pow {σ κ : ℝ} (hκ : 0 ≤ κ) (r : ℕ) : gam σ κ r ≤ ((2 : ℝ) ^ r) ^ σ := by
  unfold gam
  exact div_le_self (by positivity) (Real.one_le_rpow (one_le_log_e2r r) hκ)

lemma gam_le_one {σ κ : ℝ} (hσ : σ ≤ 0) (hκ : 0 ≤ κ) (r : ℕ) : gam σ κ r ≤ 1 :=
  (gam_le_pow hκ r).trans (two_pow_rpow_le_one hσ r)

/-- soma geométrica: `σ < 0` -/
lemma gam_sum_geom {σ κ q : ℝ} (hσ : σ < 0) (hκ : 0 ≤ κ) (hq : 0 < q) :
    ∑' r : ℕ, ENNReal.ofReal (gam σ κ r) ^ q < ⊤ := by
  set ρ := (2 : ℝ) ^ σ
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hσ
  have hρp : ENNReal.ofReal ρ ^ q < 1 := ENNReal.rpow_lt_one (by simpa using hρ1) hq
  have hterm : ∀ r : ℕ, ENNReal.ofReal (gam σ κ r) ^ q ≤ (ENNReal.ofReal ρ ^ q) ^ r := by
    intro r
    have e1 : ((2 : ℝ) ^ r) ^ σ = ρ ^ r := by
      simp only [ρ]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
        Real.rpow_mul (by norm_num), Real.rpow_natCast]
    calc ENNReal.ofReal (gam σ κ r) ^ q ≤ ENNReal.ofReal (ρ ^ r) ^ q :=
          ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (e1 ▸ gam_le_pow hκ r)) hq.le
      _ = (ENNReal.ofReal ρ ^ q) ^ r := by
          rw [ENNReal.ofReal_pow hρ0.le, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
            ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, mul_comm]
  refine lt_of_le_of_lt (ENNReal.tsum_le_tsum hterm) ?_
  rw [ENNReal.tsum_geometric]
  exact ENNReal.inv_lt_top.mpr (tsub_pos_of_lt hρp)

/-- soma logarítmica crítica: `σ ≤ 0` e `κ q > 1` -/
lemma gam_sum_log {σ κ q : ℝ} (hσ : σ ≤ 0) (hq : 0 < q) (hκq : 1 < κ * q) :
    ∑' r : ℕ, ENNReal.ofReal (gam σ κ r) ^ q < ⊤ := by
  have hκ : 0 < κ := by
    by_contra h
    have : κ * q ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) hq.le
    linarith
  set L := Real.log 2
  have hL0 : 0 < L := Real.log_pos (by norm_num)
  have hL1 : L ≤ 1 := by
    have := Real.log_two_lt_d9
    simp only [L]; linarith
  set h : ℕ → ℝ := fun r => (L ^ (κ * q))⁻¹ * (((r + 1 : ℕ) : ℝ) ^ (κ * q))⁻¹
  have hsum : Summable h :=
    ((summable_nat_add_iff 1).mpr (Real.summable_nat_rpow_inv.mpr hκq)).mul_left _
  have hterm : ∀ r : ℕ, ENNReal.ofReal (gam σ κ r) ^ q ≤ ENNReal.ofReal (h r) := by
    intro r
    rw [ENNReal.ofReal_rpow_of_nonneg (gam_nonneg σ κ r) hq.le]
    apply ENNReal.ofReal_le_ofReal
    have hlog := one_le_log_e2r r
    have hbase : ((r + 1 : ℕ) : ℝ) * L ≤ Real.log (Real.exp 1 * 2 ^ r) := by
      rw [log_e2r]; push_cast; nlinarith
    have hr1 : (0 : ℝ) < ((r + 1 : ℕ) : ℝ) := by positivity
    have h1 : gam σ κ r ≤ (Real.log (Real.exp 1 * 2 ^ r) ^ κ)⁻¹ := by
      unfold gam
      rw [div_eq_mul_inv]
      exact mul_le_of_le_one_left (by positivity) (two_pow_rpow_le_one hσ r)
    have h2 : (Real.log (Real.exp 1 * 2 ^ r) ^ κ)⁻¹ ≤ ((((r + 1 : ℕ) : ℝ) * L) ^ κ)⁻¹ :=
      inv_anti₀ (by positivity) (Real.rpow_le_rpow (by positivity) hbase hκ.le)
    calc gam σ κ r ^ q ≤ (((((r + 1 : ℕ) : ℝ) * L) ^ κ)⁻¹) ^ q :=
          Real.rpow_le_rpow (gam_nonneg σ κ r) (h1.trans h2) hq.le
      _ = h r := by
          simp only [h]
          rw [Real.inv_rpow (by positivity), ← Real.rpow_mul (by positivity),
            Real.mul_rpow hr1.le hL0.le, mul_inv, mul_comm]
  refine lt_of_le_of_lt (ENNReal.tsum_le_tsum hterm) ?_
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun r => by simp only [h]; positivity) hsum]
  exact ENNReal.ofReal_lt_top

/-! ## Agendas de altura -/

/-- forma comum das agendas: `⌈c (N+1)^ν [log(eN)]^κ⌉` -/
noncomputable def Hgen (c ν κ : ℝ) (N : ℕ) : ℕ :=
  ⌈c * ((N : ℝ) + 1) ^ ν * Real.log (Real.exp 1 * N) ^ κ⌉₊

/-- `H_{s,κ}(N) = ⌈C_K (N+1)^{ν_s} [log(eN)]^κ⌉` (eq. corrected-height-schedule) -/
noncomputable def HskK (k0 : ℕ) (m0 : ℤ) (s κ : ℝ) : ℕ → ℕ := Hgen (CK k0 m0) (max 1 s) κ

/-- `H̃_{s,η}(N) = ⌈C_K (N+1)^{max{1,s+η}}⌉` (eq. polynomial-slack-schedule) -/
noncomputable def HtilK (k0 : ℕ) (m0 : ℤ) (s η : ℝ) (N : ℕ) : ℕ :=
  ⌈CK k0 m0 * ((N : ℝ) + 1) ^ max 1 (s + η)⌉₊

/-- `Ĥ^{[B]}_{s,κ}(N) = ⌈A_{K,s}(B+1)(N+1)^{ν_s}[log(eN)]^κ⌉`
(eq. ball-calibrated-height-schedule), com `A_{K,s} = AK k₀ m₀` do Lema IV.4.1 -/
noncomputable def HhatK (k0 : ℕ) (m0 : ℤ) (B s κ : ℝ) : ℕ → ℕ :=
  Hgen (AK k0 m0 * (B + 1)) (max 1 s) κ

lemma HtilK_eq (k0 : ℕ) (m0 : ℤ) (s η : ℝ) :
    HtilK k0 m0 s η = Hgen (CK k0 m0) (max 1 (s + η)) 0 := by
  funext N; simp [HtilK, Hgen]

lemma HskK_zero (s κ : ℝ) : HskK 0 0 s κ = Hsk s κ := by
  funext N
  have : CK 0 0 = 8 := by unfold CK; norm_num
  simp [HskK, Hgen, Hsk, this]

lemma Hgen_mono {c ν κ : ℝ} (hc : 0 ≤ c) (hν : 0 ≤ ν) (hκ : 0 ≤ κ) : Monotone (Hgen c ν κ) := by
  intro N M hNM
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rcases Nat.eq_zero_or_pos M with rfl | hM
    · exact le_rfl
    apply Nat.ceil_mono
    have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have h1 : 1 ≤ ((M : ℝ) + 1) ^ ν := Real.one_le_rpow (by linarith) hν
    have h2 : 1 ≤ Real.log (Real.exp 1 * M) ^ κ := Real.one_le_rpow (log_eN_ge_one hM) hκ
    have h0 := Real.zero_rpow_le_one κ
    simp only [Nat.cast_zero, zero_add, Real.one_rpow, mul_one, mul_zero, Real.log_zero]
    calc c * (0 : ℝ) ^ κ ≤ c * 1 := mul_le_mul_of_nonneg_left h0 hc
      _ = c * 1 * 1 := by ring
      _ ≤ c * ((M : ℝ) + 1) ^ ν * Real.log (Real.exp 1 * M) ^ κ :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 hc) h2 zero_le_one
            (mul_nonneg hc (by positivity))
  · apply Nat.ceil_mono
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hNM' : (N : ℝ) ≤ M := by exact_mod_cast hNM
    have hl := log_eN_ge_one hN
    have hlm : Real.log (Real.exp 1 * N) ≤ Real.log (Real.exp 1 * M) :=
      Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left hNM' (Real.exp_pos 1).le)
    exact mul_le_mul (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (by linarith) hν) hc)
      (Real.rpow_le_rpow (by linarith) hlm hκ) (by positivity) (mul_nonneg hc (by positivity))

lemma Hgen_ge {c ν κ : ℝ} (hc : 0 ≤ c) (hκ : 0 ≤ κ) {N : ℕ} (hN : 1 ≤ N) :
    c * ((N : ℝ) + 1) ^ ν ≤ Hgen c ν κ N := by
  calc c * ((N : ℝ) + 1) ^ ν ≤ c * ((N : ℝ) + 1) ^ ν * Real.log (Real.exp 1 * N) ^ κ :=
        le_mul_of_one_le_right (mul_nonneg hc (by positivity))
          (Real.one_le_rpow (log_eN_ge_one hN) hκ)
    _ ≤ _ := Nat.le_ceil _

/-- `n^s / H(n) ≤ c⁻¹ γ_r` nas escalas diádicas `n = 2^r` -/
lemma ratio_le_gam {c ν κ : ℝ} (hc : 0 < c) (hν : 0 ≤ ν) (s : ℝ) (r : ℕ) :
    ((2 : ℝ) ^ r) ^ s / (Hgen c ν κ (2 ^ r) : ℝ) ≤ c⁻¹ * gam (s - ν) κ r := by
  have hn : (0 : ℝ) < 2 ^ r := by positivity
  have hlog := one_le_log_e2r r
  have hD : 0 < c * ((2 : ℝ) ^ r) ^ ν * Real.log (Real.exp 1 * 2 ^ r) ^ κ := by positivity
  have hH : c * ((2 : ℝ) ^ r) ^ ν * Real.log (Real.exp 1 * 2 ^ r) ^ κ ≤
      (Hgen c ν κ (2 ^ r) : ℝ) := by
    refine le_trans ?_ (Nat.le_ceil _)
    push_cast
    have : ((2 : ℝ) ^ r) ^ ν ≤ ((2 : ℝ) ^ r + 1) ^ ν :=
      Real.rpow_le_rpow hn.le (by linarith) hν
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hc.le) (by positivity)
  calc ((2 : ℝ) ^ r) ^ s / (Hgen c ν κ (2 ^ r) : ℝ)
      ≤ ((2 : ℝ) ^ r) ^ s / (c * ((2 : ℝ) ^ r) ^ ν * Real.log (Real.exp 1 * 2 ^ r) ^ κ) :=
        div_le_div_of_nonneg_left (by positivity) hD hH
    _ = c⁻¹ * gam (s - ν) κ r := by
        unfold gam
        rw [Real.rpow_sub hn]
        field_simp

/-- a agenda domina a geometria da malha uniforme (eq. height-geometry-condition) -/
lemma geo_of_ge {k0 r : ℕ} {m0 : ℤ} {Hn : ℕ} (h : CK k0 m0 * ((2 : ℝ) ^ r + 1) ≤ Hn) :
    2 ≤ Hn ∧ k0 + r + 1 ≤ Hn ∧
      ∀ j : ℤ, 0 ≤ j → j < 2 ^ r → (2 ^ r * m0 + j).natAbs + 1 ≤ Hn := by
  have hn1 : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
  have hm0 := abs_nonneg (m0 : ℝ)
  have hk : (0 : ℝ) ≤ k0 := Nat.cast_nonneg _
  have hexp : CK k0 m0 * ((2 : ℝ) ^ r + 1) =
      4 * (k0 * 2 ^ r) + 4 * k0 + 4 * (|(m0 : ℝ)| * 2 ^ r) + 4 * |(m0 : ℝ)| + 8 * 2 ^ r + 8 := by
    unfold CK; ring
  have hkn : (0 : ℝ) ≤ k0 * 2 ^ r := by positivity
  have hmn : (0 : ℝ) ≤ |(m0 : ℝ)| * 2 ^ r := by positivity
  refine ⟨?_, ?_, ?_⟩
  · have : (2 : ℝ) ≤ Hn := by linarith
    exact_mod_cast this
  · have a2 : ((r + 1 : ℕ) : ℝ) ≤ 2 ^ r := by exact_mod_cast (Nat.lt_two_pow_self (n := r))
    have : ((k0 + r + 1 : ℕ) : ℝ) ≤ Hn := by
      push_cast at a2 ⊢; linarith
    exact_mod_cast this
  · intro j hj0 hj1
    have hj0' : (0 : ℝ) ≤ j := by exact_mod_cast hj0
    have hj1' : (j : ℝ) < 2 ^ r := by exact_mod_cast hj1
    have habs : |((2 ^ r * m0 + j : ℤ) : ℝ)| ≤ 2 ^ r * |(m0 : ℝ)| + 2 ^ r := by
      push_cast
      calc |(2 : ℝ) ^ r * m0 + j| ≤ |(2 : ℝ) ^ r * m0| + |(j : ℝ)| := abs_add_le _ _
        _ ≤ 2 ^ r * |(m0 : ℝ)| + 2 ^ r := by
          rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ r), abs_of_nonneg hj0']
          linarith
    have : (((2 ^ r * m0 + j).natAbs + 1 : ℕ) : ℝ) ≤ Hn := by
      push_cast
      rw [Nat.cast_natAbs, Int.cast_abs]
      linarith
    exact_mod_cast this

/-! ## Cota nas escalas diádicas -/

/-- o termo diádico `2^{rs} e_{2^r}^{𝓛,H}(f)` -/
noncomputable def dK (k0 : ℕ) (m0 : ℤ) (s : ℝ) (H : ℕ → ℕ) (f : ℝ → ℝ) (r : ℕ) : ENNReal :=
  ENNReal.ofReal (((2 : ℝ) ^ r) ^ s) * pErrK k0 m0 H (2 ^ r) f

lemma scale_bound {P D Hn : ℝ} (hP : 0 ≤ P) (hD : 0 ≤ D) {X c ω : ENNReal}
    (h : X ≤ c * ω + ENNReal.ofReal (D / Hn)) :
    ENNReal.ofReal P * X ≤
      c * (ENNReal.ofReal P * ω) + ENNReal.ofReal D * ENNReal.ofReal (P / Hn) := by
  calc ENNReal.ofReal P * X ≤ ENNReal.ofReal P * (c * ω + ENNReal.ofReal (D / Hn)) :=
        mul_le_mul_right h _
    _ = c * (ENNReal.ofReal P * ω) + ENNReal.ofReal D * ENNReal.ofReal (P / Hn) := by
        rw [mul_add, mul_left_comm, ← ENNReal.ofReal_mul hP, ← ENNReal.ofReal_mul hD]
        congr 2; ring

lemma dK_le_dist {k0 : ℕ} {m0 : ℤ} {s : ℝ} (hs : 0 ≤ s) (H : ℕ → ℕ) (f : ℝ → ℝ) {r r0 : ℕ}
    (hr : r ≤ r0) :
    dK k0 m0 s H f r ≤ ENNReal.ofReal (((2 : ℝ) ^ r0) ^ s) * distK k0 m0 f 0 :=
  mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by positivity)
    (pow_le_pow_right₀ (by norm_num) hr) hs)) (pErrK_le_dist0 k0 m0 H _ f)

/-- Lema IV.4.1 aplicado a uma agenda que domina `C_K (N+1)^{ν_s}` -/
lemma adm_dyadic_bound {k0 : ℕ} {m0 : ℤ} {s : ℝ} {f : ℝ → ℝ} {CW : ℝ} (hs : 0 < s)
    (hs2 : s < 2) (hB : BesovInfK k0 m0 s f) (hW : IsWhitney CW) {H : ℕ → ℕ}
    (hH : ∀ N : ℕ, 1 ≤ N → CK k0 m0 * ((N : ℝ) + 1) ^ max 1 s ≤ H N) :
    ∃ (C : ℝ) (r0 : ℕ), 0 < C ∧ ∀ r, r0 ≤ r → ∃ T, AdmK k0 m0 (2 ^ r) (H (2 ^ r)) T ∧
      distK k0 m0 f (T.eval k0 m0) ≤
        ENNReal.ofReal (2 * CW) * omega2K k0 m0 f ((2 : ℝ) ^ (k0 + r))⁻¹ +
          ENNReal.ofReal (C * ((distK k0 m0 f 0).toReal + 1) / H (2 ^ r)) := by
  obtain ⟨C, hC, h⟩ := rational_jackson_height
  obtain ⟨n0, hn0⟩ := h k0 m0 s f CW hs hs2 hB hW
  have hR : 0 ≤ (distK k0 m0 f 0).toReal := ENNReal.toReal_nonneg
  refine ⟨C, max n0 ⌈2 * ((distK k0 m0 f 0).toReal + 1)⌉₊, hC, fun r hr => ?_⟩
  have hr2 : r < 2 ^ r := Nat.lt_two_pow_self
  have hn : n0 ≤ 2 ^ r := ((le_max_left _ _).trans hr).trans hr2.le
  have hRr : 2 * ((distK k0 m0 f 0).toReal + 1) ≤ (2 : ℝ) ^ r := by
    have h1 : ⌈2 * ((distK k0 m0 f 0).toReal + 1)⌉₊ ≤ 2 ^ r :=
      ((le_max_right _ _).trans hr).trans hr2.le
    have h2 : ((⌈2 * ((distK k0 m0 f 0).toReal + 1)⌉₊ : ℕ) : ℝ) ≤ ((2 ^ r : ℕ) : ℝ) := by
      exact_mod_cast h1
    push_cast at h2
    exact (Nat.le_ceil _).trans h2
  have hHr := hH (2 ^ r) Nat.one_le_two_pow
  push_cast at hHr
  have hn1 : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
  have hCK := CK_ge k0 m0
  have hmax : (0 : ℝ) ≤ max 1 s := le_trans zero_le_one (le_max_left _ _)
  have hν1 : (2 : ℝ) ^ r + 1 ≤ ((2 : ℝ) ^ r + 1) ^ max 1 s :=
    Real.self_le_rpow_of_one_le (by linarith) (le_max_left _ _)
  have hνn : ((2 : ℝ) ^ r) ^ max 1 s ≤ ((2 : ℝ) ^ r + 1) ^ max 1 s :=
    Real.rpow_le_rpow (by positivity) (by linarith) hmax
  have hgeoH : CK k0 m0 * ((2 : ℝ) ^ r + 1) ≤ H (2 ^ r) :=
    (mul_le_mul_of_nonneg_left hν1 (by linarith)).trans hHr
  have h8 : 8 * ((2 : ℝ) ^ r + 1) ≤ CK k0 m0 * ((2 : ℝ) ^ r + 1) :=
    mul_le_mul_of_nonneg_right hCK (by positivity)
  exact hn0 r hn (H (2 ^ r))
    (max_le ((mul_le_mul_of_nonneg_left hνn (by linarith)).trans hHr) (by linarith))
    (geo_of_ge hgeoH)

lemma pErrK_dyadic_bound {k0 : ℕ} {m0 : ℤ} {s : ℝ} {f : ℝ → ℝ} {CW : ℝ} (hs : 0 < s)
    (hs2 : s < 2) (hB : BesovInfK k0 m0 s f) (hW : IsWhitney CW) {H : ℕ → ℕ}
    (hH : ∀ N : ℕ, 1 ≤ N → CK k0 m0 * ((N : ℝ) + 1) ^ max 1 s ≤ H N) :
    ∃ (C : ℝ) (r0 : ℕ), 0 < C ∧ ∀ r, r0 ≤ r →
      pErrK k0 m0 H (2 ^ r) f ≤
        ENNReal.ofReal (2 * CW) * omega2K k0 m0 f ((2 : ℝ) ^ (k0 + r))⁻¹ +
          ENNReal.ofReal (C * ((distK k0 m0 f 0).toReal + 1) / H (2 ^ r)) := by
  obtain ⟨C, r0, hC, h⟩ := adm_dyadic_bound hs hs2 hB hW hH
  refine ⟨C, r0, hC, fun r hr => ?_⟩
  obtain ⟨T, hT, hd⟩ := h r hr
  exact (pErrK_le_of_adm hT f).trans hd

/-- cota de cauda para as agendas `Hgen c ν κ` com `c ≥ C_K`, `ν ≥ ν_s` -/
lemma dK_tail_bound {k0 : ℕ} {m0 : ℤ} {s : ℝ} {f : ℝ → ℝ} (hs : 0 < s) (hs2 : s < 2)
    (hB : BesovInfK k0 m0 s f) {c ν κ : ℝ} (hc : CK k0 m0 ≤ c) (hν : max 1 s ≤ ν) (hκ : 0 ≤ κ) :
    ∃ (D : ℝ) (r0 : ℕ), 0 ≤ D ∧ ∀ r, r0 ≤ r →
      dK k0 m0 s (Hgen c ν κ) f r ≤ ENNReal.ofReal 2 * btermK k0 m0 s f r +
        ENNReal.ofReal D * ENNReal.ofReal (gam (s - ν) κ r) := by
  have hCK := CK_ge k0 m0
  have hc0 : 0 < c := by linarith
  have hν0 : 0 ≤ ν := le_trans (le_trans zero_le_one (le_max_left _ _)) hν
  have hH : ∀ N : ℕ, 1 ≤ N → CK k0 m0 * ((N : ℝ) + 1) ^ max 1 s ≤ Hgen c ν κ N := by
    intro N hN
    have hN' : (1 : ℝ) ≤ (N : ℝ) + 1 := by
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg _
      linarith
    calc CK k0 m0 * ((N : ℝ) + 1) ^ max 1 s ≤ c * ((N : ℝ) + 1) ^ ν :=
          mul_le_mul hc (Real.rpow_le_rpow_of_exponent_le hN' hν) (by positivity) hc0.le
      _ ≤ _ := Hgen_ge hc0.le hκ hN
  obtain ⟨C, r0, hC, hb⟩ := pErrK_dyadic_bound hs hs2 hB whitney_one hH
  have hR : 0 ≤ (distK k0 m0 f 0).toReal := ENNReal.toReal_nonneg
  refine ⟨C * ((distK k0 m0 f 0).toReal + 1) * c⁻¹, r0, by positivity, fun r hr => ?_⟩
  have h1 := scale_bound (P := ((2 : ℝ) ^ r) ^ s) (by positivity)
    (by positivity : 0 ≤ C * ((distK k0 m0 f 0).toReal + 1)) (hb r hr)
  rw [mul_one] at h1
  refine h1.trans (add_le_add le_rfl ?_)
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc C * ((distK k0 m0 f 0).toReal + 1) * (((2 : ℝ) ^ r) ^ s / (Hgen c ν κ (2 ^ r) : ℝ))
      ≤ C * ((distK k0 m0 f 0).toReal + 1) * (c⁻¹ * gam (s - ν) κ r) :=
        mul_le_mul_of_nonneg_left (ratio_le_gam hc0 hν0 s r) (by positivity)
    _ = _ := by ring

/-! ## Besov: relações entre `q < ∞` e `q = ∞` -/

lemma btermK_le_tsum {k0 : ℕ} {m0 : ℤ} {s q : ℝ} (hq : 0 < q) (f : ℝ → ℝ) (r : ℕ) :
    btermK k0 m0 s f r ≤ (∑' r : ℕ, btermK k0 m0 s f r ^ q) ^ (1 / q) := by
  calc btermK k0 m0 s f r = (btermK k0 m0 s f r ^ q) ^ (1 / q) := by
        rw [← ENNReal.rpow_mul, mul_one_div_cancel hq.ne', ENNReal.rpow_one]
    _ ≤ _ := ENNReal.rpow_le_rpow (ENNReal.le_tsum r) (by positivity)

lemma bnormInf_le_bnormQ {k0 : ℕ} {m0 : ℤ} {s q : ℝ} (hq : 0 < q) (f : ℝ → ℝ) :
    bnormInf k0 m0 s f ≤ bnormQ k0 m0 s q f :=
  add_le_add le_rfl (iSup_le fun r => btermK_le_tsum hq f r)

lemma BesovQK.toInf {k0 : ℕ} {m0 : ℤ} {s q : ℝ} (hq : 0 < q) {f : ℝ → ℝ}
    (h : BesovQK k0 m0 s q f) : BesovInfK k0 m0 s f :=
  ⟨h.1, lt_of_le_of_lt (bnormInf_le_bnormQ hq f) h.2⟩

lemma tsum_bterm_le {k0 : ℕ} {m0 : ℤ} {s q : ℝ} (hq : 0 < q) {f : ℝ → ℝ} {X : ENNReal}
    (h : bnormQ k0 m0 s q f ≤ X) : ∑' r : ℕ, btermK k0 m0 s f r ^ q ≤ X ^ q := by
  have h1 : (∑' r : ℕ, btermK k0 m0 s f r ^ q) ^ (1 / q) ≤ X := le_trans le_add_self h
  have h2 := ENNReal.rpow_le_rpow h1 hq.le
  rwa [← ENNReal.rpow_mul, one_div_mul_cancel hq.ne', ENNReal.rpow_one] at h2

/-! ## Teorema IV.4.2 -/

lemma dK_lt_top {k0 : ℕ} {m0 : ℤ} {s : ℝ} (hs : 0 ≤ s) (H : ℕ → ℕ) {f : ℝ → ℝ}
    (hd : distK k0 m0 f 0 < ⊤) (r : ℕ) : dK k0 m0 s H f r < ⊤ :=
  lt_of_le_of_lt (dK_le_dist hs H f le_rfl) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hd)

lemma direct_generic_inf {k0 : ℕ} {m0 : ℤ} {s : ℝ} {f : ℝ → ℝ} (hs : 0 < s) (hs2 : s < 2)
    (hB : BesovInfK k0 m0 s f) {c ν κ : ℝ} (hc : CK k0 m0 ≤ c) (hν : max 1 s ≤ ν) (hκ : 0 ≤ κ) :
    rateInfK k0 m0 s (Hgen c ν κ) f < ⊤ := by
  have hCK := CK_ge k0 m0
  have hν0 : 0 ≤ ν := le_trans (le_trans zero_le_one (le_max_left _ _)) hν
  have hmono : Monotone (Hgen c ν κ) := Hgen_mono (by linarith) hν0 hκ
  have hred := rate_inf_le_dyadic hs (pErrK_antitone (k0 := k0) (m0 := m0) hmono f)
  have hdfin : distK k0 m0 f 0 < ⊤ := lt_of_le_of_lt le_self_add hB.2
  have hbfin : ⨆ r, btermK k0 m0 s f r < ⊤ := lt_of_le_of_lt le_add_self hB.2
  obtain ⟨D, r0, hD, htail⟩ := dK_tail_bound hs hs2 hB hc hν hκ
  have hsup : ⨆ r, dK k0 m0 s (Hgen c ν κ) f r ≤
      ENNReal.ofReal (((2 : ℝ) ^ r0) ^ s) * distK k0 m0 f 0 +
        (ENNReal.ofReal 2 * (⨆ r, btermK k0 m0 s f r) + ENNReal.ofReal D) := by
    refine iSup_le fun r => ?_
    rcases le_total r r0 with h | h
    · exact (dK_le_dist hs.le _ f h).trans le_self_add
    · refine ((htail r h).trans (add_le_add (mul_le_mul_right (le_iSup _ r) _) ?_)).trans
        le_add_self
      calc ENNReal.ofReal D * ENNReal.ofReal (gam (s - ν) κ r) ≤ ENNReal.ofReal D * 1 :=
            mul_le_mul_right (ENNReal.ofReal_le_one.mpr
              (gam_le_one (by linarith [le_max_right 1 s]) hκ r)) _
        _ = ENNReal.ofReal D := mul_one _
  unfold rateInfK
  refine lt_of_le_of_lt hred (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_of_le_of_lt hsup ?_))
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hdfin,
    ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hbfin, ENNReal.ofReal_lt_top⟩⟩

lemma direct_generic_Q {k0 : ℕ} {m0 : ℤ} {s q : ℝ} {f : ℝ → ℝ} (hs : 0 < s) (hs2 : s < 2)
    (hq : 0 < q) (hB : BesovQK k0 m0 s q f) {c ν κ : ℝ} (hc : CK k0 m0 ≤ c) (hν : max 1 s ≤ ν)
    (hκ : 0 ≤ κ) (hsum : ∑' r : ℕ, ENNReal.ofReal (gam (s - ν) κ r) ^ q < ⊤) :
    rateQK k0 m0 s q (Hgen c ν κ) f < ⊤ := by
  have hCK := CK_ge k0 m0
  have hν0 : 0 ≤ ν := le_trans (le_trans zero_le_one (le_max_left _ _)) hν
  have hmono : Monotone (Hgen c ν κ) := Hgen_mono (by linarith) hν0 hκ
  have hred := rate_q_le_dyadic hs hq (pErrK_antitone (k0 := k0) (m0 := m0) hmono f)
  have hBinf := hB.toInf hq
  have hdfin : distK k0 m0 f 0 < ⊤ := lt_of_le_of_lt le_self_add hB.2
  have htfin : ∑' r : ℕ, btermK k0 m0 s f r ^ q < ⊤ := by
    have h1 : (∑' r : ℕ, btermK k0 m0 s f r ^ q) ^ (1 / q) < ⊤ :=
      lt_of_le_of_lt le_add_self hB.2
    have := ENNReal.rpow_lt_top_of_nonneg hq.le h1.ne
    rwa [← ENNReal.rpow_mul, one_div_mul_cancel hq.ne', ENNReal.rpow_one] at this
  obtain ⟨D, r0, hD, htail⟩ := dK_tail_bound hs hs2 hBinf hc hν hκ
  have hS := tsum_rpow_le_of_tail (a := dK k0 m0 s (Hgen c ν κ) f) hq r0 htail
  have h2q : (2 : ENNReal) ^ q < ⊤ := ENNReal.rpow_lt_top_of_nonneg hq.le (by norm_num)
  have hfin : ∑' r, dK k0 m0 s (Hgen c ν κ) f r ^ q < ⊤ := by
    refine lt_of_le_of_lt hS (ENNReal.add_lt_top.mpr ⟨?_, ?_⟩)
    · exact ENNReal.sum_lt_top.mpr fun r _ =>
        ENNReal.rpow_lt_top_of_nonneg hq.le (dK_lt_top hs.le _ hdfin r).ne
    · exact ENNReal.mul_lt_top h2q (ENNReal.add_lt_top.mpr
        ⟨ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hq.le ENNReal.ofReal_ne_top) htfin,
          ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hq.le ENNReal.ofReal_ne_top) hsum⟩)
  unfold rateQK
  exact lt_of_le_of_lt hred (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by positivity) hfin.ne))

/-- `B^s_{∞,∞}(K)` como conjunto -/
def BesovInfSet (k0 : ℕ) (m0 : ℤ) (s : ℝ) : Set (ℝ → ℝ) := {f | BesovInfK k0 m0 s f}

/-- `B^s_{∞,q}(K)`, `0 < q < ∞`, como conjunto -/
def BesovQSet (k0 : ℕ) (m0 : ℤ) (s q : ℝ) : Set (ℝ → ℝ) := {f | BesovQK k0 m0 s q f}

/-- **Teorema IV.4.2 (direção direta com altura aritmética).** Para `0 < s < 2`:
`B^s_{∞,∞}(K) ⊂ 𝒜^s_∞(𝓛,H_{s,0})`; `B^s_{∞,q}(K) ⊂ 𝒜^s_q(𝓛,H_{s,0})` para `0 < q < ∞`,
`0 < s < 1`; `B^s_{∞,q}(K) ⊂ 𝒜^s_q(𝓛,H_{s,κ})` para `0 < q < ∞`, `1 ≤ s < 2`, `κ > 1/q`; e,
como alternativa sem logaritmo, o mesmo com `H̃_{s,η}`, `η > 0`, no lugar de `H_{s,κ}`. -/
theorem direct_besov_height (k0 : ℕ) (m0 : ℤ) {s : ℝ} (hs : 0 < s) (hs2 : s < 2) :
    BesovInfSet k0 m0 s ⊆ AclassInf k0 m0 s (HskK k0 m0 s 0) ∧
    (∀ q : ℝ, 0 < q → s < 1 →
      BesovQSet k0 m0 s q ⊆ AclassQ k0 m0 s q (HskK k0 m0 s 0)) ∧
    (∀ q κ : ℝ, 0 < q → 1 ≤ s → 1 / q < κ →
      BesovQSet k0 m0 s q ⊆ AclassQ k0 m0 s q (HskK k0 m0 s κ)) ∧
    (∀ q η : ℝ, 0 < q → 1 ≤ s → 0 < η →
      BesovQSet k0 m0 s q ⊆ AclassQ k0 m0 s q (HtilK k0 m0 s η)) := by
  refine ⟨fun f hf => ⟨hf.1, direct_generic_inf hs hs2 hf le_rfl le_rfl le_rfl⟩,
    fun q hq hs1 f hf => ⟨hf.1, ?_⟩, fun q κ hq hs1 hκ f hf => ⟨hf.1, ?_⟩,
    fun q η hq hs1 hη f hf => ⟨hf.1, ?_⟩⟩
  · exact direct_generic_Q hs hs2 hq hf le_rfl le_rfl le_rfl
      (gam_sum_geom (by rw [max_eq_left hs1.le]; linarith) le_rfl hq)
  · have hκ0 : 0 < κ := lt_trans (by positivity) hκ
    exact direct_generic_Q hs hs2 hq hf le_rfl le_rfl hκ0.le
      (gam_sum_log (by rw [max_eq_right hs1]; linarith) hq ((div_lt_iff₀ hq).mp hκ))
  · rw [HtilK_eq]
    exact direct_generic_Q hs hs2 hq hf le_rfl (max_le_max le_rfl (by linarith)) le_rfl
      (gam_sum_geom (by have := le_max_right 1 (s + η); linarith) le_rfl hq)

/-! ## Corolário IV.4.3 -/

lemma AK_ge (k0 : ℕ) (m0 : ℤ) : 1 ≤ AK k0 m0 := (rational_jackson_uniform_explicit k0 m0).1

lemma dK_ball_bound {k0 : ℕ} {m0 : ℤ} {s : ℝ} {f : ℝ → ℝ} {B κ : ℝ} (hs : 0 < s) (hs2 : s < 2)
    (hB1 : 1 ≤ B) (hfc : ContinuousOn f (cellIcc k0 m0))
    (hnorm : bnormInf k0 m0 s f ≤ ENNReal.ofReal B) (hκ : 0 ≤ κ) {r : ℕ} (hr : 1 ≤ r) :
    dK k0 m0 s (HhatK k0 m0 B s κ) f r ≤ ENNReal.ofReal 2 * btermK k0 m0 s f r +
      ENNReal.ofReal 8 * ENNReal.ofReal (gam (s - max 1 s) κ r) := by
  obtain ⟨hA1, hA⟩ := rational_jackson_uniform_explicit k0 m0
  have hA0 : 0 < AK k0 m0 := by linarith
  have hc0 : 0 < AK k0 m0 * (B + 1) := mul_pos hA0 (by linarith)
  have hmax : (0 : ℝ) ≤ max 1 s := le_trans zero_le_one (le_max_left _ _)
  have hHr : AK k0 m0 * (B + 1) * ((2 : ℝ) ^ r) ^ max 1 s ≤
      (HhatK k0 m0 B s κ (2 ^ r) : ℝ) := by
    have h1 := Hgen_ge (c := AK k0 m0 * (B + 1)) (ν := max 1 s) hc0.le hκ (N := 2 ^ r)
      Nat.one_le_two_pow
    push_cast at h1
    exact le_trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (by linarith) hmax) hc0.le) h1
  obtain ⟨-, T, hT, hd⟩ := hA s f 1 B hs hs2 whitney_one hB1 hfc hnorm r hr _ hHr
  have hp := (pErrK_le_of_adm (H := HhatK k0 m0 B s κ) hT f).trans hd
  have h1 := scale_bound (P := ((2 : ℝ) ^ r) ^ s) (by positivity)
    (by positivity : (0 : ℝ) ≤ 8 * (B + 1)) hp
  rw [mul_one] at h1
  refine h1.trans (add_le_add le_rfl ?_)
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  have hg := gam_nonneg (s - max 1 s) κ r
  have hinv : (AK k0 m0)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hA1
  calc 8 * (B + 1) * (((2 : ℝ) ^ r) ^ s / (HhatK k0 m0 B s κ (2 ^ r) : ℝ))
      ≤ 8 * (B + 1) * ((AK k0 m0 * (B + 1))⁻¹ * gam (s - max 1 s) κ r) :=
        mul_le_mul_of_nonneg_left (ratio_le_gam hc0 hmax s r) (by positivity)
    _ = 8 * ((AK k0 m0)⁻¹ * gam (s - max 1 s) κ r) := by
        have : B + 1 ≠ 0 := by linarith
        field_simp
    _ ≤ 8 * gam (s - max 1 s) κ r := by nlinarith [mul_le_mul_of_nonneg_right hinv hg]

lemma HhatK_mono (k0 : ℕ) (m0 : ℤ) {B κ : ℝ} (hB : 0 ≤ B) (s : ℝ) (hκ : 0 ≤ κ) :
    Monotone (HhatK k0 m0 B s κ) :=
  Hgen_mono (mul_nonneg (by linarith [AK_ge k0 m0]) (by linarith))
    (le_trans zero_le_one (le_max_left _ _)) hκ

lemma ball_generic_Q {k0 : ℕ} {m0 : ℤ} {s q κ : ℝ} (hs : 0 < s) (hs2 : s < 2) (hq : 0 < q)
    (hκ : 0 ≤ κ) (hsum : ∑' r : ℕ, ENNReal.ofReal (gam (s - max 1 s) κ r) ^ q < ⊤) :
    ∃ C : ℝ, ∀ (B : ℝ) (f : ℝ → ℝ), 1 ≤ B → ContinuousOn f (cellIcc k0 m0) →
      bnormQ k0 m0 s q f ≤ ENNReal.ofReal B →
      rateQK k0 m0 s q (HhatK k0 m0 B s κ) f ≤ ENNReal.ofReal (C * (B + 1)) := by
  have h2q : (2 : ENNReal) ^ q < ⊤ := ENNReal.rpow_lt_top_of_nonneg hq.le (by norm_num)
  have hMq : (1 + (2 : ENNReal) ^ q * (ENNReal.ofReal 2 ^ q + ENNReal.ofReal 8 ^ q *
      ∑' r : ℕ, ENNReal.ofReal (gam (s - max 1 s) κ r) ^ q)) ^ (1 / q) < ⊤ := by
    refine ENNReal.rpow_lt_top_of_nonneg (by positivity) (ENNReal.add_lt_top.mpr
      ⟨ENNReal.one_lt_top, ENNReal.mul_lt_top h2q (ENNReal.add_lt_top.mpr
        ⟨ENNReal.rpow_lt_top_of_nonneg hq.le ENNReal.ofReal_ne_top,
          ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hq.le ENNReal.ofReal_ne_top)
            hsum⟩)⟩).ne
  refine ⟨2 ^ s * ((1 + (2 : ENNReal) ^ q * (ENNReal.ofReal 2 ^ q + ENNReal.ofReal 8 ^ q *
      ∑' r : ℕ, ENNReal.ofReal (gam (s - max 1 s) κ r) ^ q)) ^ (1 / q)).toReal,
    fun B f hB1 hfc hnorm => ?_⟩
  have hB0 : 0 ≤ B := by linarith
  have hred := rate_q_le_dyadic hs hq
    (pErrK_antitone (k0 := k0) (m0 := m0) (HhatK_mono k0 m0 hB0 s hκ) f)
  have hninf : bnormInf k0 m0 s f ≤ ENNReal.ofReal B := (bnormInf_le_bnormQ hq f).trans hnorm
  have hS := tsum_rpow_le_of_tail (a := dK k0 m0 s (HhatK k0 m0 B s κ) f) hq 1
    (fun r hr => dK_ball_bound hs hs2 hB1 hfc hninf hκ hr)
  rw [Finset.sum_range_one] at hS
  have hd0 : dK k0 m0 s (HhatK k0 m0 B s κ) f 0 ≤ ENNReal.ofReal B := by
    refine (dK_le_dist hs.le _ f le_rfl).trans ?_
    simp only [pow_zero, Real.one_rpow, ENNReal.ofReal_one, one_mul]
    exact le_self_add.trans hnorm
  have ht := tsum_bterm_le hq hnorm
  have hBY : ENNReal.ofReal B ^ q ≤ ENNReal.ofReal (B + 1) ^ q :=
    ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (by linarith)) hq.le
  have hY1 : 1 ≤ ENNReal.ofReal (B + 1) ^ q :=
    ENNReal.one_le_rpow (ENNReal.one_le_ofReal.mpr (by linarith)) hq
  have hfin : ∑' r, dK k0 m0 s (HhatK k0 m0 B s κ) f r ^ q ≤
      ENNReal.ofReal (B + 1) ^ q * (1 + (2 : ENNReal) ^ q * (ENNReal.ofReal 2 ^ q +
        ENNReal.ofReal 8 ^ q * ∑' r : ℕ, ENNReal.ofReal (gam (s - max 1 s) κ r) ^ q)) := by
    calc _ ≤ _ := hS
      _ ≤ ENNReal.ofReal (B + 1) ^ q + (2 : ENNReal) ^ q * (ENNReal.ofReal 2 ^ q *
            ENNReal.ofReal (B + 1) ^ q + ENNReal.ofReal 8 ^ q * (ENNReal.ofReal (B + 1) ^ q *
              ∑' r : ℕ, ENNReal.ofReal (gam (s - max 1 s) κ r) ^ q)) :=
          add_le_add ((ENNReal.rpow_le_rpow hd0 hq.le).trans hBY)
            (mul_le_mul_right (add_le_add (mul_le_mul_right (ht.trans hBY) _)
              (mul_le_mul_right (le_mul_of_one_le_left' hY1) _)) _)
      _ = _ := by ring
  unfold rateQK
  calc _ ≤ _ := hred
    _ ≤ ENNReal.ofReal (2 ^ s) * (ENNReal.ofReal (B + 1) ^ q *
          (1 + (2 : ENNReal) ^ q * (ENNReal.ofReal 2 ^ q + ENNReal.ofReal 8 ^ q *
            ∑' r : ℕ, ENNReal.ofReal (gam (s - max 1 s) κ r) ^ q))) ^ (1 / q) :=
        mul_le_mul_right (ENNReal.rpow_le_rpow hfin (by positivity)) _
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / q), ← ENNReal.rpow_mul,
          mul_one_div_cancel hq.ne', ENNReal.rpow_one, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hMq.ne]
        ring

/-- **Corolário IV.4.3 (imersões quantitativas uniformes sobre bolas).** Com a agenda
`Ĥ^{[B]}_{s,κ}` (`HhatK`), existem constantes independentes de `B` e de `f` tais que, sobre a
bola `{f ∈ C(K) : ‖f‖* ≤ B}`, `B ≥ 1`:
`𝔞_{s,∞}^{𝓛,Ĥ^{[B]}_{s,0}}(f) ≤ C_{K,s}(B+1)` (`0 < s < 2`);
`𝔞_{s,q}^{𝓛,Ĥ^{[B]}_{s,0}}(f) ≤ C_{K,s,q}(B+1)` (`0 < s < 1`, `0 < q < ∞`);
`𝔞_{s,q}^{𝓛,Ĥ^{[B]}_{s,κ}}(f) ≤ C_{K,s,q,κ}(B+1)` (`1 ≤ s < 2`, `0 < q < ∞`, `κ > 1/q`). -/
theorem uniform_besov_ball (k0 : ℕ) (m0 : ℤ) :
    (∀ s : ℝ, 0 < s → s < 2 → ∃ C : ℝ, ∀ (B : ℝ) (f : ℝ → ℝ), 1 ≤ B →
      ContinuousOn f (cellIcc k0 m0) → bnormInf k0 m0 s f ≤ ENNReal.ofReal B →
      rateInfK k0 m0 s (HhatK k0 m0 B s 0) f ≤ ENNReal.ofReal (C * (B + 1))) ∧
    (∀ s q : ℝ, 0 < s → s < 1 → 0 < q → ∃ C : ℝ, ∀ (B : ℝ) (f : ℝ → ℝ), 1 ≤ B →
      ContinuousOn f (cellIcc k0 m0) → bnormQ k0 m0 s q f ≤ ENNReal.ofReal B →
      rateQK k0 m0 s q (HhatK k0 m0 B s 0) f ≤ ENNReal.ofReal (C * (B + 1))) ∧
    (∀ s q κ : ℝ, 1 ≤ s → s < 2 → 0 < q → 1 / q < κ → ∃ C : ℝ, ∀ (B : ℝ) (f : ℝ → ℝ), 1 ≤ B →
      ContinuousOn f (cellIcc k0 m0) → bnormQ k0 m0 s q f ≤ ENNReal.ofReal B →
      rateQK k0 m0 s q (HhatK k0 m0 B s κ) f ≤ ENNReal.ofReal (C * (B + 1))) := by
  refine ⟨fun s hs hs2 => ⟨2 ^ s * 8, fun B f hB1 hfc hnorm => ?_⟩,
    fun s q hs hs1 hq => ball_generic_Q hs (by linarith) hq le_rfl
      (gam_sum_geom (by rw [max_eq_left hs1.le]; linarith) le_rfl hq),
    fun s q κ hs1 hs2 hq hκ => ball_generic_Q (by linarith) hs2 hq
      (lt_trans (by positivity) hκ).le
      (gam_sum_log (by rw [max_eq_right hs1]; linarith) hq ((div_lt_iff₀ hq).mp hκ))⟩
  have hB0 : 0 ≤ B := by linarith
  have hred := rate_inf_le_dyadic hs
    (pErrK_antitone (k0 := k0) (m0 := m0) (HhatK_mono k0 m0 hB0 s le_rfl) f)
  have hsup : ⨆ r, dK k0 m0 s (HhatK k0 m0 B s 0) f r ≤ ENNReal.ofReal (2 * B + 8) := by
    refine iSup_le fun r => ?_
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · refine (dK_le_dist hs.le _ f le_rfl).trans ?_
      simp only [pow_zero, Real.one_rpow, ENNReal.ofReal_one, one_mul]
      exact (le_self_add.trans hnorm).trans (ENNReal.ofReal_le_ofReal (by linarith))
    · refine (dK_ball_bound hs hs2 hB1 hfc hnorm le_rfl hr).trans ?_
      have hb : btermK k0 m0 s f r ≤ ENNReal.ofReal B :=
        ((le_iSup (fun r => btermK k0 m0 s f r) r).trans le_add_self).trans hnorm
      calc ENNReal.ofReal 2 * btermK k0 m0 s f r +
            ENNReal.ofReal 8 * ENNReal.ofReal (gam (s - max 1 s) 0 r)
          ≤ ENNReal.ofReal 2 * ENNReal.ofReal B + ENNReal.ofReal 8 * 1 :=
            add_le_add (mul_le_mul_right hb _) (mul_le_mul_right (ENNReal.ofReal_le_one.mpr
              (gam_le_one (by linarith [le_max_right 1 s]) le_rfl r)) _)
        _ = ENNReal.ofReal (2 * B + 8) := by
            rw [mul_one, ← ENNReal.ofReal_mul (by norm_num),
              ← ENNReal.ofReal_add (by positivity) (by norm_num)]
  unfold rateInfK
  calc _ ≤ _ := hred
    _ ≤ ENNReal.ofReal (2 ^ s) * ENNReal.ofReal (2 * B + 8) := mul_le_mul_right hsup _
    _ = ENNReal.ofReal (2 ^ s * (2 * B + 8)) := (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
        have : (0 : ℝ) < 2 ^ s := by positivity
        nlinarith)

end Pendencias.Jackson
