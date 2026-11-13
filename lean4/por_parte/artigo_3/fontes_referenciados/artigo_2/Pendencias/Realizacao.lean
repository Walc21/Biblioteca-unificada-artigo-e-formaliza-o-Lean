import Pendencias.Direta

/-!
# IV.5.12, IV.5.13 e IV.5.14 — funcional de realização em `[0,1]`

-- ITEM: IV.5.12
-- ITEM: IV.5.13
-- ITEM: IV.5.14

* `realG G N f = inf_{g ∈ G_N} {‖f - g‖_∞ + ω₂(g, 1/N)_∞}`: o funcional de realização de uma
  família qualquer `G` (eq. network-regularized-certificate); `Agenda.realN H` é o caso
  `G = Σ^{𝓛,H}` (eq. self-roughness-certificate), por definição (`realN_eq`);
* `RGInf s G`, `RGQ s q G`: os estratos reversíveis `{f ∈ C([0,1]) :
  ‖(2^{rs} 𝓡_{2^r}(f))_{r≥1}‖_{ℓ^q} < ∞}` (eq. reversible-stratum); `RInf`, `RQ` são os casos
  `G = Σ^{𝓛,H}`;
* `BesovInfSet 0 0 s`, `BesovQSet 0 0 s q`: `B^s_{∞,q}([0,1])` (ver `Jackson.lean`);
  `Hsk s κ = H_{s,κ}` e `HtilK 0 0 s η = H̃_{s,η}` em `K = [0,1]`.
-/

namespace Pendencias.Jackson

open Set Artigo LTree Pendencias Pendencias.Agenda

/-! ## Funcional de realização de uma família -/

/-- `𝓡_N^{G}(f) = inf_{g ∈ G_N} {‖f - g‖_∞ + ω₂(g, N⁻¹)_∞}` em `[0,1]` -/
noncomputable def realG (G : ℕ → Set (ℝ → ℝ)) (N : ℕ) (f : ℝ → ℝ) : ENNReal :=
  ⨅ g ∈ G N, (distInf f g + omega2 g (1 / N))

lemma realN_eq (H : ℕ → ℕ) (N : ℕ) (f : ℝ → ℝ) : realN H N f = realG (Sigma H) N f := rfl

lemma distInf_comm (f g : ℝ → ℝ) : distInf f g = distInf g f := by
  unfold distInf; simp only [abs_sub_comm]

/-- a desigualdade inversa vale para qualquer família: `ω₂(f, 1/N) ≤ 4 𝓡_N^{G}(f)` -/
lemma inverse_realG (G : ℕ → Set (ℝ → ℝ)) (N : ℕ) (f : ℝ → ℝ) :
    omega2 f (1 / N) ≤ 4 * realG G N f := by
  unfold realG
  rw [ENNReal.mul_iInf_of_ne (by norm_num) (by norm_num)]
  refine le_iInf fun g => ?_
  rw [ENNReal.mul_iInf_of_ne (by norm_num) (by norm_num)]
  refine le_iInf fun _ => ?_
  calc omega2 f (1 / N) ≤ 4 * distInf f g + omega2 g (1 / N) := omega2_le f g _
    _ ≤ 4 * distInf f g + 4 * omega2 g (1 / N) :=
        add_le_add le_rfl (le_mul_of_one_le_left (zero_le (omega2 g (1 / N))) (by norm_num))
    _ = 4 * (distInf f g + omega2 g (1 / N)) := (mul_add _ _ _).symm

lemma omega2_mono_t (f : ℝ → ℝ) {t t' : ℝ} (h : t ≤ t') : omega2 f t ≤ omega2 f t' :=
  iSup_le fun _ => iSup_le fun hh => iSup_le fun _ => iSup_le fun hx =>
    le_omega2 ⟨hh.1, hh.2.trans h⟩ hx

/-- usar `g ∈ G_N` no funcional: `𝓡_N ≤ 5‖f - g‖ + ω₂(f,t)` para `t ≥ 1/N` -/
lemma realG_le_five {G : ℕ → Set (ℝ → ℝ)} {N : ℕ} {f g : ℝ → ℝ} (hg : g ∈ G N) {t : ℝ}
    (ht : 1 / (N : ℝ) ≤ t) : realG G N f ≤ 5 * distInf f g + omega2 f t := by
  calc realG G N f ≤ distInf f g + omega2 g (1 / N) := iInf₂_le g hg
    _ ≤ distInf f g + omega2 g t := add_le_add le_rfl (omega2_mono_t g ht)
    _ ≤ distInf f g + (4 * distInf g f + omega2 f t) := add_le_add le_rfl (omega2_le g f t)
    _ = 5 * distInf f g + omega2 f t := by rw [distInf_comm g f]; ring

lemma five_bound {d ω : ENNReal} {x : ℝ} (hd : d ≤ 2 * ω + ENNReal.ofReal x) :
    5 * d + ω ≤ 11 * ω + ENNReal.ofReal (5 * x) := by
  calc 5 * d + ω ≤ 5 * (2 * ω + ENNReal.ofReal x) + ω :=
        add_le_add (mul_le_mul_right hd 5) le_rfl
    _ = 11 * ω + 5 * ENNReal.ofReal x := by ring
    _ = 11 * ω + ENNReal.ofReal (5 * x) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5), ENNReal.ofReal_ofNat]

lemma inv_two_pow_cast (r : ℕ) : (1 : ℝ) / ((2 ^ r : ℕ) : ℝ) = ((2 : ℝ) ^ r)⁻¹ := by
  push_cast; rw [one_div]

lemma distInf_lt_top_of_cont {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (0 : ℝ) 1)) :
    distInf f 0 < ⊤ := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  refine lt_of_le_of_lt (iSup₂_le fun x hx => ?_ : distInf f 0 ≤ ENNReal.ofReal C)
    ENNReal.ofReal_lt_top
  apply ENNReal.ofReal_le_ofReal
  simpa [Real.norm_eq_abs] using hC x hx

/-! ## IV.5.12 -/

/-- **Teorema IV.5.12 (Jackson racional para o funcional de realização)**, primeira parte.
Com `C₀ = 11` universal e `C_f = C₁(‖f‖_∞ + 1)`, `C₁` universal: se `0 < s < 2` e
`f ∈ B^s_{∞,∞}([0,1])`, então para toda potência de dois `N = 2^r` suficientemente grande e toda
agenda cuja altura `H(N)` satisfaz as hipóteses do Lema IV.4.1 em `K = [0,1]`
(`H(N) ≥ max{C_K N^{ν_s}, 16(R+1)}` e a condição geométrica `H(N) ≥ max{2, r+1, N}`),
`¼ ω₂(f,1/N) ≤ 𝓡_N^{𝓛,H}(f) ≤ C₀ ω₂(f,1/N) + C_f/H(N)`. -/
theorem regularized_jackson :
    ∃ C0 C1 : ℝ, 0 < C0 ∧ 0 < C1 ∧ ∀ (s : ℝ) (f : ℝ → ℝ), 0 < s → s < 2 → BesovInfK 0 0 s f →
      ∃ n0 : ℕ, ∀ r : ℕ, n0 ≤ 2 ^ r → ∀ H : ℕ → ℕ,
        max (CK 0 0 * ((2 : ℝ) ^ r) ^ max 1 s) (16 * ((distInf f 0).toReal + 1)) ≤
          (H (2 ^ r) : ℝ) →
        (2 ≤ H (2 ^ r) ∧ r + 1 ≤ H (2 ^ r) ∧ 2 ^ r ≤ H (2 ^ r)) →
        omega2 f (1 / ((2 ^ r : ℕ) : ℝ)) ≤ 4 * realN H (2 ^ r) f ∧
        realN H (2 ^ r) f ≤ ENNReal.ofReal C0 * omega2 f (1 / ((2 ^ r : ℕ) : ℝ)) +
          ENNReal.ofReal (C1 * ((distInf f 0).toReal + 1) / H (2 ^ r)) := by
  obtain ⟨C, hC, h⟩ := rational_jackson_height
  refine ⟨11, 5 * C, by norm_num, by positivity, fun s f hs hs2 hB => ?_⟩
  obtain ⟨n0, hn0⟩ := h 0 0 s f 1 hs hs2 hB whitney_one
  refine ⟨n0, fun r hr H hH hgeo => ⟨universal_inverse H (2 ^ r) f, ?_⟩⟩
  have hgeo' : 2 ≤ H (2 ^ r) ∧ 0 + r + 1 ≤ H (2 ^ r) ∧
      ∀ j : ℤ, 0 ≤ j → j < 2 ^ r → (2 ^ r * 0 + j).natAbs + 1 ≤ H (2 ^ r) := by
    refine ⟨hgeo.1, by simpa using hgeo.2.1, fun j hj0 hj1 => ?_⟩
    have h1 : (j.natAbs : ℤ) < 2 ^ r := by rw [Int.natAbs_of_nonneg hj0]; exact hj1
    have h2 : j.natAbs < 2 ^ r := by exact_mod_cast h1
    simp only [mul_zero, zero_add]
    omega
  obtain ⟨T, hT, hd⟩ := hn0 r hr (H (2 ^ r)) (by rw [distK_zero]; exact hH) hgeo'
  simp only [distK_zero, omega2K_zero, zero_add, mul_one, ENNReal.ofReal_ofNat] at hd
  have hg : T.eval 0 0 ∈ Sigma H (2 ^ r) := Or.inr ⟨T, hT, rfl⟩
  have h5 := realG_le_five (G := Sigma H) (f := f) hg (le_refl (1 / ((2 ^ r : ℕ) : ℝ)))
  rw [inv_two_pow_cast] at h5 ⊢
  rw [ENNReal.ofReal_ofNat, realN_eq]
  refine (h5.trans (five_bound hd)).trans (le_of_eq ?_)
  congr 2; ring

/-- **Teorema IV.5.12**, versão uniforme. Com `C₀ = 11` e `C = 40` universais: se
`‖f‖*_{B^s_{∞,∞}} ≤ B`, `B ≥ 1`, e `H(N) ≥ Ĥ^{[B]}_{s,0}(N)`, a mesma estimativa vale para toda
potência diádica `N = 2^r ≥ 2`, com `C_f/H(N)` substituído por `C(B+1)/H(N)`. -/
theorem regularized_jackson_uniform :
    ∃ C0 C : ℝ, 0 < C0 ∧ 0 < C ∧ ∀ (s : ℝ) (f : ℝ → ℝ) (B : ℝ), 0 < s → s < 2 → 1 ≤ B →
      ContinuousOn f (Icc (0 : ℝ) 1) → bnormInf 0 0 s f ≤ ENNReal.ofReal B →
      ∀ r : ℕ, 1 ≤ r → ∀ H : ℕ → ℕ, HhatK 0 0 B s 0 (2 ^ r) ≤ H (2 ^ r) →
        omega2 f (1 / ((2 ^ r : ℕ) : ℝ)) ≤ 4 * realN H (2 ^ r) f ∧
        realN H (2 ^ r) f ≤ ENNReal.ofReal C0 * omega2 f (1 / ((2 ^ r : ℕ) : ℝ)) +
          ENNReal.ofReal (C * (B + 1) / H (2 ^ r)) := by
  refine ⟨11, 40, by norm_num, by norm_num, fun s f B hs hs2 hB1 hfc hnorm r hr H hH =>
    ⟨universal_inverse H (2 ^ r) f, ?_⟩⟩
  obtain ⟨hA1, hA⟩ := rational_jackson_uniform_explicit 0 0
  have hc0 : 0 ≤ AK 0 0 * (B + 1) := mul_nonneg (by linarith) (by linarith)
  have hmax : (0 : ℝ) ≤ max 1 s := le_trans zero_le_one (le_max_left _ _)
  have hHr : AK 0 0 * (B + 1) * ((2 : ℝ) ^ r) ^ max 1 s ≤ (H (2 ^ r) : ℝ) := by
    have h1 := Hgen_ge (c := AK 0 0 * (B + 1)) (ν := max 1 s) (κ := 0) hc0 le_rfl (N := 2 ^ r)
      Nat.one_le_two_pow
    push_cast at h1
    have h2 : (HhatK 0 0 B s 0 (2 ^ r) : ℝ) ≤ H (2 ^ r) := by exact_mod_cast hH
    exact le_trans (le_trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (by linarith) hmax) hc0) h1) h2
  obtain ⟨-, T, hT, hd⟩ := hA s f 1 B hs hs2 whitney_one hB1 (cellIcc_zero ▸ hfc) hnorm r hr _ hHr
  simp only [distK_zero, omega2K_zero, zero_add, mul_one, ENNReal.ofReal_ofNat] at hd
  have hg : T.eval 0 0 ∈ Sigma H (2 ^ r) := Or.inr ⟨T, hT, rfl⟩
  have h5 := realG_le_five (G := Sigma H) (f := f) hg (le_refl (1 / ((2 ^ r : ℕ) : ℝ)))
  rw [inv_two_pow_cast] at h5 ⊢
  rw [ENNReal.ofReal_ofNat, realN_eq]
  refine (h5.trans (five_bound hd)).trans (le_of_eq ?_)
  congr 2; ring

/-! ## Estratos reversíveis -/

/-- termo `2^{rs} 𝓡_{2^r}^{G}(f)` -/
noncomputable def rG (s : ℝ) (G : ℕ → Set (ℝ → ℝ)) (f : ℝ → ℝ) (r : ℕ) : ENNReal :=
  ENNReal.ofReal (((2 : ℝ) ^ r) ^ s) * realG G (2 ^ r) f

/-- estrato reversível, `q = ∞`: `{f ∈ C([0,1]) : sup_{r ≥ 1} 2^{rs} 𝓡_{2^r}^{G}(f) < ∞}`
(eq. reversible-stratum; os índices `r ≥ 1` são escritos `r + 1`, `r ≥ 0`) -/
def RGInf (s : ℝ) (G : ℕ → Set (ℝ → ℝ)) : Set (ℝ → ℝ) :=
  {f | ContinuousOn f (Icc (0 : ℝ) 1) ∧ ⨆ r : ℕ, rG s G f (r + 1) < ⊤}

/-- estrato reversível, `0 < q < ∞`:
`{f ∈ C([0,1]) : (∑_{r ≥ 1} [2^{rs} 𝓡_{2^r}^{G}(f)]^q)^{1/q} < ∞}` -/
def RGQ (s q : ℝ) (G : ℕ → Set (ℝ → ℝ)) : Set (ℝ → ℝ) :=
  {f | ContinuousOn f (Icc (0 : ℝ) 1) ∧ (∑' r : ℕ, rG s G f (r + 1) ^ q) ^ (1 / q) < ⊤}

/-- `𝓡_∞^s(𝓛,H)` -/
def RInf (s : ℝ) (H : ℕ → ℕ) : Set (ℝ → ℝ) := RGInf s (Sigma H)

/-- `𝓡_q^s(𝓛,H)`, `0 < q < ∞` -/
def RQ (s q : ℝ) (H : ℕ → ℕ) : Set (ℝ → ℝ) := RGQ s q (Sigma H)

lemma rG_le_dist {s : ℝ} {G : ℕ → Set (ℝ → ℝ)} (f : ℝ → ℝ) {r : ℕ}
    (h0 : (0 : ℝ → ℝ) ∈ G (2 ^ r)) :
    rG s G f r ≤ ENNReal.ofReal (((2 : ℝ) ^ r) ^ s) * distInf f 0 := by
  refine mul_le_mul_right ?_ _
  calc realG G (2 ^ r) f ≤ distInf f 0 + omega2 0 (1 / ((2 ^ r : ℕ) : ℝ)) := iInf₂_le 0 h0
    _ = distInf f 0 := by rw [omega2_zero, add_zero]

lemma rG_lt_top {s : ℝ} {G : ℕ → Set (ℝ → ℝ)} {f : ℝ → ℝ} {r : ℕ}
    (h0 : (0 : ℝ → ℝ) ∈ G (2 ^ r)) (hd : distInf f 0 < ⊤) : rG s G f r < ⊤ :=
  lt_of_le_of_lt (rG_le_dist f h0) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hd)

/-! ### Do estrato para Besov (desigualdade inversa universal) -/

lemma bterm_succ_le (s : ℝ) (G : ℕ → Set (ℝ → ℝ)) (f : ℝ → ℝ) (r : ℕ) :
    btermK 0 0 s f (r + 1) ≤ 4 * rG s G f (r + 1) := by
  rw [btermK_zero]
  unfold bterm rG
  have h := inverse_realG G (2 ^ (r + 1)) f
  rw [inv_two_pow_cast] at h
  calc ENNReal.ofReal (((2 : ℝ) ^ (r + 1)) ^ s) * omega2 f ((2 : ℝ) ^ (r + 1))⁻¹
      ≤ ENNReal.ofReal (((2 : ℝ) ^ (r + 1)) ^ s) * (4 * realG G (2 ^ (r + 1)) f) :=
        mul_le_mul_right h _
    _ = _ := mul_left_comm _ _ _

lemma bterm_zero_le (s : ℝ) (f : ℝ → ℝ) : btermK 0 0 s f 0 ≤ 4 * distInf f 0 := by
  rw [btermK_zero]
  simp only [bterm, pow_zero, Real.one_rpow, ENNReal.ofReal_one, one_mul, inv_one]
  exact omega2_le_norm f 1

lemma besov_of_RGInf {s : ℝ} {G : ℕ → Set (ℝ → ℝ)} {f : ℝ → ℝ} (hf : f ∈ RGInf s G) :
    BesovInfK 0 0 s f := by
  obtain ⟨hfc, hfin⟩ := hf
  have hd := distInf_lt_top_of_cont hfc
  refine ⟨cellIcc_zero ▸ hfc, ?_⟩
  unfold bnormInf
  rw [distK_zero]
  refine ENNReal.add_lt_top.mpr ⟨hd, lt_of_le_of_lt (iSup_le fun r => ?_ :
    ⨆ r, btermK 0 0 s f r ≤ 4 * distInf f 0 + 4 * ⨆ r : ℕ, rG s G f (r + 1)) ?_⟩
  · rcases Nat.eq_zero_or_pos r with rfl | hr
    · exact (bterm_zero_le s f).trans le_self_add
    · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      exact ((bterm_succ_le s G f r').trans
        (mul_le_mul_right (le_iSup (fun r : ℕ => rG s G f (r + 1)) r') 4)).trans le_add_self
  · exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top (by norm_num) hd,
      ENNReal.mul_lt_top (by norm_num) hfin⟩

lemma besov_of_RGQ {s q : ℝ} (hq : 0 < q) {G : ℕ → Set (ℝ → ℝ)} {f : ℝ → ℝ}
    (hf : f ∈ RGQ s q G) : BesovQK 0 0 s q f := by
  obtain ⟨hfc, hfin⟩ := hf
  have hd := distInf_lt_top_of_cont hfc
  have hfin' : ∑' r : ℕ, rG s G f (r + 1) ^ q < ⊤ := by
    have := ENNReal.rpow_lt_top_of_nonneg hq.le hfin.ne
    rwa [← ENNReal.rpow_mul, one_div_mul_cancel hq.ne', ENNReal.rpow_one] at this
  have h4q : (4 : ENNReal) ^ q < ⊤ := ENNReal.rpow_lt_top_of_nonneg hq.le (by norm_num)
  refine ⟨cellIcc_zero ▸ hfc, ?_⟩
  unfold bnormQ
  rw [distK_zero]
  refine ENNReal.add_lt_top.mpr ⟨hd, ENNReal.rpow_lt_top_of_nonneg (by positivity) (ne_of_lt ?_)⟩
  rw [tsum_eq_zero_add' ENNReal.summable]
  refine ENNReal.add_lt_top.mpr ⟨ENNReal.rpow_lt_top_of_nonneg hq.le
    (lt_of_le_of_lt (bterm_zero_le s f) (ENNReal.mul_lt_top (by norm_num) hd)).ne, ?_⟩
  calc ∑' r : ℕ, btermK 0 0 s f (r + 1) ^ q ≤ ∑' r : ℕ, (4 : ENNReal) ^ q * rG s G f (r + 1) ^ q :=
        ENNReal.tsum_le_tsum fun r => by
          rw [← ENNReal.mul_rpow_of_nonneg _ _ hq.le]
          exact ENNReal.rpow_le_rpow (bterm_succ_le s G f r) hq.le
    _ = (4 : ENNReal) ^ q * ∑' r : ℕ, rG s G f (r + 1) ^ q := ENNReal.tsum_mul_left
    _ < ⊤ := ENNReal.mul_lt_top h4q hfin'

/-! ### De Besov para o estrato (lado direto) -/

/-- Lema IV.4.1 em `[0,1]`, com o aproximante exibido em `Σ_{2^r}^{𝓛,H}` -/
lemma sigma_dyadic_bound {s : ℝ} {f : ℝ → ℝ} (hs : 0 < s) (hs2 : s < 2)
    (hB : BesovInfK 0 0 s f) {H : ℕ → ℕ}
    (hH : ∀ N : ℕ, 1 ≤ N → CK 0 0 * ((N : ℝ) + 1) ^ max 1 s ≤ H N) :
    ∃ (C : ℝ) (r0 : ℕ), 0 < C ∧ ∀ r, r0 ≤ r → ∃ g ∈ Sigma H (2 ^ r),
      distInf f g ≤ 2 * omega2 f ((2 : ℝ) ^ r)⁻¹ +
        ENNReal.ofReal (C * ((distInf f 0).toReal + 1) / H (2 ^ r)) := by
  obtain ⟨C, r0, hC, h⟩ := adm_dyadic_bound hs hs2 hB whitney_one hH
  refine ⟨C, r0, hC, fun r hr => ?_⟩
  obtain ⟨T, hT, hd⟩ := h r hr
  simp only [distK_zero, omega2K_zero, zero_add, mul_one, ENNReal.ofReal_ofNat] at hd
  exact ⟨T.eval 0 0, Or.inr ⟨T, hT, rfl⟩, hd⟩

/-- cota de cauda do funcional de realização de uma família `G` que contém `Σ^{𝓛,H}` com
atraso diádico `a`: `Σ_{2^r}^{𝓛,H} ⊆ G_{2^{r+a}}` -/
lemma rG_tail_bound {s : ℝ} {f : ℝ → ℝ} (hs : 0 < s) (hs2 : s < 2) (hB : BesovInfK 0 0 s f)
    {c ν κ : ℝ} (hc : CK 0 0 ≤ c) (hν : max 1 s ≤ ν) (hκ : 0 ≤ κ)
    {G : ℕ → Set (ℝ → ℝ)} {a : ℕ} (hG : ∀ r : ℕ, Sigma (Hgen c ν κ) (2 ^ r) ⊆ G (2 ^ (r + a))) :
    ∃ (D : ℝ) (r0 : ℕ), 0 ≤ D ∧ ∀ r, r0 ≤ r →
      rG s G f (r + a) ≤ ENNReal.ofReal (11 * ((2 : ℝ) ^ a) ^ s) * btermK 0 0 s f r +
        ENNReal.ofReal D * ENNReal.ofReal (gam (s - ν) κ r) := by
  have hCK := CK_ge 0 0
  have hc0 : 0 < c := by linarith
  have hν0 : 0 ≤ ν := le_trans (le_trans zero_le_one (le_max_left _ _)) hν
  have hH : ∀ N : ℕ, 1 ≤ N → CK 0 0 * ((N : ℝ) + 1) ^ max 1 s ≤ Hgen c ν κ N := by
    intro N hN
    have hN' : (1 : ℝ) ≤ (N : ℝ) + 1 := by
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg _
      linarith
    calc CK 0 0 * ((N : ℝ) + 1) ^ max 1 s ≤ c * ((N : ℝ) + 1) ^ ν :=
          mul_le_mul hc (Real.rpow_le_rpow_of_exponent_le hN' hν) (by positivity) hc0.le
      _ ≤ _ := Hgen_ge hc0.le hκ hN
  obtain ⟨C, r0, hC, hb⟩ := sigma_dyadic_bound hs hs2 hB hH
  have hR : 0 ≤ (distInf f 0).toReal := ENNReal.toReal_nonneg
  set A : ℝ := ((2 : ℝ) ^ a) ^ s with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨5 * A * C * ((distInf f 0).toReal + 1) * c⁻¹, r0, by positivity, fun r hr => ?_⟩
  obtain ⟨g, hg, hd⟩ := hb r hr
  have ht : (1 : ℝ) / ((2 ^ (r + a) : ℕ) : ℝ) ≤ ((2 : ℝ) ^ r)⁻¹ := by
    rw [inv_two_pow_cast]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (Nat.le_add_right r a))
  have h11 := (realG_le_five (f := f) (hG r hg) ht).trans (five_bound hd)
  set P : ℝ := ((2 : ℝ) ^ r) ^ s with hP
  have hP0 : 0 ≤ P := by positivity
  have hPa : ((2 : ℝ) ^ (r + a)) ^ s = A * P := by
    rw [hA, hP, pow_add, Real.mul_rpow (by positivity) (by positivity), mul_comm]
  set x : ℝ := C * ((distInf f 0).toReal + 1) / (Hgen c ν κ (2 ^ r) : ℝ) with hx
  have hbt : btermK 0 0 s f r = ENNReal.ofReal P * omega2 f ((2 : ℝ) ^ r)⁻¹ := by
    rw [btermK_zero]; rfl
  calc rG s G f (r + a) = ENNReal.ofReal (A * P) * realG G (2 ^ (r + a)) f := by
        unfold rG; rw [hPa]
    _ ≤ ENNReal.ofReal (A * P) * (11 * omega2 f ((2 : ℝ) ^ r)⁻¹ + ENNReal.ofReal (5 * x)) :=
        mul_le_mul_right h11 _
    _ = ENNReal.ofReal (11 * A) * (ENNReal.ofReal P * omega2 f ((2 : ℝ) ^ r)⁻¹) +
          ENNReal.ofReal (A * P * (5 * x)) := by
        rw [mul_add, ← ENNReal.ofReal_mul (by positivity : 0 ≤ A * P),
          ENNReal.ofReal_mul hA0, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 11),
          ENNReal.ofReal_ofNat]
        ring
    _ ≤ _ := by
        rw [hbt, ← ENNReal.ofReal_mul (by positivity)]
        refine add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_)
        have hrat := ratio_le_gam (κ := κ) hc0 hν0 s r
        calc A * P * (5 * x) = 5 * A * C * ((distInf f 0).toReal + 1) *
              (P / (Hgen c ν κ (2 ^ r) : ℝ)) := by rw [hx]; ring
          _ ≤ 5 * A * C * ((distInf f 0).toReal + 1) * (c⁻¹ * gam (s - ν) κ r) :=
              mul_le_mul_of_nonneg_left hrat (by positivity)
          _ = _ := by ring

lemma RGQ_of_besov {s q : ℝ} (hs : 0 < s) (hs2 : s < 2) (hq : 0 < q) {f : ℝ → ℝ}
    (hB : BesovQK 0 0 s q f) {c ν κ : ℝ} (hc : CK 0 0 ≤ c) (hν : max 1 s ≤ ν) (hκ : 0 ≤ κ)
    (hsum : ∑' r : ℕ, ENNReal.ofReal (gam (s - ν) κ r) ^ q < ⊤)
    {G : ℕ → Set (ℝ → ℝ)} {a : ℕ} (h0 : ∀ r : ℕ, (0 : ℝ → ℝ) ∈ G (2 ^ r))
    (hG : ∀ r : ℕ, Sigma (Hgen c ν κ) (2 ^ r) ⊆ G (2 ^ (r + a))) : f ∈ RGQ s q G := by
  have hfc : ContinuousOn f (Icc (0 : ℝ) 1) := cellIcc_zero ▸ hB.1
  have hd := distInf_lt_top_of_cont hfc
  have htfin : ∑' r : ℕ, btermK 0 0 s f r ^ q < ⊤ := by
    have h1 : (∑' r : ℕ, btermK 0 0 s f r ^ q) ^ (1 / q) < ⊤ :=
      lt_of_le_of_lt le_add_self hB.2
    have := ENNReal.rpow_lt_top_of_nonneg hq.le h1.ne
    rwa [← ENNReal.rpow_mul, one_div_mul_cancel hq.ne', ENNReal.rpow_one] at this
  obtain ⟨D, r0, hD, htail⟩ := rG_tail_bound hs hs2 (hB.toInf hq) hc hν hκ hG
  have hS := tsum_rpow_le_of_tail (a := fun i => rG s G f (i + a)) hq r0 htail
  have h2q : (2 : ENNReal) ^ q < ⊤ := ENNReal.rpow_lt_top_of_nonneg hq.le (by norm_num)
  have hterm : ∀ r, rG s G f r ^ q < ⊤ := fun r =>
    ENNReal.rpow_lt_top_of_nonneg hq.le (rG_lt_top (h0 r) hd).ne
  have hshift : ∑' i, rG s G f (i + a) ^ q < ⊤ := by
    refine lt_of_le_of_lt hS (ENNReal.add_lt_top.mpr ⟨?_, ?_⟩)
    · exact ENNReal.sum_lt_top.mpr fun r _ => hterm _
    · exact ENNReal.mul_lt_top h2q (ENNReal.add_lt_top.mpr
        ⟨ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hq.le ENNReal.ofReal_ne_top) htfin,
          ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hq.le ENNReal.ofReal_ne_top) hsum⟩)
  have hall : ∑' r, rG s G f r ^ q < ⊤ := by
    rw [← Summable.sum_add_tsum_nat_add' (f := fun r => rG s G f r ^ q) (k := a)
      ENNReal.summable]
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.sum_lt_top.mpr fun r _ => hterm _, hshift⟩
  exact ⟨hfc, ENNReal.rpow_lt_top_of_nonneg (by positivity)
    (lt_of_le_of_lt (tsum_tail_le (fun r => rG s G f r ^ q) 1) hall).ne⟩

lemma RGInf_of_besov {s : ℝ} (hs : 0 < s) (hs2 : s < 2) {f : ℝ → ℝ}
    (hB : BesovInfK 0 0 s f) {c ν κ : ℝ} (hc : CK 0 0 ≤ c) (hν : max 1 s ≤ ν) (hκ : 0 ≤ κ)
    {G : ℕ → Set (ℝ → ℝ)} {a : ℕ} (h0 : ∀ r : ℕ, (0 : ℝ → ℝ) ∈ G (2 ^ r))
    (hG : ∀ r : ℕ, Sigma (Hgen c ν κ) (2 ^ r) ⊆ G (2 ^ (r + a))) : f ∈ RGInf s G := by
  have hfc : ContinuousOn f (Icc (0 : ℝ) 1) := cellIcc_zero ▸ hB.1
  have hd := distInf_lt_top_of_cont hfc
  have hbfin : ⨆ r, btermK 0 0 s f r < ⊤ := lt_of_le_of_lt le_add_self hB.2
  obtain ⟨D, r0, hD, htail⟩ := rG_tail_bound hs hs2 hB hc hν hκ hG
  refine ⟨hfc, lt_of_le_of_lt (iSup_le fun j => ?_ : ⨆ j : ℕ, rG s G f (j + 1) ≤
    ENNReal.ofReal (((2 : ℝ) ^ (r0 + a)) ^ s) * distInf f 0 +
      (ENNReal.ofReal (11 * ((2 : ℝ) ^ a) ^ s) * (⨆ r, btermK 0 0 s f r) + ENNReal.ofReal D)) ?_⟩
  · rcases le_total (j + 1) (r0 + a) with h | h
    · refine ((rG_le_dist f (h0 _)).trans (mul_le_mul_left ?_ _)).trans le_self_add
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by positivity)
        (pow_le_pow_right₀ (by norm_num) h) hs.le)
    · obtain ⟨i, hi, hji⟩ : ∃ i, r0 ≤ i ∧ j + 1 = i + a := ⟨j + 1 - a, by omega, by omega⟩
      rw [hji]
      refine ((htail i hi).trans (add_le_add (mul_le_mul_right (le_iSup _ i) _) ?_)).trans
        le_add_self
      calc ENNReal.ofReal D * ENNReal.ofReal (gam (s - ν) κ i) ≤ ENNReal.ofReal D * 1 :=
            mul_le_mul_right (ENNReal.ofReal_le_one.mpr
              (gam_le_one (by linarith [le_max_right 1 s]) hκ i)) _
        _ = ENNReal.ofReal D := mul_one _
  · exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hd,
      ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hbfin,
        ENNReal.ofReal_lt_top⟩⟩

/-- igualdade de conjuntos para uma família `G` (caso `q = ∞`) -/
lemma besov_eq_RGInf {s : ℝ} (hs : 0 < s) (hs2 : s < 2) {c ν κ : ℝ} (hc : CK 0 0 ≤ c)
    (hν : max 1 s ≤ ν) (hκ : 0 ≤ κ) {G : ℕ → Set (ℝ → ℝ)} {a : ℕ}
    (h0 : ∀ r : ℕ, (0 : ℝ → ℝ) ∈ G (2 ^ r))
    (hG : ∀ r : ℕ, Sigma (Hgen c ν κ) (2 ^ r) ⊆ G (2 ^ (r + a))) :
    BesovInfSet 0 0 s = RGInf s G :=
  Set.Subset.antisymm (fun _ hf => RGInf_of_besov hs hs2 hf hc hν hκ h0 hG)
    (fun _ hf => besov_of_RGInf hf)

/-- igualdade de conjuntos para uma família `G` (caso `0 < q < ∞`) -/
lemma besov_eq_RGQ {s q : ℝ} (hs : 0 < s) (hs2 : s < 2) (hq : 0 < q) {c ν κ : ℝ}
    (hc : CK 0 0 ≤ c) (hν : max 1 s ≤ ν) (hκ : 0 ≤ κ)
    (hsum : ∑' r : ℕ, ENNReal.ofReal (gam (s - ν) κ r) ^ q < ⊤)
    {G : ℕ → Set (ℝ → ℝ)} {a : ℕ} (h0 : ∀ r : ℕ, (0 : ℝ → ℝ) ∈ G (2 ^ r))
    (hG : ∀ r : ℕ, Sigma (Hgen c ν κ) (2 ^ r) ⊆ G (2 ^ (r + a))) :
    BesovQSet 0 0 s q = RGQ s q G :=
  Set.Subset.antisymm (fun _ hf => RGQ_of_besov hs hs2 hq hf hc hν hκ hsum h0 hG)
    (fun _ hf => besov_of_RGQ hq hf)

/-! ## IV.5.13 -/

lemma Hsk_eq_Hgen (s κ : ℝ) : Hsk s κ = Hgen (CK 0 0) (max 1 s) κ := (HskK_zero s κ).symm

/-- **Teorema IV.5.13 (caracterização pelo funcional de realização).** Para `0 < s < 2`:
`B^s_{∞,∞}([0,1]) = 𝓡^s_∞(𝓛,H_{s,0})`; `B^s_{∞,q}([0,1]) = 𝓡^s_q(𝓛,H_{s,0})` para
`0 < q < ∞`, `0 < s < 1`; `B^s_{∞,q}([0,1]) = 𝓡^s_q(𝓛,H_{s,κ})` para `0 < q < ∞`,
`1 ≤ s < 2`, `κ > 1/q`; e a agenda logarítmica da última linha pode ser substituída pela
agenda com folga polinomial `H̃_{s,η}`, `η > 0`. -/
theorem complete_besov_reversibility {s : ℝ} (hs : 0 < s) (hs2 : s < 2) :
    BesovInfSet 0 0 s = RInf s (Hsk s 0) ∧
    (∀ q : ℝ, 0 < q → s < 1 → BesovQSet 0 0 s q = RQ s q (Hsk s 0)) ∧
    (∀ q κ : ℝ, 0 < q → 1 ≤ s → 1 / q < κ → BesovQSet 0 0 s q = RQ s q (Hsk s κ)) ∧
    (∀ q η : ℝ, 0 < q → 1 ≤ s → 0 < η → BesovQSet 0 0 s q = RQ s q (HtilK 0 0 s η)) := by
  have hz : ∀ (H : ℕ → ℕ) (r : ℕ), (0 : ℝ → ℝ) ∈ Sigma H (2 ^ r) := fun _ _ => Or.inl rfl
  have hsub : ∀ (H : ℕ → ℕ) (r : ℕ), Sigma H (2 ^ r) ⊆ Sigma H (2 ^ (r + 0)) :=
    fun _ _ => subset_rfl
  refine ⟨?_, fun q hq hs1 => ?_, fun q κ hq hs1 hκ => ?_, fun q η hq hs1 hη => ?_⟩
  · rw [Hsk_eq_Hgen]
    exact besov_eq_RGInf hs hs2 le_rfl le_rfl le_rfl (hz _) (hsub _)
  · rw [Hsk_eq_Hgen]
    exact besov_eq_RGQ hs hs2 hq le_rfl le_rfl le_rfl
      (gam_sum_geom (by rw [max_eq_left hs1.le]; linarith) le_rfl hq) (hz _) (hsub _)
  · rw [Hsk_eq_Hgen]
    exact besov_eq_RGQ hs hs2 hq le_rfl le_rfl (lt_trans (by positivity) hκ).le
      (gam_sum_log (by rw [max_eq_right hs1]; linarith) hq ((div_lt_iff₀ hq).mp hκ))
      (hz _) (hsub _)
  · rw [HtilK_eq]
    exact besov_eq_RGQ hs hs2 hq le_rfl (max_le_max le_rfl (by linarith)) le_rfl
      (gam_sum_geom (by have := le_max_right 1 (s + η); linarith) le_rfl hq) (hz _) (hsub _)

/-! ## IV.5.14 -/

/-- aninhamento no orçamento: `𝒩_N ⊆ 𝒩_M` para `1 ≤ N ≤ M` -/
lemma nest_mono {Nn : ℕ → Set (ℝ → ℝ)} (hnest : ∀ N : ℕ, 1 ≤ N → Nn N ⊆ Nn (N + 1)) {N M : ℕ}
    (hN : 1 ≤ N) (hNM : N ≤ M) : Nn N ⊆ Nn M := by
  induction M, hNM using Nat.le_induction with
  | base => exact subset_rfl
  | succ M hM ih => exact ih.trans (hnest M (hN.trans hM))

/-- da hipótese `Σ_N^{𝓛,H} ⊆ 𝒩_{⌈cN⌉}` e do aninhamento: `Σ_{2^r} ⊆ 𝒩_{2^{r+a}}` com
`d = 2^a ≥ c` -/
lemma net_contains {Nn : ℕ → Set (ℝ → ℝ)} (hnest : ∀ N : ℕ, 1 ≤ N → Nn N ⊆ Nn (N + 1)) {c : ℝ}
    (hc : 1 ≤ c) {H : ℕ → ℕ} (hcont : ∀ N : ℕ, 1 ≤ N → Sigma H N ⊆ Nn ⌈c * N⌉₊) (r : ℕ) :
    Sigma H (2 ^ r) ⊆ Nn (2 ^ (r + ⌈c⌉₊)) := by
  have hn1 : (1 : ℝ) ≤ ((2 ^ r : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_two_pow
  have h1 : 1 ≤ ⌈c * ((2 ^ r : ℕ) : ℝ)⌉₊ := Nat.one_le_ceil_iff.mpr (by nlinarith)
  have h2 : ⌈c * ((2 ^ r : ℕ) : ℝ)⌉₊ ≤ 2 ^ (r + ⌈c⌉₊) := by
    apply Nat.ceil_le.mpr
    have hc2 : c ≤ ((2 ^ ⌈c⌉₊ : ℕ) : ℝ) :=
      (Nat.le_ceil c).trans (by exact_mod_cast (Nat.lt_two_pow_self (n := ⌈c⌉₊)).le)
    push_cast at hc2 hn1 ⊢
    rw [pow_add, mul_comm ((2 : ℝ) ^ r)]
    exact mul_le_mul_of_nonneg_right hc2 (by positivity)
  exact (hcont (2 ^ r) Nat.one_le_two_pow).trans (nest_mono hnest h1 h2)

/-- **Teorema IV.5.14 (reversibilidade estável por inclusão de redes).** Seja `(𝒩_N)` uma
família de funções aninhada no orçamento (`0 ∈ 𝒩_N`, `𝒩_N ⊆ 𝒩_{N+1}`, `N ≥ 1`); o enunciado
vale para qualquer família de funções, em particular para as realizadas por redes ReLU. Se,
para alguma constante `c ≥ 1`, `Σ_N^{𝓛,H} ⊆ 𝒩_{⌈cN⌉}` (`N ≥ 1`) sob a agenda `H` em questão,
então substituir `𝓡_N^{𝓛,H}` por `𝓡_N^{𝒩}` (`realG 𝒩`) preserva as igualdades do
Teorema IV.5.13: `B^s_{∞,q}([0,1]) = {f ∈ C : ‖(2^{rs} 𝓡^{𝒩}_{2^r}(f))_{r ≥ 1}‖_{ℓ^q} < ∞}`
sob cada uma das agendas `H_{s,0}` (`q = ∞`; `q < ∞` e `s < 1`), `H_{s,κ}` (`q < ∞`,
`1 ≤ s`, `κ > 1/q`) e `H̃_{s,η}`. -/
theorem architecture_stable_reversibility {s : ℝ} (hs : 0 < s) (hs2 : s < 2)
    (Nn : ℕ → Set (ℝ → ℝ)) (h0 : ∀ N : ℕ, 1 ≤ N → (0 : ℝ → ℝ) ∈ Nn N)
    (hnest : ∀ N : ℕ, 1 ≤ N → Nn N ⊆ Nn (N + 1)) {c : ℝ} (hc : 1 ≤ c) :
    ((∀ N : ℕ, 1 ≤ N → Sigma (Hsk s 0) N ⊆ Nn ⌈c * N⌉₊) → BesovInfSet 0 0 s = RGInf s Nn) ∧
    (∀ q : ℝ, 0 < q → s < 1 → (∀ N : ℕ, 1 ≤ N → Sigma (Hsk s 0) N ⊆ Nn ⌈c * N⌉₊) →
      BesovQSet 0 0 s q = RGQ s q Nn) ∧
    (∀ q κ : ℝ, 0 < q → 1 ≤ s → 1 / q < κ →
      (∀ N : ℕ, 1 ≤ N → Sigma (Hsk s κ) N ⊆ Nn ⌈c * N⌉₊) → BesovQSet 0 0 s q = RGQ s q Nn) ∧
    (∀ q η : ℝ, 0 < q → 1 ≤ s → 0 < η →
      (∀ N : ℕ, 1 ≤ N → Sigma (HtilK 0 0 s η) N ⊆ Nn ⌈c * N⌉₊) →
      BesovQSet 0 0 s q = RGQ s q Nn) := by
  have hz : ∀ r : ℕ, (0 : ℝ → ℝ) ∈ Nn (2 ^ r) := fun r => h0 _ Nat.one_le_two_pow
  refine ⟨fun hcont => ?_, fun q hq hs1 hcont => ?_, fun q κ hq hs1 hκ hcont => ?_,
    fun q η hq hs1 hη hcont => ?_⟩
  · rw [Hsk_eq_Hgen] at hcont
    exact besov_eq_RGInf hs hs2 le_rfl le_rfl le_rfl hz (net_contains hnest hc hcont)
  · rw [Hsk_eq_Hgen] at hcont
    exact besov_eq_RGQ hs hs2 hq le_rfl le_rfl le_rfl
      (gam_sum_geom (by rw [max_eq_left hs1.le]; linarith) le_rfl hq) hz
      (net_contains hnest hc hcont)
  · rw [Hsk_eq_Hgen] at hcont
    exact besov_eq_RGQ hs hs2 hq le_rfl le_rfl (lt_trans (by positivity) hκ).le
      (gam_sum_log (by rw [max_eq_right hs1]; linarith) hq ((div_lt_iff₀ hq).mp hκ)) hz
      (net_contains hnest hc hcont)
  · rw [HtilK_eq] at hcont
    exact besov_eq_RGQ hs hs2 hq le_rfl (max_le_max le_rfl (by linarith)) le_rfl
      (gam_sum_geom (by have := le_max_right 1 (s + η); linarith) le_rfl hq) hz
      (net_contains hnest hc hcont)

end Pendencias.Jackson
