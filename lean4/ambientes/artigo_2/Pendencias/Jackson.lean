import Pendencias.Inversa

/-!
# IV.4.1 — Jackson racional com altura explícita

-- ITEM: IV.4.1

Objetos do Artigo 3, §4, sobre uma raiz diádica geral `K = J_{k₀,m₀}`, `L = |K| = 2^{-k₀}`:

* `distOn a b f g = ‖f - g‖_{∞,[a,b]}` e `omega2On a b f t = ω₂(f,t)_{∞,[a,b]}`
  (eq. second-modulus-direct), em `ENNReal`; `distK`, `omega2K` são os casos `[a,b] = K`;
* `bnormInf`, `bnormQ`: a quase-norma diádica `‖f‖*_{B^s_{∞,q}(K)}` da eq. (dyadic-besov-norm);
  `BesovInfK`, `BesovQK`: as classes `B^s_{∞,q}(K) ⊂ C(K)`;
* `AdmK k₀ m₀ N H`: representações de `𝒜_{N,H}(K)`;
* `IsWhitney C_W`: a desigualdade de Whitney de ordem dois (eq. whitney-direct) com constante
  `C_W`; `whitney_one` prova que `C_W = 1` é admissível (logo a hipótese não é vazia);
* `CK k₀ m₀ = 4(k₀ + |m₀| + 2)` (eq. height-schedule-constants).

Resultados: `rational_jackson_height` (primeira parte do lema) e `rational_jackson_uniform`
(versão uniforme sobre bolas, com `A_{K,s} = 16·2^{k₀} + |m₀| + 2`, que nem depende de `s`).
-/

namespace Pendencias.Jackson

open Set Artigo LTree Pendencias Pendencias.Agenda

/-! ## Distância uniforme e segundo módulo em um intervalo -/

/-- `‖f - g‖_{∞,[a,b]}` em `ENNReal` (mesma fórmula de `Agenda.distInf`, que é o caso `[0,1]`). -/
noncomputable def distOn (a b : ℝ) (f g : ℝ → ℝ) : ENNReal :=
  ⨆ x ∈ Icc a b, ENNReal.ofReal |f x - g x|

/-- `ω₂(f,t)_{∞,[a,b]} = sup_{0<h≤t, x, x+2h ∈ [a,b]} |f(x+2h) - 2f(x+h) + f(x)|`
(eq. second-modulus-direct; mesma fórmula de `Agenda.omega2`, que é o caso `[0,1]`). -/
noncomputable def omega2On (a b : ℝ) (f : ℝ → ℝ) (t : ℝ) : ENNReal :=
  ⨆ h : ℝ, ⨆ (_ : 0 < h ∧ h ≤ t), ⨆ x : ℝ, ⨆ (_ : a ≤ x ∧ x + 2 * h ≤ b),
    ENNReal.ofReal |f (x + 2 * h) - 2 * f (x + h) + f x|

/-- `‖f - g‖_{∞,K}`, `K = J_{k₀,m₀}` -/
noncomputable def distK (k0 : ℕ) (m0 : ℤ) (f g : ℝ → ℝ) : ENNReal :=
  distOn (cL k0 m0) (cR k0 m0) f g

/-- `ω₂(f,t)_{∞,K}`, `K = J_{k₀,m₀}` -/
noncomputable def omega2K (k0 : ℕ) (m0 : ℤ) (f : ℝ → ℝ) (t : ℝ) : ENNReal :=
  omega2On (cL k0 m0) (cR k0 m0) f t

lemma le_distOn {a b : ℝ} {f g : ℝ → ℝ} {x : ℝ} (hx : x ∈ Icc a b) :
    ENNReal.ofReal |f x - g x| ≤ distOn a b f g :=
  le_iSup₂ (f := fun x (_ : x ∈ Icc a b) => ENNReal.ofReal |f x - g x|) x hx

lemma le_omega2On {a b : ℝ} {f : ℝ → ℝ} {t h x : ℝ} (hh : 0 < h ∧ h ≤ t)
    (hx : a ≤ x ∧ x + 2 * h ≤ b) :
    ENNReal.ofReal |f (x + 2 * h) - 2 * f (x + h) + f x| ≤ omega2On a b f t :=
  le_iSup₂_of_le h hh (le_iSup₂_of_le x hx le_rfl)

lemma omega2On_mono {a b a' b' t t' : ℝ} (ha : a ≤ a') (hb : b' ≤ b) (ht : t' ≤ t) (f : ℝ → ℝ) :
    omega2On a' b' f t' ≤ omega2On a b f t :=
  iSup_le fun _ => iSup_le fun hh => iSup_le fun _ => iSup_le fun hx =>
    le_omega2On ⟨hh.1, hh.2.trans ht⟩ ⟨ha.trans hx.1, hx.2.trans hb⟩

lemma omega2On_le_of_bound {a b M : ℝ} {f : ℝ → ℝ} (hf : ∀ x ∈ Icc a b, |f x| ≤ M) (t : ℝ) :
    omega2On a b f t ≤ ENNReal.ofReal (4 * M) := by
  refine iSup_le fun h => iSup_le fun hh => iSup_le fun x => iSup_le fun hx => ?_
  apply ENNReal.ofReal_le_ofReal
  have m0 := hf x ⟨hx.1, by linarith [hh.1]⟩
  have m1 := hf (x + h) ⟨by linarith [hh.1], by linarith [hh.1]⟩
  have m2 := hf (x + 2 * h) ⟨by linarith [hh.1], hx.2⟩
  rw [abs_le] at m0 m1 m2 ⊢
  constructor <;> linarith

lemma distOn_le_of_bound {a b M : ℝ} {f g : ℝ → ℝ} (h : ∀ x ∈ Icc a b, |f x - g x| ≤ M) :
    distOn a b f g ≤ ENNReal.ofReal M :=
  iSup₂_le fun x hx => ENNReal.ofReal_le_ofReal (h x hx)

/-- de `‖f‖_{∞,[a,b]} < ∞` para a cota pontual -/
lemma abs_le_of_distOn {a b : ℝ} {f : ℝ → ℝ} (h : distOn a b f 0 ≠ ⊤) {x : ℝ} (hx : x ∈ Icc a b) :
    |f x| ≤ (distOn a b f 0).toReal := by
  have := le_distOn (f := f) (g := 0) hx
  simp only [Pi.zero_apply, sub_zero] at this
  exact (ENNReal.ofReal_le_iff_le_toReal h).mp this

lemma abs_second_le_of_omega2On {a b : ℝ} {f : ℝ → ℝ} {t : ℝ} (hfin : omega2On a b f t ≠ ⊤)
    {h x : ℝ} (hh : 0 < h ∧ h ≤ t) (hx : a ≤ x ∧ x + 2 * h ≤ b) :
    |f (x + 2 * h) - 2 * f (x + h) + f x| ≤ (omega2On a b f t).toReal :=
  (ENNReal.ofReal_le_iff_le_toReal hfin).mp (le_omega2On hh hx)

lemma omega2On_ne_top_of_continuousOn {a b : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (t : ℝ) : omega2On a b f t ≠ ⊤ := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  exact (lt_of_le_of_lt (omega2On_le_of_bound (M := C) (fun x hx => by
    simpa [Real.norm_eq_abs] using hC x hx) t) ENNReal.ofReal_lt_top).ne

/-! ## Desigualdade de Whitney de ordem dois -/

/-- `C_W` é uma constante de Whitney de ordem dois (eq. whitney-direct): em todo intervalo
compacto `J = [a,b]` e para toda `f ∈ C(J)`,
`inf_{ℓ afim} ‖f - ℓ‖_{∞,J} ≤ C_W ω₂(f,|J|)_{∞,J}`. O ínfimo é escrito com `ε > 0` arbitrário. -/
def IsWhitney (CW : ℝ) : Prop :=
  0 ≤ CW ∧ ∀ (a b : ℝ) (f : ℝ → ℝ), a < b → ContinuousOn f (Icc a b) → ∀ ε : ℝ, 0 < ε →
    ∃ p q : ℝ, ∀ x ∈ Icc a b, |f x - (p + q * x)| ≤ CW * (omega2On a b f (b - a)).toReal + ε

/-- o interpolador nos extremos reproduz funções afins e tem norma `1`: seu erro é no máximo
duas vezes a melhor aproximação afim, logo `≤ 2 C_W ω₂(f,|J|)_J`. -/
lemma interp_le_whitney {CW : ℝ} (hW : IsWhitney CW) {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) {x : ℝ} (hx : x ∈ Icc a b) :
    |f x - linInterp f a b x| ≤ 2 * CW * (omega2On a b f (b - a)).toReal := by
  set W := (omega2On a b f (b - a)).toReal
  have hne : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  have hba : 0 < b - a := sub_pos.mpr hab
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨p, q, hpq⟩ := hW.2 a b f hab hf (ε / 2) (by positivity)
  set θ := (x - a) / (b - a)
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith [hx.1]) hba.le
  have hθ1 : θ ≤ 1 := by
    rw [div_le_one hba]; linarith [hx.2]
  have e : f x - linInterp f a b x =
      (f x - (p + q * x)) - (1 - θ) * (f a - (p + q * a)) - θ * (f b - (p + q * b)) := by
    simp only [linInterp, θ]; field_simp; ring
  have h1 := hpq x hx
  have h2 := hpq a ⟨le_rfl, hab.le⟩
  have h3 := hpq b ⟨hab.le, le_rfl⟩
  rw [e]
  have h4 : |(1 - θ) * (f a - (p + q * a))| ≤ (1 - θ) * (CW * W + ε / 2) := by
    rw [abs_mul, abs_of_nonneg (by linarith)]
    exact mul_le_mul_of_nonneg_left h2 (by linarith)
  have h5 : |θ * (f b - (p + q * b))| ≤ θ * (CW * W + ε / 2) := by
    rw [abs_mul, abs_of_nonneg hθ0]
    exact mul_le_mul_of_nonneg_left h3 hθ0
  calc |f x - (p + q * x) - (1 - θ) * (f a - (p + q * a)) - θ * (f b - (p + q * b))|
      ≤ |f x - (p + q * x)| + |(1 - θ) * (f a - (p + q * a))| + |θ * (f b - (p + q * b))| := by
        have := abs_sub (f x - (p + q * x) - (1 - θ) * (f a - (p + q * a))) (θ * (f b - (p + q * b)))
        have := abs_sub (f x - (p + q * x)) ((1 - θ) * (f a - (p + q * a)))
        linarith
    _ ≤ (CW * W + ε / 2) + (1 - θ) * (CW * W + ε / 2) + θ * (CW * W + ε / 2) := by linarith
    _ = 2 * CW * W + ε := by ring

/-- **Whitney de ordem dois com `C_W = 1`**: o interpolador afim nos extremos já satisfaz
`‖f - P f‖_{∞,J} ≤ ω₂(f,|J|)_J`. -/
theorem whitney_one : IsWhitney 1 := by
  refine ⟨zero_le_one, fun a b f hab hf ε hε => ?_⟩
  set σ := (f b - f a) / (b - a)
  refine ⟨f a - σ * a, σ, fun x hx => ?_⟩
  set W := (omega2On a b f (b - a)).toReal
  have hfin := omega2On_ne_top_of_continuousOn hf (b - a)
  have hW0 : 0 ≤ W := ENNReal.toReal_nonneg
  have hne : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  set g : ℝ → ℝ := fun y => f y - (f a - σ * a + σ * y)
  have hga : g a = 0 := by simp only [g]; ring
  have hgb : g b = 0 := by simp only [g, σ]; field_simp; ring
  have hgc : ContinuousOn (fun y => |g y|) (Icc a b) :=
    (hf.sub (continuousOn_const.add (continuousOn_const.mul continuousOn_id))).abs
  obtain ⟨z, hz, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨a, ⟨le_rfl, hab.le⟩⟩ hgc
  have hmax' : ∀ y ∈ Icc a b, |g y| ≤ |g z| := fun y hy => hmax hy
  -- segundas diferenças de `g` e de `f` coincidem
  have hd : ∀ y h : ℝ, g (y + 2 * h) - 2 * g (y + h) + g y =
      f (y + 2 * h) - 2 * f (y + h) + f y := by
    intro y h; simp only [g]; ring
  have hE : |g z| ≤ W := by
    rcases le_total (z - a) (b - z) with hc | hc
    · rcases eq_or_lt_of_le (sub_nonneg.mpr hz.1) with h0 | h0
      · have : z = a := by linarith
        rw [this, hga, abs_zero]; exact hW0
      · have h2 := abs_second_le_of_omega2On hfin (h := z - a) (x := a) ⟨h0, by linarith [hz.2]⟩
          ⟨le_rfl, by linarith⟩
        rw [← hd, hga, show a + (z - a) = z by ring] at h2
        have h3 := hmax' (a + 2 * (z - a)) ⟨by linarith, by linarith⟩
        have h4 : 2 * |g z| ≤ |g (a + 2 * (z - a)) - 2 * g z + 0| + |g (a + 2 * (z - a))| := by
          have := abs_sub (g (a + 2 * (z - a))) (g (a + 2 * (z - a)) - 2 * g z + 0)
          rw [show g (a + 2 * (z - a)) - (g (a + 2 * (z - a)) - 2 * g z + 0) = 2 * g z by ring,
            abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at this
          linarith
        linarith
    · rcases eq_or_lt_of_le (sub_nonneg.mpr hz.2) with h0 | h0
      · have : z = b := by linarith
        rw [this, hgb, abs_zero]; exact hW0
      · have h2 := abs_second_le_of_omega2On hfin (h := b - z) (x := b - 2 * (b - z))
          ⟨h0, by linarith [hz.1]⟩ ⟨by linarith, by linarith⟩
        rw [← hd, show b - 2 * (b - z) + 2 * (b - z) = b by ring, hgb,
          show b - 2 * (b - z) + (b - z) = z by ring] at h2
        have h3 := hmax' (b - 2 * (b - z)) ⟨by linarith, by linarith⟩
        have h4 : 2 * |g z| ≤ |0 - 2 * g z + g (b - 2 * (b - z))| + |g (b - 2 * (b - z))| := by
          have := abs_sub (g (b - 2 * (b - z))) (0 - 2 * g z + g (b - 2 * (b - z)))
          rw [show g (b - 2 * (b - z)) - (0 - 2 * g z + g (b - 2 * (b - z))) = 2 * g z by ring,
            abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at this
          linarith
        linarith
  have : |f x - (f a - σ * a + σ * x)| ≤ |g z| := hmax' x hx
  linarith

/-! ## Besov diádico e classes admissíveis sobre `K` -/

/-- termo `2^{rs} ω₂(f, L 2^{-r})_{∞,K}`, `L = 2^{-k₀}` -/
noncomputable def btermK (k0 : ℕ) (m0 : ℤ) (s : ℝ) (f : ℝ → ℝ) (r : ℕ) : ENNReal :=
  ENNReal.ofReal (((2 : ℝ) ^ r) ^ s) * omega2K k0 m0 f ((2 : ℝ) ^ (k0 + r))⁻¹

/-- `‖f‖*_{B^s_{∞,∞}(K)}` (eq. dyadic-besov-norm, `q = ∞`) -/
noncomputable def bnormInf (k0 : ℕ) (m0 : ℤ) (s : ℝ) (f : ℝ → ℝ) : ENNReal :=
  distK k0 m0 f 0 + ⨆ r : ℕ, btermK k0 m0 s f r

/-- `‖f‖*_{B^s_{∞,q}(K)}` (eq. dyadic-besov-norm, `0 < q < ∞`) -/
noncomputable def bnormQ (k0 : ℕ) (m0 : ℤ) (s q : ℝ) (f : ℝ → ℝ) : ENNReal :=
  distK k0 m0 f 0 + (∑' r : ℕ, btermK k0 m0 s f r ^ q) ^ (1 / q)

/-- `f ∈ B^s_{∞,∞}(K)`: o texto define a quase-norma para `f ∈ C(K)`, logo a classe é
`{f ∈ C(K) : ‖f‖* < ∞}`. -/
def BesovInfK (k0 : ℕ) (m0 : ℤ) (s : ℝ) (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (cellIcc k0 m0) ∧ bnormInf k0 m0 s f < ⊤

/-- `f ∈ B^s_{∞,q}(K)`, `0 < q < ∞` -/
def BesovQK (k0 : ℕ) (m0 : ℤ) (s q : ℝ) (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (cellIcc k0 m0) ∧ bnormQ k0 m0 s q f < ⊤

/-- representações admissíveis de `𝒜_{N,H}(K)`: raiz `K = J_{k₀,m₀}`, no máximo `N` folhas e
altura atômica no máximo `H` (o caso `(k₀,m₀) = (0,0)` é `Artigo.AdmNH`). -/
def AdmK (k0 : ℕ) (m0 : ℤ) (N H : ℕ) (T : LTree) : Prop :=
  WF k0 m0 T ∧ T.numLeaves ≤ N ∧ T.maxHeight ≤ H

/-- `C_K = 4(k₀ + |m₀| + 2)` (eq. height-schedule-constants) -/
noncomputable def CK (k0 : ℕ) (m0 : ℤ) : ℝ := 4 * ((k0 : ℝ) + |(m0 : ℝ)| + 2)

lemma CK_ge (k0 : ℕ) (m0 : ℤ) : 8 ≤ CK k0 m0 := by
  unfold CK
  have : (0 : ℝ) ≤ k0 := Nat.cast_nonneg _
  have := abs_nonneg (m0 : ℝ)
  linarith

/-! ### Caso `K = [0,1]` -/

lemma cL00 : cL 0 0 = 0 := by simp [cL]
lemma cR00 : cR 0 0 = 1 := by simp [cR]

lemma distK_zero (f g : ℝ → ℝ) : distK 0 0 f g = distInf f g := by
  unfold distK distOn distInf; rw [cL00, cR00]

lemma omega2K_zero (f : ℝ → ℝ) (t : ℝ) : omega2K 0 0 f t = omega2 f t := by
  unfold omega2K omega2On omega2; rw [cL00, cR00]

lemma admK_zero (N H : ℕ) (T : LTree) : AdmK 0 0 N H T ↔ AdmNH N H T := Iff.rfl

lemma btermK_zero (s : ℝ) (f : ℝ → ℝ) (r : ℕ) : btermK 0 0 s f r = bterm s f r := by
  unfold btermK bterm; rw [omega2K_zero, zero_add]

/-! ## Valores nodais em grades alternadas de passo `1/Q`, `Q = 2^e` -/

/-- numerador inteiro `b_n` do valor nodal `v_n = b_n/(2Q)`: ponto da grade
`Q⁻¹(ℤ + (n mod 2)/2)` mais próximo de `f(t_n)`, `t_n = n 2^{-K}`; empates para baixo. -/
noncomputable def bq (f : ℝ → ℝ) (e K : ℕ) (n : ℤ) : ℤ :=
  2 * ⌈(2 : ℝ) ^ e * f (cL K n) - ((n % 2 : ℤ) : ℝ) / 2 - 1 / 2⌉ + n % 2

/-- valores nodais `v_n` -/
noncomputable def vq (f : ℝ → ℝ) (e K : ℕ) (n : ℤ) : ℚ := (bq f e K n : ℚ) / (2 * 2 ^ e)

lemma vq_cast (f : ℝ → ℝ) (e K : ℕ) (n : ℤ) :
    ((vq f e K n : ℚ) : ℝ) = (bq f e K n : ℝ) / (2 * 2 ^ e) := by
  simp [vq]

lemma bq_mod (f : ℝ → ℝ) (e K : ℕ) (n : ℤ) : bq f e K n % 2 = n % 2 := by
  unfold bq; omega

lemma vq_ne (f : ℝ → ℝ) (e K : ℕ) (n : ℤ) : vq f e K n ≠ vq f e K (n + 1) := by
  intro h
  unfold vq at h
  have h2 : (bq f e K n : ℚ) = bq f e K (n + 1) := by
    have : (2 * 2 ^ e : ℚ) ≠ 0 := by positivity
    field_simp at h; exact_mod_cast h
  have h3 : bq f e K n = bq f e K (n + 1) := by exact_mod_cast h2
  have := bq_mod f e K n; have := bq_mod f e K (n + 1)
  omega

lemma vq_good (f : ℝ → ℝ) (e K r : ℕ) (m : ℤ) : GoodVals (vq f e K) r m :=
  fun n _ _ => vq_ne f e K n

/-- erro de quantização `≤ 1/(2Q)` -/
lemma vq_err (f : ℝ → ℝ) (e K : ℕ) (n : ℤ) :
    |f (cL K n) - vq f e K n| ≤ 1 / (2 * 2 ^ e) := by
  rw [vq_cast]
  set p : ℝ := ((n % 2 : ℤ) : ℝ)
  set z := (2 : ℝ) ^ e * f (cL K n) - p / 2
  set c := ⌈z - 1 / 2⌉
  have h1 := Int.le_ceil (z - 1 / 2)
  have h2 := Int.ceil_lt_add_one (z - 1 / 2)
  have hn : (0 : ℝ) < 2 ^ e := by positivity
  have hb : (bq f e K n : ℝ) = 2 * (c : ℝ) + p := by
    simp only [bq, c, z, p]; push_cast; ring
  have e1 : f (cL K n) - (bq f e K n : ℝ) / (2 * 2 ^ e) = (z - c) / 2 ^ e := by
    rw [hb]; simp only [z]; field_simp; ring
  rw [e1, abs_div, abs_of_pos hn, div_le_div_iff₀ hn (by positivity)]
  have : |z - c| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
  nlinarith

lemma bq_cast (f : ℝ → ℝ) (e K : ℕ) (n : ℤ) :
    (bq f e K n : ℝ) = 2 * 2 ^ e * ((vq f e K n : ℚ) : ℝ) := by
  rw [vq_cast]; field_simp

/-- `|b_n| ≤ 2QR + 1` (eq. general-b-bound) -/
lemma bq_abs_le {f : ℝ → ℝ} {R : ℝ} {e K : ℕ} {n : ℤ} (hf : |f (cL K n)| ≤ R) :
    |(bq f e K n : ℝ)| ≤ 2 * R * 2 ^ e + 1 := by
  have he := vq_err f e K n
  have hn : (0 : ℝ) < 2 ^ e := by positivity
  rw [bq_cast, abs_mul, abs_of_pos (by positivity)]
  have hv : |((vq f e K n : ℚ) : ℝ)| ≤ R + 1 / (2 * 2 ^ e) := by
    calc |((vq f e K n : ℚ) : ℝ)| = |f (cL K n) - (f (cL K n) - vq f e K n)| := by ring_nf
      _ ≤ |f (cL K n)| + |f (cL K n) - vq f e K n| := abs_sub _ _
      _ ≤ _ := by linarith
  calc 2 * 2 ^ e * |((vq f e K n : ℚ) : ℝ)| ≤ 2 * 2 ^ e * (R + 1 / (2 * 2 ^ e)) := by gcongr
    _ = _ := by field_simp

/-- diferença de valores nodais vizinhos -/
lemma vq_diff_le (f : ℝ → ℝ) (e K : ℕ) (n : ℤ) :
    |((vq f e K (n + 1) : ℚ) : ℝ) - vq f e K n| ≤
      |f (cL K (n + 1)) - f (cL K n)| + 1 / 2 ^ e := by
  have he1 := vq_err f e K n
  have he2 := vq_err f e K (n + 1)
  have e1 : ((vq f e K (n + 1) : ℚ) : ℝ) - vq f e K n = (f (cL K (n + 1)) - f (cL K n))
      - (f (cL K (n + 1)) - vq f e K (n + 1)) + (f (cL K n) - vq f e K n) := by ring
  rw [e1]
  have hh : (1 : ℝ) / (2 * 2 ^ e) + 1 / (2 * 2 ^ e) = 1 / 2 ^ e := by field_simp; ring
  calc _ ≤ |(f (cL K (n + 1)) - f (cL K n)) - (f (cL K (n + 1)) - vq f e K (n + 1))|
        + |f (cL K n) - vq f e K n| := abs_add_le _ _
    _ ≤ |f (cL K (n + 1)) - f (cL K n)| + |f (cL K (n + 1)) - vq f e K (n + 1)|
        + |f (cL K n) - vq f e K n| := by gcongr; exact abs_sub _ _
    _ ≤ _ := by linarith

/-! ## Alturas dos átomos da construção -/

lemma ht_div_le_nat (p : ℤ) (q : ℕ) (hq : 0 < q) {H : ℕ} (hp : |(p : ℝ)| ≤ H) (hqH : q ≤ H) :
    ht ((p : ℚ) / q) ≤ H := by
  have := ht_cast_le_of hq hp (by exact_mod_cast hqH)
  exact_mod_cast this

/-- eq. (general-atom-parameters): cada átomo da malha tem altura `≤ H`, desde que
`8(R+1)Q ≤ H`, a geometria caiba em `H` e a inclinação inteira (caso `2^K > 2Q`) caiba em `H`. -/
lemma atom_height_le {f : ℝ → ℝ} {R : ℝ} {e K : ℕ} {n : ℤ} {H : ℕ} (hR : 0 ≤ R)
    (hf0 : |f (cL K n)| ≤ R) (hf1 : |f (cL K (n + 1))| ≤ R)
    (hQ : 8 * (R + 1) * 2 ^ e ≤ (H : ℝ)) (hk : K + 1 ≤ H) (hm : n.natAbs + 1 ≤ H)
    (hsl : (2 : ℝ) ^ K * (|f (cL K (n + 1)) - f (cL K n)| + 1 / 2 ^ e) ≤ H) :
    (interpAtom (vq f e K) K n).height ≤ H := by
  have hne := vq_ne f e K n
  have hA : interpAtom (vq f e K) K n =
      Atom.ofEndpoints K n (vq f e K n) (vq f e K (n + 1)) hne := by
    simp [interpAtom, hne]
  have he1 : (1 : ℝ) ≤ 2 ^ e := one_le_pow₀ (by norm_num)
  have hb0 := bq_abs_le (e := e) hf0
  have hb1 := bq_abs_le (e := e) hf1
  have hRe : 0 ≤ R * 2 ^ e := by positivity
  have hQ' : 8 * (R * 2 ^ e) + 8 * 2 ^ e ≤ (H : ℝ) := by
    linarith [show 8 * (R + 1) * 2 ^ e = 8 * (R * 2 ^ e) + 8 * (2 : ℝ) ^ e by ring]
  have hy0 : (interpAtom (vq f e K) K n).y0 =
      ((bq f e K n + bq f e K (n + 1) : ℤ) : ℚ) / ((4 * 2 ^ e : ℕ) : ℚ) := by
    rw [hA]; simp only [Atom.ofEndpoints, vq]; push_cast; field_simp; ring
  have hs : (interpAtom (vq f e K) K n).s =
      (((bq f e K (n + 1) - bq f e K n) * 2 ^ (K - (e + 1)) : ℤ) : ℚ) /
        ((2 ^ (e + 1 - K) : ℕ) : ℚ) := by
    rw [hA]; simp only [Atom.ofEndpoints, vq]; push_cast
    have hpow : (2 : ℚ) ^ K * 2 ^ (e + 1 - K) = 2 ^ (K - (e + 1)) * (2 * 2 ^ e) := by
      have h1 : (2 : ℚ) * 2 ^ e = 2 ^ (e + 1) := by ring
      rw [h1, ← pow_add, ← pow_add]; congr 1; omega
    rw [eq_div_iff (by positivity)]
    calc (2 : ℚ) ^ K * ((bq f e K (n + 1) : ℚ) / (2 * 2 ^ e) - (bq f e K n : ℚ) / (2 * 2 ^ e)) *
          2 ^ (e + 1 - K)
        = ((bq f e K (n + 1) : ℚ) - bq f e K n) / (2 * 2 ^ e) * (2 ^ K * 2 ^ (e + 1 - K)) := by
          ring
      _ = ((bq f e K (n + 1) : ℚ) - bq f e K n) / (2 * 2 ^ e) *
            (2 ^ (K - (e + 1)) * (2 * 2 ^ e)) := by rw [hpow]
      _ = ((bq f e K (n + 1) : ℚ) - bq f e K n) * 2 ^ (K - (e + 1)) := by field_simp
  have hH2 : 2 ≤ H := by
    have : (2 : ℝ) ≤ H := by linarith
    exact_mod_cast this
  rw [Atom.height_le_iff]
  simp only [interpAtom_k, interpAtom_m]
  refine ⟨hH2, hk, hm, ?_, ?_⟩
  · rw [hy0]
    apply ht_div_le_nat _ _ (by positivity)
    · push_cast
      calc |(bq f e K n : ℝ) + bq f e K (n + 1)|
          ≤ |(bq f e K n : ℝ)| + |(bq f e K (n + 1) : ℝ)| := abs_add_le _ _
        _ ≤ (H : ℝ) := by linarith
    · have : ((4 * 2 ^ e : ℕ) : ℝ) ≤ H := by push_cast; linarith
      exact_mod_cast this
  · rw [hs]
    apply ht_div_le_nat _ _ (by positivity)
    · by_cases hc : K ≤ e + 1
      · have h0 : K - (e + 1) = 0 := by omega
        rw [h0, pow_zero, mul_one]
        push_cast
        calc |(bq f e K (n + 1) : ℝ) - bq f e K n|
            ≤ |(bq f e K (n + 1) : ℝ)| + |(bq f e K n : ℝ)| := abs_sub _ _
          _ ≤ (H : ℝ) := by linarith
      · have hK : (2 : ℝ) ^ K = 2 ^ (K - (e + 1)) * (2 * 2 ^ e) := by
          have h1 : (2 : ℝ) * 2 ^ e = 2 ^ (e + 1) := by ring
          rw [h1, ← pow_add]; congr 1; omega
        have hp : (((bq f e K (n + 1) - bq f e K n) * 2 ^ (K - (e + 1)) : ℤ) : ℝ) =
            2 ^ K * (((vq f e K (n + 1) : ℚ) : ℝ) - vq f e K n) := by
          rw [vq_cast, vq_cast, hK]; push_cast; field_simp
        rw [hp, abs_mul, abs_of_pos (by positivity)]
        exact (mul_le_mul_of_nonneg_left (vq_diff_le f e K n) (by positivity)).trans hsl
    · have h1 : 2 ^ (e + 1 - K) ≤ 2 ^ (e + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : ((2 ^ (e + 1) : ℕ) : ℝ) ≤ H := by push_cast; rw [pow_succ]; linarith
      exact h1.trans (by exact_mod_cast h2)

/-- os nós `t_n = n 2^{-(k₀+r)}`, `2^r m₀ ≤ n ≤ 2^r(m₀+1)`, estão em `K` -/
lemma node_mem {k0 r : ℕ} {m0 n : ℤ} (h1 : 2 ^ r * m0 ≤ n) (h2 : n ≤ 2 ^ r * (m0 + 1)) :
    cL (k0 + r) n ∈ cellIcc k0 m0 := by
  rw [cellIcc_eq]; unfold cL cR
  have hp : (0 : ℝ) < 2 ^ r := by positivity
  have hk : (0 : ℝ) < 2 ^ k0 := by positivity
  have h1' : (2 : ℝ) ^ r * m0 ≤ n := by exact_mod_cast h1
  have h2' : (n : ℝ) ≤ 2 ^ r * (m0 + 1) := by exact_mod_cast h2
  rw [pow_add]
  constructor
  · rw [div_le_div_iff₀ hk (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h1' hk.le]
  · rw [div_le_div_iff₀ (by positivity) hk]
    nlinarith [mul_le_mul_of_nonneg_left h2' hk.le]

lemma node_step (K : ℕ) (n : ℤ) : cL K (n + 1) - cL K n = ((2 : ℝ) ^ K)⁻¹ := by
  unfold cL; push_cast; field_simp; ring

/-- janela (Q-window): potência de dois `Q = 2^e` com `8(R+1)Q ≤ H < 16(R+1)Q` -/
lemma exists_Q {R : ℝ} (hR : 0 ≤ R) {H : ℕ} (hH : 16 * (R + 1) ≤ (H : ℝ)) :
    ∃ e : ℕ, 8 * (R + 1) * 2 ^ e ≤ (H : ℝ) ∧ (H : ℝ) < 16 * (R + 1) * 2 ^ e := by
  set x := (H : ℝ) / (8 * (R + 1))
  have hd : (0 : ℝ) < 8 * (R + 1) := by positivity
  have hx2 : 2 ≤ x := by rw [le_div_iff₀ hd]; linarith
  set N := ⌊x⌋₊
  have hN : N ≠ 0 := by
    have : 1 ≤ N := Nat.le_floor (by push_cast; linarith)
    omega
  refine ⟨Nat.log 2 N, ?_, ?_⟩
  · have h1 : (2 ^ Nat.log 2 N : ℕ) ≤ N := Nat.pow_log_le_self 2 hN
    have h2 : ((2 ^ Nat.log 2 N : ℕ) : ℝ) ≤ x :=
      le_trans (by exact_mod_cast h1) (Nat.floor_le (by linarith))
    push_cast at h2
    rw [le_div_iff₀ hd] at h2; linarith
  · have h1 : N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
    have h2 : x < ((2 ^ (Nat.log 2 N + 1) : ℕ) : ℝ) := by
      have := Nat.lt_floor_add_one x
      have h3 : (N : ℝ) + 1 ≤ ((2 ^ (Nat.log 2 N + 1) : ℕ) : ℝ) := by exact_mod_cast h1
      linarith
    push_cast at h2
    rw [div_lt_iff₀ hd, pow_succ] at h2; linarith

/-- núcleo da construção: racionalização com denominador comensurável na malha uniforme de
`2^r` folhas. -/
lemma jackson_core {CW : ℝ} (hW : IsWhitney CW) {k0 r : ℕ} {m0 : ℤ} {f : ℝ → ℝ}
    (hfc : ContinuousOn f (cellIcc k0 m0)) {R : ℝ} (hR : 0 ≤ R)
    (hf : ∀ x ∈ cellIcc k0 m0, |f x| ≤ R) {H : ℕ} (hH : 16 * (R + 1) ≤ (H : ℝ))
    (hk : k0 + r + 1 ≤ H)
    (hm : ∀ n : ℤ, 2 ^ r * m0 ≤ n → n < 2 ^ r * (m0 + 1) → n.natAbs + 1 ≤ H)
    (hsl : ∀ n : ℤ, 2 ^ r * m0 ≤ n → n < 2 ^ r * (m0 + 1) →
      (2 : ℝ) ^ (k0 + r) *
        (|f (cL (k0 + r) (n + 1)) - f (cL (k0 + r) n)| + 16 * (R + 1) / H) ≤ H) :
    ∃ T, AdmK k0 m0 (2 ^ r) H T ∧
      distK k0 m0 f (T.eval k0 m0) ≤
        ENNReal.ofReal (2 * CW) * omega2K k0 m0 f ((2 : ℝ) ^ (k0 + r))⁻¹ +
          ENNReal.ofReal (8 * (R + 1) / H) := by
  obtain ⟨e, he1, he2⟩ := exists_Q hR hH
  have hH0 : (0 : ℝ) < H := by linarith
  have hinv : (1 : ℝ) / 2 ^ e ≤ 16 * (R + 1) / H := by
    rw [div_le_div_iff₀ (by positivity) hH0]; linarith
  have hgood : GoodVals (vq f e (k0 + r)) r m0 := vq_good f e (k0 + r) r m0
  have hWF := uniformTree_WF (vq f e (k0 + r)) r k0 m0 hgood
  refine ⟨uniformTree (vq f e (k0 + r)) r k0 m0,
    ⟨hWF, (uniformTree_numLeaves _ r k0 m0).le, ?_⟩, ?_⟩
  · rw [maxHeight_le_iff]
    intro a ha
    obtain ⟨n, h1, h2, rfl⟩ := uniformTree_leaves _ r k0 m0 a ha
    refine atom_height_le hR (hf _ (node_mem h1 h2.le))
      (hf _ (node_mem (by omega) (by omega))) he1 hk (hm n h1 h2) ?_
    refine le_trans ?_ (hsl n h1 h2)
    gcongr
  · refine iSup₂_le fun x hx => ?_
    obtain ⟨n, h1, h2, hxn, hsub, hbd⟩ := uniformTree_error hgood f (η := 1 / (2 * 2 ^ e))
      (fun n _ _ => vq_err f e (k0 + r) n) x hx
    have hab := cL_lt_cR (k0 + r) n
    have hsub' : cL k0 m0 ≤ cL (k0 + r) n ∧ cR (k0 + r) n ≤ cR k0 m0 :=
      (Icc_subset_Icc_iff hab.le).mp hsub
    have hfJ : ContinuousOn f (Icc (cL (k0 + r) n) (cR (k0 + r) n)) := hfc.mono hsub
    have hw := interp_le_whitney hW hab hfJ hxn
    rw [cell_len] at hw
    have hωJ : omega2On (cL (k0 + r) n) (cR (k0 + r) n) f ((2 : ℝ) ^ (k0 + r))⁻¹ ≤
        omega2K k0 m0 f ((2 : ℝ) ^ (k0 + r))⁻¹ := omega2On_mono hsub'.1 hsub'.2 le_rfl f
    have hfin := omega2On_ne_top_of_continuousOn hfJ ((2 : ℝ) ^ (k0 + r))⁻¹
    have h8 : (1 : ℝ) / (2 * 2 ^ e) ≤ 8 * (R + 1) / H := by
      rw [div_le_div_iff₀ (by positivity) hH0]; linarith
    calc ENNReal.ofReal |f x - (uniformTree (vq f e (k0 + r)) r k0 m0).eval k0 m0 x|
        ≤ ENNReal.ofReal (2 * CW *
            (omega2On (cL (k0 + r) n) (cR (k0 + r) n) f ((2 : ℝ) ^ (k0 + r))⁻¹).toReal +
              1 / (2 * 2 ^ e)) := ENNReal.ofReal_le_ofReal (by linarith)
      _ ≤ ENNReal.ofReal (2 * CW *
            (omega2On (cL (k0 + r) n) (cR (k0 + r) n) f ((2 : ℝ) ^ (k0 + r))⁻¹).toReal) +
            ENNReal.ofReal (1 / (2 * 2 ^ e)) := ENNReal.ofReal_add_le
      _ = ENNReal.ofReal (2 * CW) *
            omega2On (cL (k0 + r) n) (cR (k0 + r) n) f ((2 : ℝ) ^ (k0 + r))⁻¹ +
            ENNReal.ofReal (1 / (2 * 2 ^ e)) := by
          rw [ENNReal.ofReal_mul (by have := hW.1; positivity), ENNReal.ofReal_toReal hfin]
      _ ≤ _ := add_le_add (mul_le_mul_right hωJ _) (ENNReal.ofReal_le_ofReal h8)

/-! ## Lema IV.4.1 -/

/-- **Lema IV.4.1 (Jackson racional com altura explícita)**, primeira parte.
Com `C = 8` absoluto: para `f ∈ B^s_{∞,∞}(K)`, `R = ‖f‖_∞`, e toda constante de Whitney `C_W`,
existe `n₀` tal que, para toda potência de dois `n = 2^r ≥ n₀` e todo inteiro
`H ≥ max{C_K n^{ν_s}, 16(R+1)}` que satisfaça a condição geométrica
(eq. height-geometry-condition), existe `g ∈ 𝒜_{n,H}(K)` com
`‖f - g‖_∞ ≤ 2 C_W ω₂(f, L/n)_{∞,K} + C(R+1)/H`. -/
theorem rational_jackson_height :
    ∃ C : ℝ, 0 < C ∧ ∀ (k0 : ℕ) (m0 : ℤ) (s : ℝ) (f : ℝ → ℝ) (CW : ℝ), 0 < s → s < 2 →
      BesovInfK k0 m0 s f → IsWhitney CW →
      ∃ n0 : ℕ, ∀ r : ℕ, n0 ≤ 2 ^ r → ∀ H : ℕ,
        max (CK k0 m0 * ((2 : ℝ) ^ r) ^ max 1 s) (16 * ((distK k0 m0 f 0).toReal + 1)) ≤ (H : ℝ) →
        (2 ≤ H ∧ k0 + r + 1 ≤ H ∧
          ∀ j : ℤ, 0 ≤ j → j < 2 ^ r → (2 ^ r * m0 + j).natAbs + 1 ≤ H) →
        ∃ T, AdmK k0 m0 (2 ^ r) H T ∧
          distK k0 m0 f (T.eval k0 m0) ≤
            ENNReal.ofReal (2 * CW) * omega2K k0 m0 f ((2 : ℝ) ^ (k0 + r))⁻¹ +
              ENNReal.ofReal (C * ((distK k0 m0 f 0).toReal + 1) / H) := by
  refine ⟨8, by norm_num, fun k0 m0 s f CW _ _ hB hW => ?_⟩
  obtain ⟨hfc, hnorm⟩ := hB
  have hdfin : distK k0 m0 f 0 ≠ ⊤ := (lt_of_le_of_lt le_self_add hnorm).ne
  set R := (distK k0 m0 f 0).toReal
  have hR : 0 ≤ R := ENNReal.toReal_nonneg
  have hf : ∀ x ∈ cellIcc k0 m0, |f x| ≤ R := fun x hx => abs_le_of_distOn hdfin hx
  have hCK := CK_ge k0 m0
  have hε0 : 0 < CK k0 m0 / 2 ^ (k0 + 1) := div_pos (by linarith) (by positivity)
  have huc := (isCompact_Icc : IsCompact (cellIcc k0 m0)).uniformContinuousOn_of_continuous hfc
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδf⟩ := huc _ hε0
  refine ⟨max ⌈(2 : ℝ) ^ k0 * (R + 1)⌉₊ (⌈1 / ((2 : ℝ) ^ k0 * δ)⌉₊ + 1),
    fun r hr H hH hgeo => ?_⟩
  obtain ⟨hH1, hH2⟩ := max_le_iff.mp hH
  have hk0 : (0 : ℝ) < 2 ^ k0 := by positivity
  have hn1 : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
  have hrA : (2 : ℝ) ^ k0 * (R + 1) ≤ 2 ^ r := by
    have h1 : ⌈(2 : ℝ) ^ k0 * (R + 1)⌉₊ ≤ 2 ^ r := (le_max_left _ _).trans hr
    have h2 : ((⌈(2 : ℝ) ^ k0 * (R + 1)⌉₊ : ℕ) : ℝ) ≤ ((2 ^ r : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h2
    exact (Nat.le_ceil _).trans h2
  have hrB : 1 / ((2 : ℝ) ^ k0 * δ) < 2 ^ r := by
    have h1 : ⌈1 / ((2 : ℝ) ^ k0 * δ)⌉₊ + 1 ≤ 2 ^ r := (le_max_right _ _).trans hr
    have h2 : ((⌈1 / ((2 : ℝ) ^ k0 * δ)⌉₊ + 1 : ℕ) : ℝ) ≤ ((2 ^ r : ℕ) : ℝ) := by
      exact_mod_cast h1
    push_cast at h2
    linarith [Nat.le_ceil (1 / ((2 : ℝ) ^ k0 * δ))]
  have hstep : ((2 : ℝ) ^ (k0 + r))⁻¹ < δ := by
    rw [div_lt_iff₀ (by positivity)] at hrB
    rw [inv_lt_comm₀ (by positivity) hδ, pow_add, ← one_div]
    rw [div_lt_iff₀ hδ]
    nlinarith
  have hnν : (2 : ℝ) ^ r ≤ ((2 : ℝ) ^ r) ^ max 1 s :=
    Real.self_le_rpow_of_one_le hn1 (le_max_left 1 s)
  have hHn : CK k0 m0 * 2 ^ r ≤ (H : ℝ) :=
    (mul_le_mul_of_nonneg_left hnν (by linarith)).trans hH1
  have h8n : 8 * (2 : ℝ) ^ r ≤ H := by nlinarith
  have hH0 : (0 : ℝ) < H := by linarith
  refine jackson_core hW hfc hR hf hH2 hgeo.2.1 (fun n h1 h2 => ?_) (fun n h1 h2 => ?_)
  · have e1 : (2 : ℤ) ^ r * (m0 + 1) = 2 ^ r * m0 + 2 ^ r := by ring
    have := hgeo.2.2 (n - 2 ^ r * m0) (by linarith) (by linarith)
    rwa [show 2 ^ r * m0 + (n - 2 ^ r * m0) = n by ring] at this
  · have hx1 : cL (k0 + r) n ∈ cellIcc k0 m0 := node_mem h1 h2.le
    have hx2 : cL (k0 + r) (n + 1) ∈ cellIcc k0 m0 := node_mem (by omega) (by omega)
    have hd := hδf _ hx2 _ hx1 (by
      rw [Real.dist_eq, node_step, abs_of_pos (by positivity)]; exact hstep)
    rw [Real.dist_eq] at hd
    have ha : (2 : ℝ) ^ (k0 + r) * |f (cL (k0 + r) (n + 1)) - f (cL (k0 + r) n)| ≤ H / 2 := by
      calc (2 : ℝ) ^ (k0 + r) * |f (cL (k0 + r) (n + 1)) - f (cL (k0 + r) n)|
          ≤ 2 ^ (k0 + r) * (CK k0 m0 / 2 ^ (k0 + 1)) :=
            mul_le_mul_of_nonneg_left hd.le (by positivity)
        _ = CK k0 m0 * 2 ^ r / 2 := by rw [pow_add, pow_succ]; field_simp
        _ ≤ H / 2 := by linarith
    have hb : (2 : ℝ) ^ (k0 + r) * (16 * (R + 1) / H) ≤ H / 2 := by
      rw [← mul_div_assoc, div_le_iff₀ hH0, pow_add]
      calc (2 : ℝ) ^ k0 * 2 ^ r * (16 * (R + 1)) = 16 * 2 ^ r * (2 ^ k0 * (R + 1)) := by ring
        _ ≤ 16 * 2 ^ r * 2 ^ r := by gcongr
        _ ≤ H / 2 * H := by nlinarith [mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ 8 * 2 ^ r) h8n]
    rw [mul_add]; linarith

/-- a constante `A_{K,s}` da versão uniforme do Lema IV.4.1 (e da agenda calibrada
`Ĥ^{[B]}_{s,κ}` do Corolário IV.4.3): `16·2^{k₀} + |m₀| + 2`; não depende de `s`. -/
noncomputable def AK (k0 : ℕ) (m0 : ℤ) : ℝ := 16 * 2 ^ k0 + |(m0 : ℝ)| + 2

/-- **Lema IV.4.1**, versão uniforme. Existe `A_{K,s} ≥ 1` (aqui `16·2^{k₀} + |m₀| + 2`,
independente de `f` e até de `s`) tal que, se `B ≥ 1`, `‖f‖*_{B^s_{∞,∞}(K)} ≤ B`,
`n = 2^r ≥ 2` e `H ≥ A_{K,s}(B+1) n^{ν_s}`, então a condição geométrica
(eq. height-geometry-condition) é automática e existe `g ∈ 𝒜_{n,H}(K)` com
`‖f - g‖_∞ ≤ 2 C_W ω₂(f, L/n)_{∞,K} + 8(B+1)/H`, sem limiar dependente de `f`. -/
theorem rational_jackson_uniform_explicit (k0 : ℕ) (m0 : ℤ) :
    1 ≤ AK k0 m0 ∧ ∀ (s : ℝ) (f : ℝ → ℝ) (CW B : ℝ), 0 < s → s < 2 → IsWhitney CW → 1 ≤ B →
      ContinuousOn f (cellIcc k0 m0) → bnormInf k0 m0 s f ≤ ENNReal.ofReal B →
      ∀ r : ℕ, 1 ≤ r → ∀ H : ℕ, AK k0 m0 * (B + 1) * ((2 : ℝ) ^ r) ^ max 1 s ≤ (H : ℝ) →
        (2 ≤ H ∧ k0 + r + 1 ≤ H ∧
          ∀ j : ℤ, 0 ≤ j → j < 2 ^ r → (2 ^ r * m0 + j).natAbs + 1 ≤ H) ∧
        ∃ T, AdmK k0 m0 (2 ^ r) H T ∧
          distK k0 m0 f (T.eval k0 m0) ≤
            ENNReal.ofReal (2 * CW) * omega2K k0 m0 f ((2 : ℝ) ^ (k0 + r))⁻¹ +
              ENNReal.ofReal (8 * (B + 1) / H) := by
  have hk0 : (1 : ℝ) ≤ 2 ^ k0 := one_le_pow₀ (by norm_num)
  have hm0 := abs_nonneg (m0 : ℝ)
  unfold AK
  refine ⟨by linarith, fun s f CW B _ _ hW hB hfc hnorm r hr H hH => ?_⟩
  have hB0 : 0 ≤ B := by linarith
  have hf : ∀ x ∈ cellIcc k0 m0, |f x| ≤ B := by
    intro x hx
    have h1 := (le_distOn (f := f) (g := 0) hx).trans ((le_self_add).trans hnorm)
    simpa using (ENNReal.ofReal_le_ofReal_iff hB0).mp h1
  have hn2 : (2 : ℝ) ≤ 2 ^ r := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) hr
  have hnν : (2 : ℝ) ^ r ≤ ((2 : ℝ) ^ r) ^ max 1 s :=
    Real.self_le_rpow_of_one_le (by linarith) (le_max_left 1 s)
  set n : ℝ := 2 ^ r with hn
  set X : ℝ := (B + 1) * n with hX
  have hX2 : 2 * n ≤ X := by rw [hX]; nlinarith
  have hAX : (16 * 2 ^ k0 + |(m0 : ℝ)| + 2) * X ≤ (H : ℝ) := by
    refine le_trans ?_ hH
    rw [hX, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left hnν (by positivity)
  have hXn : 0 ≤ X := by linarith
  have h1 : (2 : ℝ) ^ k0 * (2 * n) ≤ 2 ^ k0 * X := mul_le_mul_of_nonneg_left hX2 (by positivity)
  have h2 : |(m0 : ℝ)| * (2 * n) ≤ |(m0 : ℝ)| * X := mul_le_mul_of_nonneg_left hX2 hm0
  have h3 : n ≤ 2 ^ k0 * n := le_mul_of_one_le_left (by linarith) hk0
  have hHB : 16 * (2 ^ k0 * X) ≤ (H : ℝ) := by nlinarith
  have hXB : (B + 1) ≤ 2 ^ k0 * X := by
    rw [hX]; nlinarith [mul_le_mul hk0 (by linarith : (1 : ℝ) ≤ n) zero_le_one (by positivity),
      mul_nonneg hB0 (by linarith : (0 : ℝ) ≤ 2 ^ k0 * n - 1)]
  have hH16 : 16 * (B + 1) ≤ (H : ℝ) := by linarith
  have hH0 : (0 : ℝ) < H := by linarith
  have hgeoK : k0 + r + 1 ≤ H := by
    have a1 : ((k0 + 1 : ℕ) : ℝ) ≤ 2 ^ k0 := by exact_mod_cast (Nat.lt_two_pow_self (n := k0))
    have a2 : ((r + 1 : ℕ) : ℝ) ≤ n := by rw [hn]; exact_mod_cast (Nat.lt_two_pow_self (n := r))
    have : ((k0 + r + 1 : ℕ) : ℝ) ≤ H := by
      push_cast at a1 a2 ⊢
      nlinarith
    exact_mod_cast this
  have hgeoM : ∀ j : ℤ, 0 ≤ j → j < 2 ^ r → (2 ^ r * m0 + j).natAbs + 1 ≤ H := by
    intro j hj0 hj1
    have hj0' : (0 : ℝ) ≤ j := by exact_mod_cast hj0
    have hj1' : (j : ℝ) < n := by rw [hn]; exact_mod_cast hj1
    have habs : |((2 ^ r * m0 + j : ℤ) : ℝ)| ≤ n * |(m0 : ℝ)| + n := by
      push_cast
      calc |(2 : ℝ) ^ r * m0 + j| ≤ |(2 : ℝ) ^ r * m0| + |(j : ℝ)| := abs_add_le _ _
        _ ≤ n * |(m0 : ℝ)| + n := by
          rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ r), abs_of_nonneg hj0']
          linarith
    have : (((2 ^ r * m0 + j).natAbs + 1 : ℕ) : ℝ) ≤ H := by
      push_cast
      rw [Nat.cast_natAbs, Int.cast_abs]
      nlinarith
    exact_mod_cast this
  have hH2 : 2 ≤ H := by
    have : (2 : ℝ) ≤ H := by linarith
    exact_mod_cast this
  refine ⟨⟨hH2, hgeoK, hgeoM⟩, ?_⟩
  refine jackson_core hW hfc hB0 hf hH16 hgeoK (fun m h1' h2' => ?_) (fun m h1' h2' => ?_)
  · have := hgeoM (m - 2 ^ r * m0) (by linarith) (by linarith [show (2 : ℤ) ^ r * (m0 + 1) = 2 ^ r * m0 + 2 ^ r by ring])
    rwa [show 2 ^ r * m0 + (m - 2 ^ r * m0) = m by ring] at this
  · have hx1 := hf _ (node_mem (k0 := k0) h1' h2'.le)
    have hx2 := hf _ (node_mem (k0 := k0) (r := r) (m0 := m0) (n := m + 1) (by omega) (by omega))
    have hΔ : |f (cL (k0 + r) (m + 1)) - f (cL (k0 + r) m)| ≤ 2 * B := by
      have := abs_sub (f (cL (k0 + r) (m + 1))) (f (cL (k0 + r) m)); linarith
    have ha : (2 : ℝ) ^ (k0 + r) * |f (cL (k0 + r) (m + 1)) - f (cL (k0 + r) m)| ≤ H / 2 := by
      calc (2 : ℝ) ^ (k0 + r) * |f (cL (k0 + r) (m + 1)) - f (cL (k0 + r) m)|
          ≤ 2 ^ (k0 + r) * (2 * B) := mul_le_mul_of_nonneg_left hΔ (by positivity)
        _ = 2 * (2 ^ k0 * (B * n)) := by rw [pow_add, hn]; ring
        _ ≤ 2 * (2 ^ k0 * X) := by
            have : B * n ≤ X := by rw [hX]; nlinarith
            gcongr
        _ ≤ H / 2 := by linarith
    have hb : (2 : ℝ) ^ (k0 + r) * (16 * (B + 1) / H) ≤ H / 2 := by
      rw [← mul_div_assoc, div_le_iff₀ hH0, pow_add]
      calc (2 : ℝ) ^ k0 * 2 ^ r * (16 * (B + 1)) = 16 * (2 ^ k0 * X) := by rw [hX, hn]; ring
        _ ≤ H := hHB
        _ ≤ H / 2 * H := by nlinarith
    rw [mul_add]; linarith

/-- **Lema IV.4.1**, versão uniforme, na forma existencial do texto: existe `A_{K,s} ≥ 1`. -/
theorem rational_jackson_uniform (k0 : ℕ) (m0 : ℤ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (s : ℝ) (f : ℝ → ℝ) (CW B : ℝ), 0 < s → s < 2 → IsWhitney CW → 1 ≤ B →
      ContinuousOn f (cellIcc k0 m0) → bnormInf k0 m0 s f ≤ ENNReal.ofReal B →
      ∀ r : ℕ, 1 ≤ r → ∀ H : ℕ, A * (B + 1) * ((2 : ℝ) ^ r) ^ max 1 s ≤ (H : ℝ) →
        (2 ≤ H ∧ k0 + r + 1 ≤ H ∧
          ∀ j : ℤ, 0 ≤ j → j < 2 ^ r → (2 ^ r * m0 + j).natAbs + 1 ≤ H) ∧
        ∃ T, AdmK k0 m0 (2 ^ r) H T ∧
          distK k0 m0 f (T.eval k0 m0) ≤
            ENNReal.ofReal (2 * CW) * omega2K k0 m0 f ((2 : ℝ) ^ (k0 + r))⁻¹ +
              ENNReal.ofReal (8 * (B + 1) / H) :=
  ⟨AK k0 m0, rational_jackson_uniform_explicit k0 m0⟩

end Pendencias.Jackson
