import Pendencias.Taxa

/-!
# IV.5.10 (desigualdade inversa universal), IV.5.7 (imersão inversa sob crescimento de
Lipschitz) e IV.5.8 (aplicação às agendas diretas)

Em `K = [0,1]` (`L = 1`):

* `omega2 f t = sup_{0<h≤t, x, x+2h ∈ K} |f(x+2h) - 2f(x+h) + f(x)|` (eq. second-modulus-direct),
  em `ENNReal`;
* `realN H N f = inf_{g ∈ Σ_N} (‖f-g‖_∞ + ω₂(g, 1/N))` (eq. self-roughness-certificate);
* classes de Besov pela norma diádica do texto (eq. dyadic-besov-norm):
  `BesovInf θ f :↔ ‖f‖_∞ + sup_r 2^{rθ} ω₂(f, 2^{-r}) < ∞` e
  `BesovQ θ p f :↔ ‖f‖_∞ + ‖(2^{rθ} ω₂(f, 2^{-r}))_r‖_{ℓ^p} < ∞`.
-/

namespace Pendencias.Agenda

open Set Artigo LTree Pendencias Finset

/-! ## Segundo módulo -/

/-- `ω₂(f,t)_{∞,[0,1]}` -/
noncomputable def omega2 (f : ℝ → ℝ) (t : ℝ) : ENNReal :=
  ⨆ h : ℝ, ⨆ (_ : 0 < h ∧ h ≤ t), ⨆ x : ℝ, ⨆ (_ : 0 ≤ x ∧ x + 2 * h ≤ 1),
    ENNReal.ofReal |f (x + 2 * h) - 2 * f (x + h) + f x|

lemma le_omega2 {f : ℝ → ℝ} {t h x : ℝ} (hh : 0 < h ∧ h ≤ t) (hx : 0 ≤ x ∧ x + 2 * h ≤ 1) :
    ENNReal.ofReal |f (x + 2 * h) - 2 * f (x + h) + f x| ≤ omega2 f t :=
  le_iSup₂_of_le h hh (le_iSup₂_of_le x hx le_rfl)

lemma le_distInf {f g : ℝ → ℝ} {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    ENNReal.ofReal |f y - g y| ≤ distInf f g :=
  le_iSup₂ (f := fun y (_ : y ∈ Icc (0 : ℝ) 1) => ENNReal.ofReal |f y - g y|) y hy

lemma abs_second_diff_le (A B C G : ℝ) : |A - 2 * B + C + G| ≤ |A| + 2 * |B| + |C| + |G| := by
  rw [abs_le]
  constructor <;> linarith [le_abs_self A, neg_abs_le A, le_abs_self B, neg_abs_le B,
    le_abs_self C, neg_abs_le C, le_abs_self G, neg_abs_le G]

/-- desigualdade triangular para segundas diferenças: `ω₂(f,t) ≤ 4‖f-g‖ + ω₂(g,t)` -/
theorem omega2_le (f g : ℝ → ℝ) (t : ℝ) : omega2 f t ≤ 4 * distInf f g + omega2 g t := by
  refine iSup_le fun h => iSup_le fun hh => iSup_le fun x => iSup_le fun hx => ?_
  have m0 : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1, by linarith [hh.1]⟩
  have m1 : x + h ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hh.1], by linarith [hh.1]⟩
  have m2 : x + 2 * h ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hh.1], hx.2⟩
  set A := f (x + 2 * h) - g (x + 2 * h)
  set B := f (x + h) - g (x + h)
  set C := f x - g x
  set G := g (x + 2 * h) - 2 * g (x + h) + g x
  have e : f (x + 2 * h) - 2 * f (x + h) + f x = A - 2 * B + C + G := by simp only [A, B, C, G]; ring
  calc ENNReal.ofReal |f (x + 2 * h) - 2 * f (x + h) + f x|
      ≤ ENNReal.ofReal (|A| + 2 * |B| + |C| + |G|) := by
        rw [e]; exact ENNReal.ofReal_le_ofReal (abs_second_diff_le A B C G)
    _ = ENNReal.ofReal |A| + 2 * ENNReal.ofReal |B| + ENNReal.ofReal |C| + ENNReal.ofReal |G| := by
        rw [ENNReal.ofReal_add (by positivity) (abs_nonneg _),
          ENNReal.ofReal_add (by positivity) (abs_nonneg _),
          ENNReal.ofReal_add (abs_nonneg _) (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_ofNat]
    _ ≤ distInf f g + 2 * distInf f g + distInf f g + omega2 g t := by
        gcongr
        · exact le_distInf m2
        · exact le_distInf m1
        · exact le_distInf m0
        · exact le_omega2 hh hx
    _ = 4 * distInf f g + omega2 g t := by ring

lemma omega2_zero (t : ℝ) : omega2 0 t = 0 := by
  simp [omega2]

lemma omega2_le_norm (f : ℝ → ℝ) (t : ℝ) : omega2 f t ≤ 4 * distInf f 0 := by
  simpa [omega2_zero] using omega2_le f 0 t

/-- `g` `L`-Lipschitz em `[0,1]` ⟹ `ω₂(g,t) ≤ 2Lt` -/
lemma omega2_lip {g : ℝ → ℝ} {L t : ℝ} (hL : 0 ≤ L)
    (hg : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, |g x - g y| ≤ L * |x - y|) :
    omega2 g t ≤ ENNReal.ofReal (2 * L * t) := by
  refine iSup_le fun h => iSup_le fun hh => iSup_le fun x => iSup_le fun hx => ?_
  have m0 : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1, by linarith [hh.1]⟩
  have m1 : x + h ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hh.1], by linarith [hh.1]⟩
  have m2 : x + 2 * h ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hh.1], hx.2⟩
  apply ENNReal.ofReal_le_ofReal
  have h1 := hg _ m2 _ m1
  have h2 := hg _ m1 _ m0
  rw [show x + 2 * h - (x + h) = h by ring, abs_of_pos hh.1] at h1
  rw [show x + h - x = h by ring, abs_of_pos hh.1] at h2
  calc |g (x + 2 * h) - 2 * g (x + h) + g x|
      = |(g (x + 2 * h) - g (x + h)) - (g (x + h) - g x)| := by ring_nf
    _ ≤ |g (x + 2 * h) - g (x + h)| + |g (x + h) - g x| := abs_sub _ _
    _ ≤ L * h + L * h := add_le_add h1 h2
    _ ≤ 2 * L * t := by nlinarith [hh.2]

lemma distInf_triangle (f g k : ℝ → ℝ) : distInf f k ≤ distInf f g + distInf g k := by
  refine iSup₂_le fun x hx => ?_
  calc ENNReal.ofReal |f x - k x| ≤ ENNReal.ofReal (|f x - g x| + |g x - k x|) :=
        ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)
    _ = ENNReal.ofReal |f x - g x| + ENNReal.ofReal |g x - k x| :=
        ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ distInf f g + distInf g k := add_le_add (le_distInf hx) (le_distInf hx)

/-! ## IV.5.10 -/

/-- funcional de realização `𝓡_N^{𝓛,H}(f)` -/
noncomputable def realN (H : ℕ → ℕ) (N : ℕ) (f : ℝ → ℝ) : ENNReal :=
  ⨅ g ∈ Sigma H N, (distInf f g + omega2 g (1 / N))

/-- **Lema IV.5.10 (desigualdade inversa universal)**: `¼ ω₂(f, 1/N) ≤ 𝓡_N(f)`,
escrito como `ω₂(f, 1/N) ≤ 4 𝓡_N(f)`; vale para toda agenda, toda `f` e todo `N`. -/
theorem universal_inverse (H : ℕ → ℕ) (N : ℕ) (f : ℝ → ℝ) :
    omega2 f (1 / N) ≤ 4 * realN H N f := by
  unfold realN
  rw [ENNReal.mul_iInf_of_ne (by norm_num) (by norm_num)]
  refine le_iInf fun g => ?_
  rw [ENNReal.mul_iInf_of_ne (by norm_num) (by norm_num)]
  refine le_iInf fun _ => ?_
  calc omega2 f (1 / N) ≤ 4 * distInf f g + omega2 g (1 / N) := omega2_le f g _
    _ ≤ 4 * distInf f g + 4 * omega2 g (1 / N) :=
        add_le_add le_rfl (le_mul_of_one_le_left (zero_le (omega2 g (1 / N))) (by norm_num))
    _ = 4 * (distInf f g + omega2 g (1 / N)) := (mul_add _ _ _).symm

/-! ## Besov diádico em `[0,1]` -/

/-- termo `2^{rθ} ω₂(f, 2^{-r})` -/
noncomputable def bterm (θ : ℝ) (f : ℝ → ℝ) (r : ℕ) : ENNReal :=
  ENNReal.ofReal (((2 : ℝ) ^ r) ^ θ) * omega2 f ((2 : ℝ) ^ r)⁻¹

/-- `f ∈ B^θ_{∞,∞}([0,1])` -/
def BesovInf (θ : ℝ) (f : ℝ → ℝ) : Prop :=
  distInf f 0 + ⨆ r : ℕ, bterm θ f r < ⊤

/-- `f ∈ B^θ_{∞,p}([0,1])`, `0 < p < ∞` -/
def BesovQ (θ p : ℝ) (f : ℝ → ℝ) : Prop :=
  distInf f 0 + (∑' r : ℕ, bterm θ f r ^ p) ^ (1 / p) < ⊤

lemma BesovInf.mono {θ θ' : ℝ} (hθ : θ ≤ θ') {f : ℝ → ℝ} (h : BesovInf θ' f) : BesovInf θ f := by
  unfold BesovInf at h ⊢
  refine lt_of_le_of_lt (add_le_add le_rfl (iSup_mono fun r => ?_)) h
  unfold bterm
  gcongr
  exact one_le_pow₀ (by norm_num)

/-! ## IV.5.7 -/

/-- `e_N^{𝒢}(f) = inf_{g ∈ 𝒢_N} ‖f-g‖_∞` -/
noncomputable def eG (G : ℕ → Set (ℝ → ℝ)) (N : ℕ) (f : ℝ → ℝ) : ENNReal :=
  ⨅ g ∈ G N, distInf f g

/-- hipótese de crescimento de Lipschitz `Lip(g) ≤ C_L N^γ` em `[0,1]` -/
def LipGrowth (G : ℕ → Set (ℝ → ℝ)) (CL γ : ℝ) : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∀ g ∈ G N, ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
    |g x - g y| ≤ CL * (N : ℝ) ^ γ * |x - y|

lemma omega2_le_eG {G : ℕ → Set (ℝ → ℝ)} {CL γ : ℝ} (hCL : 0 ≤ CL) (hG : LipGrowth G CL γ)
    {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ) (t : ℝ) :
    omega2 f t ≤ 4 * eG G N f + ENNReal.ofReal (2 * (CL * (N : ℝ) ^ γ) * t) := by
  have h : omega2 f t ≤ ⨅ g ∈ G N, (4 * distInf f g + ENNReal.ofReal (2 * (CL * (N : ℝ) ^ γ) * t)) :=
    le_iInf₂ fun g hg => (omega2_le f g t).trans
      (add_le_add le_rfl (omega2_lip (by positivity) (hG N hN g hg)))
  refine h.trans (le_of_eq ?_)
  unfold eG
  simp only [ENNReal.mul_iInf_of_ne (by norm_num : (4 : ENNReal) ≠ 0) (by norm_num), ENNReal.iInf_add]

/-- **Teorema IV.5.7 (imersão inversa sob crescimento de Lipschitz)**, estimativa do módulo:
com `θ* = α/(α+γ)` e `C = 4 + 2^{γ+1}` (só depende de `γ`), se `Lip(g) ≤ C_L N^γ` em `𝒢_N` e
`e_N^{𝒢}(f) ≤ A N^{-α}` para `N ≥ 1` (isto é, `A_α(f) ≤ A`), então
`ω₂(f,t) ≤ C (A + C_L) t^{θ*}` para `0 < t ≤ 1/2`. -/
theorem inverse_modulus {α γ : ℝ} (hα : 0 < α) (hγ : 0 ≤ γ) {G : ℕ → Set (ℝ → ℝ)} {CL A : ℝ}
    (hCL : 0 ≤ CL) (hA : 0 ≤ A) (hG : LipGrowth G CL γ) {f : ℝ → ℝ}
    (hf : ∀ N : ℕ, 1 ≤ N → eG G N f ≤ ENNReal.ofReal (A * (N : ℝ) ^ (-α)))
    {t : ℝ} (ht0 : 0 < t) (ht : t ≤ 1 / 2) :
    omega2 f t ≤ ENNReal.ofReal ((4 + 2 ^ (γ + 1)) * (A + CL) * t ^ (α / (α + γ))) := by
  have hαγ : 0 < α + γ := by linarith
  set θ := α / (α + γ)
  set u := t ^ (-(1 / (α + γ)))
  have hu1 : 1 ≤ u := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht0 (by linarith)
    (by have : 0 < 1 / (α + γ) := by positivity
        linarith)
  set N := ⌈u⌉₊
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (by
    intro h; have := Nat.ceil_eq_zero.mp h; linarith)
  have huN : u ≤ N := Nat.le_ceil u
  have hNu : (N : ℝ) ≤ 2 * u := by have := Nat.ceil_lt_add_one (by linarith : 0 ≤ u); linarith
  have hN0 : (0 : ℝ) < N := by positivity
  -- `N^{-α} ≤ t^θ`
  have hu_α : u ^ (-α) = t ^ θ := by
    simp only [u, θ]; rw [← Real.rpow_mul ht0.le]; congr 1; field_simp
  have b1 : (N : ℝ) ^ (-α) ≤ t ^ θ := by
    rw [← hu_α, Real.rpow_neg hN0.le, Real.rpow_neg (by linarith)]
    exact inv_anti₀ (by positivity) (Real.rpow_le_rpow (by linarith) huN hα.le)
  -- `N^γ t ≤ 2^γ t^θ`
  have hu_γ : u ^ γ * t = t ^ θ := by
    simp only [u, θ]
    rw [← Real.rpow_mul ht0.le, ← Real.rpow_add_one ht0.ne']
    congr 1; field_simp; ring
  have b2 : (N : ℝ) ^ γ * t ≤ 2 ^ γ * t ^ θ := by
    rw [← hu_γ, ← mul_assoc, ← Real.mul_rpow (by norm_num) (by linarith)]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hN0.le hNu hγ) ht0.le
  have htθ : 0 ≤ t ^ θ := by positivity
  have h2γ : (2 : ℝ) ^ (γ + 1) = 2 * 2 ^ γ := by rw [Real.rpow_add_one (by norm_num)]; ring
  calc omega2 f t ≤ 4 * eG G N f + ENNReal.ofReal (2 * (CL * (N : ℝ) ^ γ) * t) :=
        omega2_le_eG hCL hG hN1 f t
    _ ≤ 4 * ENNReal.ofReal (A * t ^ θ) + ENNReal.ofReal (2 * CL * (2 ^ γ * t ^ θ)) := by
        refine add_le_add (mul_le_mul_left' ((hf N hN1).trans
          (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left b1 hA))) 4)
          (ENNReal.ofReal_le_ofReal ?_)
        have := mul_le_mul_of_nonneg_left b2 (by positivity : (0 : ℝ) ≤ 2 * CL)
        linarith
    _ = ENNReal.ofReal (4 * A * t ^ θ + 2 ^ (γ + 1) * CL * t ^ θ) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), mul_assoc 4,
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_ofNat, h2γ]
        congr 2; ring
    _ ≤ ENNReal.ofReal ((4 + 2 ^ (γ + 1)) * (A + CL) * t ^ θ) := by
        apply ENNReal.ofReal_le_ofReal
        have : (0 : ℝ) ≤ 2 ^ (γ + 1) := by positivity
        nlinarith [mul_nonneg hA this, mul_nonneg hCL this, mul_nonneg (mul_nonneg hA this) htθ,
          mul_nonneg (mul_nonneg hCL this) htθ, mul_nonneg hA htθ, mul_nonneg hCL htθ]

/-- termos diádicos de ordem `r ≥ 1` sob a estimativa do módulo -/
lemma bterm_le_of_modulus {θ θs K : ℝ} {f : ℝ → ℝ}
    (hmod : ∀ t, 0 < t → t ≤ 1 / 2 → omega2 f t ≤ ENNReal.ofReal (K * t ^ θs)) {r : ℕ} (hr : 1 ≤ r) :
    bterm θ f r ≤ ENNReal.ofReal (K * ((2 : ℝ) ^ (θ - θs)) ^ r) := by
  have h2r : (0 : ℝ) < 2 ^ r := by positivity
  have ht : ((2 : ℝ) ^ r)⁻¹ ≤ 1 / 2 := by
    rw [one_div]; exact inv_anti₀ (by norm_num) (by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) hr)
  unfold bterm
  calc ENNReal.ofReal (((2 : ℝ) ^ r) ^ θ) * omega2 f ((2 : ℝ) ^ r)⁻¹
      ≤ ENNReal.ofReal (((2 : ℝ) ^ r) ^ θ) * ENNReal.ofReal (K * (((2 : ℝ) ^ r)⁻¹) ^ θs) :=
        mul_le_mul_left' (hmod _ (by positivity) ht) _
    _ = ENNReal.ofReal (((2 : ℝ) ^ r) ^ θ * (K * (((2 : ℝ) ^ r)⁻¹) ^ θs)) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ = ENNReal.ofReal (K * ((2 : ℝ) ^ (θ - θs)) ^ r) := by
        congr 1
        rw [Real.inv_rpow h2r.le, ← Real.rpow_natCast, ← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num),
          ← Real.rpow_neg (by norm_num)]
        rw [mul_left_comm, ← Real.rpow_add (by norm_num)]
        congr 2; ring

/-- `‖f‖_∞ < ∞` a partir de `e_1^{𝒢}(f) < ∞` e Lipschitz -/
lemma distInf_lt_top_of_eG {G : ℕ → Set (ℝ → ℝ)} {CL γ : ℝ} (hG : LipGrowth G CL γ) {f : ℝ → ℝ}
    (h : eG G 1 f < ⊤) : distInf f 0 < ⊤ := by
  unfold eG at h
  obtain ⟨g, h'⟩ := iInf_lt_iff.mp h
  obtain ⟨hg, hfg⟩ := iInf_lt_iff.mp h'
  refine lt_of_le_of_lt (distInf_triangle f g 0) (ENNReal.add_lt_top.mpr ⟨hfg, ?_⟩)
  refine lt_of_le_of_lt (iSup₂_le fun x hx => ?_ : distInf g 0 ≤ ENNReal.ofReal (|g 0| + |CL|))
    ENNReal.ofReal_lt_top
  apply ENNReal.ofReal_le_ofReal
  have := hG 1 le_rfl g hg x hx 0 ⟨le_rfl, zero_le_one⟩
  simp only [Nat.cast_one, Real.one_rpow, mul_one, sub_zero, Pi.zero_apply] at this ⊢
  have h1 : |x| ≤ 1 := by rw [abs_of_nonneg hx.1]; exact hx.2
  have h2 : CL * |x| ≤ |CL| :=
    (mul_le_mul_of_nonneg_right (le_abs_self CL) (abs_nonneg x)).trans
      (mul_le_of_le_one_right (abs_nonneg _) h1)
  have h3 := abs_sub_abs_le_abs_sub (g x) (g 0)
  linarith

/-- **Teorema IV.5.7**, consequência de Besov: `f ∈ B^{θ*}_{∞,∞}([0,1])` e
`f ∈ B^θ_{∞,p}([0,1])` para `0 < θ < θ*`, `0 < p < ∞`. -/
theorem inverse_besov {α γ : ℝ} (hα : 0 < α) (hγ : 0 ≤ γ) {G : ℕ → Set (ℝ → ℝ)} {CL A : ℝ}
    (hCL : 0 ≤ CL) (hA : 0 ≤ A) (hG : LipGrowth G CL γ) {f : ℝ → ℝ}
    (hf : ∀ N : ℕ, 1 ≤ N → eG G N f ≤ ENNReal.ofReal (A * (N : ℝ) ^ (-α))) :
    BesovInf (α / (α + γ)) f ∧
    ∀ θ p : ℝ, θ < α / (α + γ) → 0 < p → BesovQ θ p f := by
  set θs := α / (α + γ)
  set K := (4 + 2 ^ (γ + 1)) * (A + CL)
  have hK : 0 ≤ K := by positivity
  have hmod : ∀ t, 0 < t → t ≤ 1 / 2 → omega2 f t ≤ ENNReal.ofReal (K * t ^ θs) :=
    fun t ht0 ht => inverse_modulus hα hγ hCL hA hG hf ht0 ht
  have hnorm : distInf f 0 < ⊤ := distInf_lt_top_of_eG hG
    (lt_of_le_of_lt (hf 1 le_rfl) ENNReal.ofReal_lt_top)
  set F := (distInf f 0).toReal
  have hF : distInf f 0 = ENNReal.ofReal F := (ENNReal.ofReal_toReal hnorm.ne).symm
  have hF0 : 0 ≤ F := ENNReal.toReal_nonneg
  have hb0 : ∀ θ, bterm θ f 0 ≤ ENNReal.ofReal (4 * F) := by
    intro θ
    simp only [bterm, pow_zero, Real.one_rpow, ENNReal.ofReal_one, one_mul, inv_one]
    calc omega2 f 1 ≤ 4 * distInf f 0 := omega2_le_norm f 1
      _ = ENNReal.ofReal (4 * F) := by
          rw [hF, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  constructor
  · -- endpoint
    refine ENNReal.add_lt_top.mpr ⟨hnorm, lt_of_le_of_lt (iSup_le fun r => ?_ :
      ⨆ r, bterm θs f r ≤ ENNReal.ofReal (4 * F + K)) ENNReal.ofReal_lt_top⟩
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · exact (hb0 θs).trans (ENNReal.ofReal_le_ofReal (by linarith))
    · refine (bterm_le_of_modulus hmod hr).trans (ENNReal.ofReal_le_ofReal ?_)
      simp only [sub_self, Real.rpow_zero, one_pow, mul_one]; linarith
  · -- ordens menores
    intro θ p hθ hp
    set ρ := (2 : ℝ) ^ (θ - θs)
    have hρ0 : 0 < ρ := by positivity
    have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    set B := 4 * F + K
    have hterm : ∀ r, bterm θ f r ≤ ENNReal.ofReal B * ENNReal.ofReal ρ ^ r := by
      intro r
      rw [← ENNReal.ofReal_pow hρ0.le, ← ENNReal.ofReal_mul (by positivity)]
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · simp only [pow_zero, mul_one]; exact (hb0 θ).trans (ENNReal.ofReal_le_ofReal (by linarith))
      · refine (bterm_le_of_modulus hmod hr).trans (ENNReal.ofReal_le_ofReal ?_)
        have : 0 ≤ ρ ^ r := by positivity
        nlinarith
    have hρp : ENNReal.ofReal ρ ^ p < 1 :=
      ENNReal.rpow_lt_one (by simpa using hρ1) hp
    have hsum : ∑' r : ℕ, bterm θ f r ^ p ≤ ENNReal.ofReal B ^ p * (1 - ENNReal.ofReal ρ ^ p)⁻¹ := by
      calc ∑' r : ℕ, bterm θ f r ^ p
          ≤ ∑' r : ℕ, ENNReal.ofReal B ^ p * (ENNReal.ofReal ρ ^ p) ^ r := by
            refine ENNReal.tsum_le_tsum fun r => ?_
            calc bterm θ f r ^ p ≤ (ENNReal.ofReal B * ENNReal.ofReal ρ ^ r) ^ p :=
                  ENNReal.rpow_le_rpow (hterm r) hp.le
              _ = ENNReal.ofReal B ^ p * (ENNReal.ofReal ρ ^ p) ^ r := by
                  rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le, ← ENNReal.rpow_natCast,
                    ← ENNReal.rpow_mul, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, mul_comm (r : ℝ) p]
        _ = _ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    have hfin : ENNReal.ofReal B ^ p * (1 - ENNReal.ofReal ρ ^ p)⁻¹ < ⊤ :=
      ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hp.le ENNReal.ofReal_ne_top)
        (ENNReal.inv_lt_top.mpr (tsub_pos_of_lt hρp))
    exact ENNReal.add_lt_top.mpr ⟨hnorm, ENNReal.rpow_lt_top_of_nonneg (by positivity)
      (lt_of_le_of_lt hsum hfin).ne⟩

/-! ## IV.5.8 -/

lemma abs_le_ht (s : ℚ) : |(s : ℝ)| ≤ ht s := by
  have hd : (1 : ℝ) ≤ s.den := by exact_mod_cast s.den_pos
  rw [Rat.cast_def, abs_div, Nat.abs_cast]
  calc |(s.num : ℝ)| / s.den ≤ |(s.num : ℝ)| := div_le_self (abs_nonneg _) hd
    _ = (s.num.natAbs : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs]
    _ ≤ ht s := by exact_mod_cast le_max_left _ _

/-- uma montagem com alturas `≤ L` é `L`-Lipschitz na sua célula -/
lemma eval_lipschitz {L : ℕ} : ∀ {k : ℕ} {m : ℤ} {T : LTree}, WF k m T →
    (∀ a ∈ T.leaves, a.height ≤ L) → ∀ x ∈ cellIcc k m, ∀ y ∈ cellIcc k m,
      |T.eval k m x - T.eval k m y| ≤ L * |x - y| := by
  intro k m T
  induction T generalizing k m with
  | leaf a =>
      intro _ hL x _ y _
      have ha := hL a (by simp [leaves])
      simp only [eval, Atom.eval]
      rw [show (a.y0 : ℝ) + a.s * (x - a.x0) - (a.y0 + a.s * (y - a.x0)) = a.s * (x - y) by ring,
        abs_mul]
      have h1 : |(a.s : ℝ)| ≤ L := (abs_le_ht a.s).trans (by
        have : ht a.s ≤ a.height := by unfold Atom.height; omega
        exact_mod_cast this.trans ha)
      exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  | node l r ihl ihr =>
      intro h hL x hx y hy
      have hLl : ∀ a ∈ l.leaves, a.height ≤ L := fun a ha => hL a (by simp [leaves, ha])
      have hLr : ∀ a ∈ r.leaves, a.height ≤ L := fun a ha => hL a (by simp [leaves, ha])
      set c := cL (k + 1) (2 * m + 1)
      have hcl : cellIcc (k + 1) (2 * m) = Icc (cL k m) c := by
        rw [cellIcc_eq, cL_child_left, cR_child_left]
      have hcr : cellIcc (k + 1) (2 * m + 1) = Icc c (cR k m) := by
        rw [cellIcc_eq, cR_child_right]
      rw [cellIcc_eq] at hx hy
      have hc : cL k m ≤ c ∧ c ≤ cR k m := by
        have := cL_lt_cR (k + 1) (2 * m); have := cL_lt_cR (k + 1) (2 * m + 1)
        rw [cL_child_left, cR_child_left] at *; rw [cR_child_right] at *; constructor <;> linarith
      have hmidL : l.eval (k + 1) (2 * m) c = r.eval (k + 1) (2 * m + 1) c := by
        have e1 := eval_at_right h.1; rw [cR_child_left] at e1
        rw [e1, eval_at_left h.2.1, h.2.2]
      -- valor da montagem como função das duas metades
      have hev : ∀ z, (node l r).eval k m z =
          if z < c then l.eval (k + 1) (2 * m) z else r.eval (k + 1) (2 * m + 1) z := fun z => rfl
      have key : ∀ x y, x ∈ Icc (cL k m) (cR k m) → y ∈ Icc (cL k m) (cR k m) → x ≤ y →
          |(node l r).eval k m x - (node l r).eval k m y| ≤ L * |x - y| := by
        intro x y hx hy hxy
        rw [hev, hev]
        by_cases hxc : x < c <;> by_cases hyc : y < c
        · rw [if_pos hxc, if_pos hyc]
          exact ihl h.1 hLl x (hcl ▸ ⟨hx.1, hxc.le⟩) y (hcl ▸ ⟨hy.1, hyc.le⟩)
        · rw [if_pos hxc, if_neg hyc]
          have h1 := ihl h.1 hLl x (hcl ▸ ⟨hx.1, hxc.le⟩) c (hcl ▸ ⟨hc.1, le_rfl⟩)
          have h2 := ihr h.2.1 hLr c (hcr ▸ ⟨le_rfl, hc.2⟩) y (hcr ▸ ⟨not_lt.mp hyc, hy.2⟩)
          rw [hmidL] at h1
          rw [abs_of_nonpos (by linarith : x - y ≤ 0)]
          rw [abs_of_nonpos (by linarith : x - c ≤ 0)] at h1
          rw [abs_of_nonpos (by linarith [not_lt.mp hyc] : c - y ≤ 0)] at h2
          calc _ ≤ |l.eval (k + 1) (2 * m) x - r.eval (k + 1) (2 * m + 1) c| +
                  |r.eval (k + 1) (2 * m + 1) c - r.eval (k + 1) (2 * m + 1) y| := abs_sub_le _ _ _
            _ ≤ L * -(x - c) + L * -(c - y) := add_le_add h1 h2
            _ = L * -(x - y) := by ring
        · exact absurd (lt_of_le_of_lt hxy hyc) hxc
        · rw [if_neg hxc, if_neg hyc]
          exact ihr h.2.1 hLr x (hcr ▸ ⟨not_lt.mp hxc, hx.2⟩) y (hcr ▸ ⟨not_lt.mp hyc, hy.2⟩)
      rcases le_total x y with hxy | hxy
      · exact key x y hx hy hxy
      · rw [abs_sub_comm, abs_sub_comm x]; exact key y x hy hx hxy

/-- todo `g ∈ Σ_N^{𝓛,H}` é `H(N)`-Lipschitz em `[0,1]` -/
lemma Sigma_lipschitz {H : ℕ → ℕ} {N : ℕ} {g : ℝ → ℝ} (hg : g ∈ Sigma H N) :
    ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, |g x - g y| ≤ (H N : ℝ) * |x - y| := by
  have h01 : cellIcc 0 0 = Icc (0 : ℝ) 1 := by simp [cellIcc]
  rcases hg with rfl | ⟨T, ⟨hw, -, hh⟩, rfl⟩
  · intro x _ y _; simp; positivity
  · intro x hx y hy
    exact eval_lipschitz hw (maxHeight_le_iff.mp hh) x (h01 ▸ hx) y (h01 ▸ hy)

/-- de `𝔞_{α,∞}(f) < ∞` para `e_N(f) ≤ A N^{-α}` -/
lemma pErr_le_of_rateInf {α : ℝ} {H : ℕ → ℕ} {f : ℝ → ℝ} (h : rateInf α H f < ⊤) {N : ℕ}
    (hN : 1 ≤ N) : pErr H N f ≤ ENNReal.ofReal ((rateInf α H f).toReal * (N : ℝ) ^ (-α)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : ENNReal.ofReal ((N : ℝ) ^ α) * pErr H N f ≤ rateInf α H f :=
    le_iSup₂ (f := fun (N : ℕ) (_ : 1 ≤ N) => ENNReal.ofReal ((N : ℝ) ^ α) * pErr H N f) N hN
  have hinv : ENNReal.ofReal ((N : ℝ) ^ (-α)) * ENNReal.ofReal ((N : ℝ) ^ α) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add hN0, neg_add_cancel, Real.rpow_zero,
      ENNReal.ofReal_one]
  calc pErr H N f = ENNReal.ofReal ((N : ℝ) ^ (-α)) * (ENNReal.ofReal ((N : ℝ) ^ α) * pErr H N f) := by
        rw [← mul_assoc, hinv, one_mul]
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-α)) * rateInf α H f := mul_le_mul_left' h1 _
    _ = _ := by
        rw [← ENNReal.ofReal_toReal h.ne, ← ENNReal.ofReal_mul (by positivity), mul_comm,
          ENNReal.toReal_ofReal ENNReal.toReal_nonneg]

/-- **Corolário IV.5.8**, `q = ∞`: se `H(N) ≤ C N^γ`, então
`𝒜_∞^α(𝓛,H) ⊂ B^{α/(α+γ)}_{∞,∞}([0,1])`. -/
theorem raw_library_inverse_inf {α γ C : ℝ} (hα : 0 < α) (hγ : 0 ≤ γ) (hC : 0 ≤ C) {H : ℕ → ℕ}
    (hHC : ∀ N : ℕ, 1 ≤ N → (H N : ℝ) ≤ C * (N : ℝ) ^ γ) {f : ℝ → ℝ}
    (hf : rateInf α H f < ⊤) : BesovInf (α / (α + γ)) f := by
  have hG : LipGrowth (Sigma H) C γ := fun N hN g hg x hx y hy =>
    (Sigma_lipschitz hg x hx y hy).trans
      (mul_le_mul_of_nonneg_right (hHC N hN) (abs_nonneg _))
  refine (inverse_besov (A := (rateInf α H f).toReal) hα hγ hC ENNReal.toReal_nonneg hG
    (fun N hN => ?_)).1
  exact pErr_le_of_rateInf hf hN

/-- **Corolário IV.5.8**, `0 < q < ∞` (via a redução diádica IV.3.2). -/
theorem raw_library_inverse {α γ C q : ℝ} (hα : 0 < α) (hγ : 0 ≤ γ) (hC : 0 ≤ C) (hq : 0 < q)
    {H : ℕ → ℕ} (hH : Monotone H) (hHC : ∀ N : ℕ, 1 ≤ N → (H N : ℝ) ≤ C * (N : ℝ) ^ γ)
    {f : ℝ → ℝ} (hf : rateQ α q H f < ⊤) : BesovInf (α / (α + γ)) f := by
  apply raw_library_inverse_inf hα hγ hC hHC
  obtain ⟨-, h2⟩ := dyadic_reduction hα hq hH f
  have hD : dyadQ α q H f < ⊤ := lt_of_le_of_lt h2 (ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by positivity) (by
      exact ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top (by norm_num)
        (ENNReal.rpow_ne_top_of_nonneg hq.le ENNReal.ofReal_ne_top)⟩)) hf)
  have hT : ∑' r, dterm α q H f r < ⊤ := by
    have := ENNReal.rpow_lt_top_of_nonneg hq.le hD.ne
    rwa [dyadQ, ← ENNReal.rpow_mul, one_div_mul_cancel hq.ne', ENNReal.rpow_one] at this
  have hInf : dyadInf α H f < ⊤ := by
    refine lt_of_le_of_lt (iSup_le fun r => ?_) (ENNReal.rpow_lt_top_of_nonneg
      (by positivity : (0 : ℝ) ≤ 1 / q) hT.ne)
    calc ENNReal.ofReal (((2 : ℝ) ^ r) ^ α) * pErr H (2 ^ r) f
        = (dterm α q H f r) ^ (1 / q) := by
          rw [dterm, ← ENNReal.rpow_mul, mul_one_div_cancel hq.ne', ENNReal.rpow_one]
      _ ≤ (∑' r, dterm α q H f r) ^ (1 / q) :=
          ENNReal.rpow_le_rpow (ENNReal.le_tsum r) (by positivity)
  exact lt_of_le_of_lt (dyadic_reduction_inf hα hH f).2
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hInf)

/-- agenda `H_{s,κ}(N) = ⌈C_K (N+1)^{ν_s} [log(eN)]^κ⌉` em `K = [0,1]` (`C_K = 8`,
`ν_s = max{1,s}`) -/
noncomputable def Hsk (s κ : ℝ) (N : ℕ) : ℕ :=
  ⌈8 * ((N : ℝ) + 1) ^ max 1 s * Real.log (Real.exp 1 * N) ^ κ⌉₊

lemma log_eN_ge_one {N : ℕ} (hN : 1 ≤ N) : 1 ≤ Real.log (Real.exp 1 * N) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
  linarith [Real.log_nonneg hN']

/-- `H_{s,κ}(N) ≤ C' N^{ν_s + εκ}` -/
lemma Hsk_le {s κ ε : ℝ} (hκ : 0 ≤ κ) (hε : 0 < ε) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ N : ℕ, 1 ≤ N → (Hsk s κ N : ℝ) ≤ C' * (N : ℝ) ^ (max 1 s + ε * κ) := by
  set ν := max 1 s
  have hν : 1 ≤ ν := le_max_left _ _
  refine ⟨2 * (8 * 2 ^ ν * (1 + 1 / ε) ^ κ), by positivity, fun N hN => ?_⟩
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog := log_eN_ge_one hN
  -- `log(eN) ≤ (1 + 1/ε) N^ε`
  have hl : Real.log (Real.exp 1 * N) ≤ (1 + 1 / ε) * (N : ℝ) ^ ε := by
    rw [Real.log_mul (Real.exp_pos 1).ne' hN0.ne', Real.log_exp]
    have h1 := Real.log_le_rpow_div hN0.le hε
    have h2 : 1 ≤ (N : ℝ) ^ ε := Real.one_le_rpow hN' hε.le
    calc 1 + Real.log N ≤ (N : ℝ) ^ ε + (N : ℝ) ^ ε / ε := by linarith
      _ = (1 + 1 / ε) * (N : ℝ) ^ ε := by ring
  set X := 8 * ((N : ℝ) + 1) ^ ν * Real.log (Real.exp 1 * N) ^ κ
  have hX1 : 1 ≤ X := by
    have : 1 ≤ ((N : ℝ) + 1) ^ ν := Real.one_le_rpow (by linarith) (by linarith)
    have : 1 ≤ Real.log (Real.exp 1 * N) ^ κ := Real.one_le_rpow hlog hκ
    nlinarith
  have hXle : X ≤ 8 * 2 ^ ν * (1 + 1 / ε) ^ κ * (N : ℝ) ^ (ν + ε * κ) := by
    have e1 : ((N : ℝ) + 1) ^ ν ≤ 2 ^ ν * (N : ℝ) ^ ν := by
      rw [← Real.mul_rpow (by norm_num) hN0.le]
      exact Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
    have e2 : Real.log (Real.exp 1 * N) ^ κ ≤ (1 + 1 / ε) ^ κ * (N : ℝ) ^ (ε * κ) := by
      rw [Real.rpow_mul hN0.le, ← Real.mul_rpow (by positivity) (by positivity)]
      exact Real.rpow_le_rpow (by linarith) hl hκ
    rw [Real.rpow_add hN0]
    calc X ≤ 8 * (2 ^ ν * (N : ℝ) ^ ν) * ((1 + 1 / ε) ^ κ * (N : ℝ) ^ (ε * κ)) := by
          simp only [X]; gcongr
      _ = _ := by ring
  calc (Hsk s κ N : ℝ) ≤ X + 1 := (Nat.ceil_lt_add_one (by linarith)).le
    _ ≤ 2 * X := by linarith
    _ ≤ _ := by rw [mul_assoc 2]; exact mul_le_mul_of_nonneg_left hXle (by norm_num)

lemma Hsk_mono {s κ : ℝ} (hκ : 0 ≤ κ) : Monotone (Hsk s κ) := by
  intro N M hNM
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rcases Nat.eq_zero_or_pos M with rfl | hM
    · exact le_rfl
    have h0 : Hsk s κ 0 ≤ 8 := by
      unfold Hsk
      apply Nat.ceil_le.mpr
      simp only [Nat.cast_zero, zero_add, Real.one_rpow, mul_one, mul_zero, Real.log_zero]
      have := Real.zero_rpow_le_one κ
      push_cast; linarith
    have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have h8 : 8 ≤ Hsk s κ M := by
      have hX : (8 : ℝ) ≤ 8 * ((M : ℝ) + 1) ^ max 1 s * Real.log (Real.exp 1 * M) ^ κ := by
        have : 1 ≤ ((M : ℝ) + 1) ^ max 1 s := Real.one_le_rpow (by linarith) (by positivity)
        have : 1 ≤ Real.log (Real.exp 1 * M) ^ κ := Real.one_le_rpow (log_eN_ge_one hM) hκ
        nlinarith
      have := hX.trans (Nat.le_ceil _)
      unfold Hsk; exact_mod_cast this
    exact h0.trans h8
  apply Nat.ceil_mono
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNM' : (N : ℝ) ≤ M := by exact_mod_cast hNM
  have hl := log_eN_ge_one hN
  gcongr

/-- `ϑ_s = s/(s + ν_s)`, que vale `s/(s+1)` para `0 < s < 1` e `1/2` para `1 ≤ s` -/
lemma vartheta_eq {s : ℝ} (hs : 0 < s) :
    s / (s + max 1 s) = if s < 1 then s / (s + 1) else 1 / 2 := by
  split_ifs with h
  · rw [max_eq_left h.le]
  · rw [max_eq_right (not_lt.mp h)]; field_simp; ring

/-- **Corolário IV.5.8**, agendas `H_{s,κ}`: para `0 < q ≤ ∞`, `𝒜_q^s(𝓛, H_{s,0}) ⊂
B^{ϑ_s}_{∞,∞}`; com fator logarítmico (`κ ≥ 0` qualquer), `𝒜_q^s(𝓛, H_{s,κ}) ⊂ B^θ_{∞,∞}`
para todo `θ < ϑ_s`. Enunciado aqui com `q < ∞` (`rateQ`); o caso `q = ∞` é análogo via
`raw_library_inverse_inf`. -/
theorem schedule_raw_inverse {s q : ℝ} (hs : 0 < s) (hq : 0 < q) {f : ℝ → ℝ} :
    (rateQ s q (Hsk s 0) f < ⊤ → BesovInf (s / (s + max 1 s)) f) ∧
    (∀ κ θ : ℝ, 0 ≤ κ → θ < s / (s + max 1 s) → rateQ s q (Hsk s κ) f < ⊤ → BesovInf θ f) := by
  have hν : 1 ≤ max 1 s := le_max_left _ _
  constructor
  · intro hf
    have hle : ∀ N : ℕ, 1 ≤ N → (Hsk s 0 N : ℝ) ≤ (2 * (8 * 2 ^ max 1 s)) * (N : ℝ) ^ max 1 s := by
      intro N hN
      have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have : (Hsk s 0 N : ℝ) ≤ 8 * ((N : ℝ) + 1) ^ max 1 s + 1 := by
        have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 8 * ((N : ℝ) + 1) ^ max 1 s *
          Real.log (Real.exp 1 * N) ^ (0 : ℝ) by positivity)
        simp only [Real.rpow_zero, mul_one] at this; unfold Hsk; simp only [Real.rpow_zero, mul_one]
        linarith
      have e1 : ((N : ℝ) + 1) ^ max 1 s ≤ 2 ^ max 1 s * (N : ℝ) ^ max 1 s := by
        rw [← Real.mul_rpow (by norm_num) (by linarith)]
        exact Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
      have e2 : 1 ≤ (N : ℝ) ^ max 1 s := Real.one_le_rpow hN' (by linarith)
      have e3 : (1 : ℝ) ≤ 2 ^ max 1 s := Real.one_le_rpow (by norm_num) (by linarith)
      nlinarith
    exact raw_library_inverse hs (by linarith) (by positivity) hq (Hsk_mono le_rfl) hle hf
  · intro κ θ hκ hθ hf
    by_cases hθ0 : θ ≤ 0
    · -- ordens não positivas: basta `‖f‖_∞ < ∞` e termos limitados; usa-se a ordem `ϑ` com `κ`
      -- aproximado por `η = 1`
      obtain ⟨C', hC', hle⟩ := Hsk_le (s := s) hκ (ε := 1) one_pos
      have := raw_library_inverse hs (by positivity) hC' hq (Hsk_mono hκ) hle hf
      exact this.mono (le_trans hθ0 (by positivity))
    push_neg at hθ0
    -- escolha de `η` com `θ < s/(s+ν+η)`
    set ν := max 1 s
    set η := (s / θ - s - ν) / 2
    have hθ' : s + ν < s / θ := by
      rw [lt_div_iff₀ hθ0]; rw [lt_div_iff₀ (by positivity)] at hθ; linarith
    have hη : 0 < η := by simp only [η]; linarith
    set ε := η / (κ + 1)
    have hε : 0 < ε := by positivity
    have hεκ : ε * κ ≤ η := by
      simp only [ε]; rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
    obtain ⟨C', hC', hle⟩ := Hsk_le (s := s) hκ hε
    have hB := raw_library_inverse hs (by positivity) hC' hq (Hsk_mono hκ) hle hf
    refine hB.mono ?_
    rw [le_div_iff₀ (by positivity)]
    have : θ * (s + ν + η) ≤ s := by
      have h1 : s + ν + η < s / θ := by simp only [η]; linarith
      rw [lt_div_iff₀ hθ0] at h1; linarith
    nlinarith

end Pendencias.Agenda
