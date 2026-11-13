module
public import Unified.Consolidado.Sec4.ReLU
public import Unified.Consolidado.Lib.Calculus
@[expose] public section

/-!
# Section 7.4: joint error under leaf and height budgets

Definition 7.13, Proposition 7.14, the class `𝓕_{R,M}` (eq. (68)) and Lemma 7.15.
-/

open Set

namespace Dyadic.Lib

/-- **Definition 7.13**, eq. (65): `E^𝓛_{N,H}(f)_∞ = inf_{g ∈ 𝒜_{N,H}(K)} ‖f - g‖_{∞,K}`, with
`inf ∅ = +∞` (values in `[0, +∞]`). -/
noncomputable def jointError (K : Set ℝ) (N H : ℕ) (f : ℝ → ℝ) : ENNReal :=
  ⨅ g ∈ AsmNH K N H, supDist K f g

/-- **Definition 7.13**, eq. (66): `H^𝓛_{ε,N}(f) = min{H ≥ 2 : E^𝓛_{N,H}(f)_∞ ≤ ε}` (meaningful
when the set is nonempty). -/
noncomputable def minHeight (K : Set ℝ) (ε : ℝ) (N : ℕ) (f : ℝ → ℝ) : ℕ :=
  sInf {H : ℕ | 2 ≤ H ∧ jointError K N H f ≤ ENNReal.ofReal ε}

/-- Assemblies with at most `N` leaves (no height budget). -/
def AsmN (K : Set ℝ) (N : ℕ) : Set (ℝ → ℝ) :=
  {g | ContinuousOn g K ∧ ∃ Λ : Finset Atom, IsAssemblyRep K g Λ ∧ Λ.card ≤ N}

/-- `E^𝓛_N(f)_∞`: best uniform error with at most `N` leaves. -/
noncomputable def leafError (K : Set ℝ) (N : ℕ) (f : ℝ → ℝ) : ENNReal :=
  ⨅ g ∈ AsmN K N, supDist K f g

lemma AsmNH_mono {K : Set ℝ} {N N' H H' : ℕ} (hN : N ≤ N') (hH : H ≤ H') :
    AsmNH K N H ⊆ AsmNH K N' H' :=
  fun _ ⟨hc, Λ, hΛ, hcard, hht⟩ => ⟨hc, Λ, hΛ, hcard.trans hN, fun a ha => (hht a ha).trans hH⟩

lemma jointError_anti {K : Set ℝ} {N N' H H' : ℕ} (hN : N ≤ N') (hH : H ≤ H') (f : ℝ → ℝ) :
    jointError K N' H' f ≤ jointError K N H f :=
  biInf_mono (fun _ hg => AsmNH_mono hN hH hg)

lemma iUnion_AsmNH (K : Set ℝ) (N : ℕ) : (⋃ H, AsmNH K N H) = AsmN K N := by
  ext g
  simp only [mem_iUnion]
  constructor
  · rintro ⟨H, hc, Λ, hΛ, hcard, -⟩; exact ⟨hc, Λ, hΛ, hcard⟩
  · rintro ⟨hc, Λ, hΛ, hcard⟩
    exact ⟨Λ.sup Atom.height, hc, Λ, hΛ, hcard, fun a ha => Finset.le_sup (f := Atom.height) ha⟩

/-- **Proposition 7.14** (monotonicity of the two budgets): `E_{N+1,H} ≤ E_{N,H}`,
`E_{N,H+1} ≤ E_{N,H}`, and `E_{N,H}(f) ↓ E_N(f)` as `H → ∞`. -/
theorem jointError_monotone (K : Set ℝ) (f : ℝ → ℝ) (N H : ℕ) :
    jointError K (N + 1) H f ≤ jointError K N H f ∧
    jointError K N (H + 1) f ≤ jointError K N H f ∧
    Antitone (fun H => jointError K N H f) ∧
    Filter.Tendsto (fun H => jointError K N H f) Filter.atTop (nhds (leafError K N f)) := by
  have hanti : Antitone (fun H => jointError K N H f) :=
    fun H H' hH => jointError_anti le_rfl hH f
  refine ⟨jointError_anti (Nat.le_succ N) le_rfl f, jointError_anti le_rfl (Nat.le_succ H) f,
    hanti, ?_⟩
  have hinf : (⨅ H, jointError K N H f) = leafError K N f := by
    unfold jointError leafError
    rw [← iUnion_AsmNH, iInf_iUnion]
  rw [← hinf]
  exact tendsto_atTop_iInf hanti

/-- The class `𝓕_{R,M} = {f ∈ C²[0,1] : ‖f‖_∞ ≤ R, ‖f''‖_∞ ≤ M}` (eq. (68)). -/
def FRM (R M : ℝ) : Set (ℝ → ℝ) :=
  {f | ContDiffOn ℝ 2 f (Icc 0 1) ∧ (∀ x ∈ Icc (0 : ℝ) 1, |f x| ≤ R) ∧
    ∀ x ∈ Icc (0 : ℝ) 1, |iteratedDerivWithin 2 f (Icc 0 1) x| ≤ M}

/-- The constant `C₀ = 4R + M/2` (eq. (69)). -/
noncomputable def C0 (R M : ℝ) : ℝ := 4 * R + M / 2

lemma FRM.c2bound {R M : ℝ} {f : ℝ → ℝ} (hf : f ∈ FRM R M) {p q : ℝ} (hp : 0 ≤ p) (hq : q ≤ 1) :
    C2Bound f p q M :=
  C2Bound.of_contDiffOn zero_lt_one hf.1 hf.2.2 hp hq

/-- **Lemma 7.15** (uniform control of the first derivative): `‖f'‖_∞ ≤ C₀ = 4R + M/2`. -/
theorem FRM.deriv_bound {R M : ℝ} {f : ℝ → ℝ} (hf : f ∈ FRM R M) :
    ∀ x ∈ Icc (0 : ℝ) 1, |derivWithin f (Icc 0 1) x| ≤ C0 R M := by
  have hC2 := FRM.c2bound hf le_rfl le_rfl
  have hint : ∀ x ∈ Ioo (0 : ℝ) 1, |derivWithin f (Icc 0 1) x| ≤ C0 R M := by
    intro x hx
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]
    obtain ⟨a, ha, hax⟩ : ∃ a ∈ Icc (0 : ℝ) 1, 1 / 2 ≤ |a - x| ∧ |a - x| ≤ 1 := by
      rcases le_or_gt x (1 / 2) with h | h
      · exact ⟨1, right_mem_Icc.2 zero_le_one, by
          rw [abs_of_pos (by linarith [hx.2])]; constructor <;> linarith [hx.1]⟩
      · exact ⟨0, left_mem_Icc.2 zero_le_one, by
          rw [abs_of_neg (by linarith)]; constructor <;> linarith [hx.2]⟩
    have ht := taylor1_bound hC2 hx ha
    have hfa := hf.2.1 a ha
    have hfx := hf.2.1 x (Ioo_subset_Icc_self hx)
    have hpos : 0 < |a - x| := by linarith [hax.1]
    have h1 : |deriv f x| * |a - x| ≤ 2 * R + M / 2 * (a - x) ^ 2 := by
      rw [← abs_mul]
      have e : deriv f x * (a - x) = (f a - f x) - (f a - f x - deriv f x * (a - x)) := by ring
      rw [e]
      calc |(f a - f x) - (f a - f x - deriv f x * (a - x))|
          ≤ |f a - f x| + |f a - f x - deriv f x * (a - x)| := abs_sub _ _
        _ ≤ (|f a| + |f x|) + M / 2 * (a - x) ^ 2 := add_le_add (abs_sub _ _) ht
        _ ≤ 2 * R + M / 2 * (a - x) ^ 2 := by linarith
    have hsq : (a - x) ^ 2 = |a - x| * |a - x| := by rw [← sq_abs, sq]
    rw [hsq] at h1
    have hM : 0 ≤ M := (abs_nonneg _).trans (hf.2.2 x (Ioo_subset_Icc_self hx))
    have hR : 0 ≤ R := (abs_nonneg _).trans hfx
    unfold C0
    by_contra hcon
    push_neg at hcon
    have : (4 * R + M / 2) * |a - x| < |deriv f x| * |a - x| :=
      mul_lt_mul_of_pos_right hcon hpos
    have e1 : 2 * R ≤ 4 * R * |a - x| := by nlinarith [hax.1]
    have e2 : M / 2 * (|a - x| * |a - x|) ≤ M / 2 * |a - x| := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      nlinarith [hax.2]
    nlinarith
  have hcont : ContinuousOn (fun x => |derivWithin f (Icc 0 1) x|) (closure (Ioo (0 : ℝ) 1)) := by
    rw [closure_Ioo zero_ne_one]
    exact (hf.1.continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) (by norm_num)).abs
  intro x hx
  rw [← closure_Ioo (zero_ne_one' ℝ)] at hx
  exact le_on_closure hint hcont continuousOn_const hx

/-- Mean value consequence of Lemma 7.15: `|f(y) - f(x)| ≤ C₀ |y - x|` on `[0,1]`. -/
lemma FRM.lipschitz {R M : ℝ} {f : ℝ → ℝ} (hf : f ∈ FRM R M) {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) : |f y - f x| ≤ C0 R M * |y - x| := by
  have := Convex.norm_image_sub_le_of_norm_derivWithin_le (𝕜 := ℝ)
    (hf.1.differentiableOn (by norm_num)) (fun z hz => by
      rw [Real.norm_eq_abs]; exact FRM.deriv_bound hf z hz) (convex_Icc 0 1) hx hy
  simpa [Real.norm_eq_abs] using this

end Dyadic.Lib
