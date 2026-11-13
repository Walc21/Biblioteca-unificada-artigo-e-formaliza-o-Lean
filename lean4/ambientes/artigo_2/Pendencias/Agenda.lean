import RequestProject.JointBudget
import RequestProject.Catalog

/-!
# IV.3.1 (aninhamento da agenda) e IV.4.6 (piso aritmético uniforme)

Definições do Artigo 3, §3.1, sobre `K = [0,1] = J_{0,0}` (o mesmo domínio de
`Artigo.jointErr`):

* `Sigma H N = {0} ∪ 𝒜_{N,H(N)}(K)` — eq. (pointed-error);
* `pErr H N f = inf_{g ∈ Sigma H N} ‖f - g‖_{∞,K}` (em `ENNReal`, como `jointErr`);
* `QH H = {r ∈ ℚ : ht r ≤ H}` — o conjunto `𝒬_H`.
-/

namespace Pendencias.Agenda

open Set Artigo LTree

/-- `‖f - g‖_{∞,[0,1]}` em `ENNReal` -/
noncomputable def distInf (f g : ℝ → ℝ) : ENNReal :=
  ⨆ x ∈ Icc (0 : ℝ) 1, ENNReal.ofReal |f x - g x|

/-- `Σ_N^{𝓛,H}(K) = {0} ∪ 𝒜_{N,H(N)}(K)` -/
def Sigma (H : ℕ → ℕ) (N : ℕ) : Set (ℝ → ℝ) :=
  {g | g = 0 ∨ ∃ T, AdmNH N (H N) T ∧ g = T.eval 0 0}

/-- erro apontado `e_N^{𝓛,H}(f)` -/
noncomputable def pErr (H : ℕ → ℕ) (N : ℕ) (f : ℝ → ℝ) : ENNReal :=
  ⨅ g ∈ Sigma H N, distInf f g

/-- `𝒬_H = {p/q ∈ ℚ : ht(p/q) ≤ H}` -/
def QH (H : ℕ) : Set ℚ := {r | ht r ≤ H}

lemma depth_lt_numLeaves' : ∀ T : LTree, T.depth < T.numLeaves
  | .leaf _ => by simp [LTree.depth, LTree.numLeaves, LTree.leaves]
  | .node l r => by
      have := depth_lt_numLeaves' l
      have := depth_lt_numLeaves' r
      simp only [LTree.depth]
      rw [LTree.numLeaves_node]
      omega

/-- eq. (pointed-inherited): `e_N = min{‖f‖_∞, E_{N,H(N)}(f)_∞}` -/
theorem pErr_eq_min (H : ℕ → ℕ) (N : ℕ) (f : ℝ → ℝ) :
    pErr H N f = min (distInf f 0) (jointErr N (H N) f) := by
  unfold pErr
  apply le_antisymm
  · refine le_min (iInf₂_le (0 : ℝ → ℝ) (Or.inl rfl)) ?_
    unfold jointErr
    exact le_iInf₂ fun T hT => iInf₂_le (T.eval 0 0) (Or.inr ⟨T, hT, rfl⟩)
  · refine le_iInf₂ fun g hg => ?_
    rcases hg with rfl | ⟨T, hT, rfl⟩
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (jointErr_le hT)

lemma Sigma_finite (H : ℕ → ℕ) (N : ℕ) : (Sigma H N).Finite := by
  apply ((Set.finite_singleton (0 : ℝ → ℝ)).union
    ((RepCat (H N) N 0 0).finite_toSet.image (fun T => T.eval 0 0))).subset
  rintro g (rfl | ⟨T, hT, rfl⟩)
  · exact Or.inl (Set.mem_singleton _)
  · refine Or.inr ⟨T, Finset.mem_coe.mpr (mem_RepCat.mpr ⟨hT.1, ?_, hT.2.2⟩), rfl⟩
    have := depth_lt_numLeaves' T
    have := hT.2.1
    omega

/-- **Proposição IV.3.1 (aninhamento da agenda).** -/
theorem schedule_nesting {H : ℕ → ℕ} (hH : Monotone H) (N : ℕ) (f : ℝ → ℝ) :
    Sigma H N ⊆ Sigma H (N + 1) ∧
    pErr H (N + 1) f ≤ pErr H N f ∧
    pErr H N f ≤ distInf f 0 ∧
    ∃ g ∈ Sigma H N, pErr H N f = distInf f g := by
  have hsub : Sigma H N ⊆ Sigma H (N + 1) := by
    rintro g (rfl | ⟨T, ⟨hw, hn, hh⟩, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨T, ⟨hw, by omega, hh.trans (hH (Nat.le_succ N))⟩, rfl⟩
  unfold pErr
  refine ⟨hsub, biInf_mono fun g hg => hsub hg, iInf₂_le (0 : ℝ → ℝ) (Or.inl rfl), ?_⟩
  obtain ⟨g, hg, hmin⟩ := Set.exists_min_image (Sigma H N) (distInf f) (Sigma_finite H N)
    ⟨0, Or.inl rfl⟩
  exact ⟨g, hg, le_antisymm (iInf₂_le g hg) (le_iInf₂ fun g' hg' => hmin g' hg')⟩

/-! ## IV.4.6 -/

/-- todo racional positivo de altura `≤ H` é `≥ 1/H` -/
lemma inv_le_of_ht {r : ℚ} {H : ℕ} (hr : 0 < r) (hH : ht r ≤ H) : (1 : ℝ) / H ≤ r := by
  have hnum : 0 < r.num := Rat.num_pos.mpr hr
  have hden : r.den ≤ H := le_trans (le_max_right _ _) hH
  have hd0 : 0 < r.den := r.den_pos
  have hH0 : (0 : ℝ) < H := by exact_mod_cast lt_of_lt_of_le hd0 hden
  have hd0' : (0 : ℝ) < r.den := by exact_mod_cast hd0
  rw [Rat.cast_def, div_le_div_iff₀ hH0 hd0']
  have h1 : (1 : ℝ) ≤ r.num := by exact_mod_cast hnum
  have h2 : (r.den : ℝ) ≤ H := by exact_mod_cast hden
  nlinarith

/-- `|1/(2H) - y| ≥ 1/(2H)` para todo `y ∈ 𝒬_H` -/
lemma half_inv_le_dist {H : ℕ} (hH : 2 ≤ H) {y : ℚ} (hy : ht y ≤ H) :
    1 / (2 * (H : ℝ)) ≤ |1 / (2 * (H : ℝ)) - y| := by
  have hH0 : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  have hpos : 0 < 1 / (2 * (H : ℝ)) := by positivity
  rcases le_or_gt y 0 with h | h
  · have : (y : ℝ) ≤ 0 := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have h1 := inv_le_of_ht h hy
    have e : (1 : ℝ) / H = 2 * (1 / (2 * (H : ℝ))) := by field_simp
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith

/-- `dist(1/(2H), 𝒬_H) = 1/(2H)` -/
theorem infDist_QH {H : ℕ} (hH : 2 ≤ H) :
    Metric.infDist (1 / (2 * (H : ℝ))) ((fun r : ℚ => (r : ℝ)) '' QH H) = 1 / (2 * (H : ℝ)) := by
  have h0 : (0 : ℝ) ∈ (fun r : ℚ => (r : ℝ)) '' QH H :=
    ⟨0, by simp only [QH, mem_setOf_eq, ht, Rat.num_zero, Rat.den_zero]; omega, by simp⟩
  apply le_antisymm
  · have := Metric.infDist_le_dist_of_mem (x := 1 / (2 * (H : ℝ))) h0
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at this
  · rw [Metric.le_infDist ⟨0, h0⟩]
    rintro _ ⟨y, hy, rfl⟩
    rw [Real.dist_eq]
    exact half_inv_le_dist hH hy

/-- **Proposição IV.4.6 (piso aritmético uniforme)**, primeira parte:
com `h = H(N) ≥ 2` e `f ≡ 1/(2h)`, `e_N^{𝓛,H}(f) ≥ 1/(2h)`. -/
theorem arithmetic_floor (H : ℕ → ℕ) (N : ℕ) (hH : 2 ≤ H N) :
    ENNReal.ofReal (1 / (2 * (H N : ℝ))) ≤ pErr H N (fun _ => 1 / (2 * (H N : ℝ))) := by
  set a : ℝ := 1 / (2 * (H N : ℝ)) with ha
  have hH0 : (0 : ℝ) < H N := by exact_mod_cast (by omega : 0 < H N)
  have hpos : 0 < a := by rw [ha]; positivity
  have h01 : cellIcc 0 0 = Icc (0 : ℝ) 1 := by simp [cellIcc]
  unfold pErr
  refine le_iInf₂ fun g hg => ?_
  -- a point `x ∈ [0,1]` with `|a - g x| ≥ a`
  obtain ⟨x, hx, hgx⟩ : ∃ x ∈ Icc (0 : ℝ) 1, a ≤ |a - g x| := by
    rcases hg with rfl | ⟨T, ⟨hw, -, hh⟩, rfl⟩
    · exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simp [abs_of_pos hpos]⟩
    · obtain ⟨L, hL⟩ := T.leaves_eq_cons
      have hmem : T.firstLeaf ∈ T.leaves := by rw [hL]; exact List.mem_cons_self
      set b := T.firstLeaf
      have hx0 : ((b.x0 : ℚ) : ℝ) ∈ cellIcc b.k b.m := by
        have e : ((b.x0 : ℚ) : ℝ) = ((b.m : ℝ) + 1 / 2) / 2 ^ b.k := by simp [Atom.x0]
        rw [e, cellIcc_eq, cL, cR]
        exact ⟨(div_le_div_iff_of_pos_right (by positivity)).mpr (by linarith),
          (div_le_div_iff_of_pos_right (by positivity)).mpr (by linarith)⟩
      have hval : T.eval 0 0 (b.x0 : ℝ) = (b.y0 : ℝ) := by
        rw [eval_leaf hw b hmem _ hx0]
        simp [Atom.eval]
      have hht : ht b.y0 ≤ H N := by
        have h1 : ht b.y0 ≤ b.height := by unfold Atom.height; omega
        exact h1.trans ((le_maxHeight hmem).trans hh)
      refine ⟨(b.x0 : ℝ), ?_, ?_⟩
      · rw [← h01]; exact leaves_cell_sub hw b hmem hx0
      · rw [hval]; exact half_inv_le_dist hH hht
  unfold distInf
  exact (ENNReal.ofReal_le_ofReal hgx).trans
    (le_iSup₂ (f := fun x (_ : x ∈ Icc (0 : ℝ) 1) => ENNReal.ofReal |a - g x|) x hx)

/-- **Proposição IV.4.6**, consequência: se uma classe `F` contém as constantes `|a| ≤ 1/4`
e `sup_{f ∈ F} e_N^{𝓛,H}(f) ≤ C N^{-s}`, então `H(N) ≥ (2C)⁻¹ N^s` sempre que `H(N) ≥ 2`. -/
theorem height_lower_bound (H : ℕ → ℕ) (F : Set (ℝ → ℝ)) {C s : ℝ}
    (hconst : ∀ a : ℝ, |a| ≤ 1 / 4 → (fun _ => a) ∈ F)
    (hrate : ∀ N : ℕ, 1 ≤ N → ∀ f ∈ F, pErr H N f ≤ ENNReal.ofReal (C * (N : ℝ) ^ (-s)))
    {N : ℕ} (hN : 1 ≤ N) (hHN : 2 ≤ H N) :
    (2 * C)⁻¹ * (N : ℝ) ^ s ≤ H N := by
  have hh : (0 : ℝ) < H N := by exact_mod_cast (by omega : 0 < H N)
  have hh2 : (2 : ℝ) ≤ H N := by exact_mod_cast hHN
  have hmemF : (fun _ => 1 / (2 * (H N : ℝ))) ∈ F := hconst _ (by
    rw [abs_of_pos (by positivity), div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith)
  have h1 := (arithmetic_floor H N hHN).trans (hrate N hN _ hmemF)
  rw [ENNReal.ofReal_le_ofReal_iff'] at h1
  have hP : (0 : ℝ) < (N : ℝ) ^ s := Real.rpow_pos_of_pos (by exact_mod_cast hN) s
  rcases h1 with h1 | h1
  · rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv,
      div_le_div_iff₀ (by positivity) hP] at h1
    have hC : 0 < C := by nlinarith
    rw [inv_mul_le_iff₀ (by positivity)]
    linarith
  · exact absurd h1 (not_le.mpr (by positivity))

end Pendencias.Agenda
