import Pendencias.Ponte
import RequestProject.DyadicTools
import RequestProject.Uniform

/-!
# V.6.1 — taxa garantida em árvores

Para uma célula `K = J_{k₀,m₀}`, uma partição em árvore `Λ` é uma `DShape` com raiz `K`, e
`‖f - P_Λ f‖_{∞,K}` é `Λ.treeErr f k₀ m₀` (máximo dos erros de interpolação nas folhas). Logo
`σ_N^{dia}(f)_∞ = Edia f k₀ m₀ N` (eq. sigma-dyadic do complemento).

* `tree_rate_pow`, `tree_rate`: com `f ∈ C²(K)` (`ContDiffOn`), `L = |K|`, `|f''| ≤ M` em `K`:
  `σ_{2^r}^{dia}(f) ≤ M L²/(8·4^r)` e `σ_N^{dia}(f) ≤ M L²/(2N²)`;
* `tree_rationalization`: para toda árvore finita `Λ` e `δ > 0` há uma montagem racional na mesma
  árvore com erro `< ‖f - P_Λ f‖_∞ + δ` (`f` contínua em `K`).
-/

namespace Pendencias

open Set Artigo LTree DShape

/-! ## Taxa -/

section rate

variable {f : ℝ → ℝ} {k₀ : ℕ} {m₀ : ℤ} {M : ℝ}

/-- erro de interpolação numa subcélula `J ⊆ K` com `|f''| ≤ M` em `K` -/
lemma locErr_le_sub (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀))
    (hM : ∀ x ∈ cellIcc k₀ m₀, |derivWithin (derivWithin f (cellIcc k₀ m₀)) (cellIcc k₀ m₀) x| ≤ M)
    {k : ℕ} {m : ℤ} (hsub : cellIcc k m ⊆ cellIcc k₀ m₀) :
    locErr f k m ≤ (cR k m - cL k m) ^ 2 / 8 * M := by
  have hab := cL_lt_cR k₀ m₀
  have hF := extF_contDiff hab hf
  rw [← locErr_congr ((eqOn_cell f k₀ m₀).mono hsub)]
  refine (locErr_le_iff hF.continuous.continuousOn).mpr fun x hx => ?_
  exact interp_remainder_C2 hF (cL_lt_cR k m) (fun y hy => by
    rw [eqOn_cell_d2 hf (hsub hy)]; exact hM y (hsub hy)) x hx

/-- `σ_N^{dia}(f) ≤ M L² / (8 (2^{⌊log₂ N⌋})²)` -/
lemma tree_rate_aux (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀))
    (hM : ∀ x ∈ cellIcc k₀ m₀, |derivWithin (derivWithin f (cellIcc k₀ m₀)) (cellIcc k₀ m₀) x| ≤ M)
    (r N : ℕ) (hN : 2 ^ r ≤ N) :
    Edia f k₀ m₀ N ≤ M * (cR k₀ m₀ - cL k₀ m₀) ^ 2 / (8 * ((2 : ℝ) ^ r) ^ 2) := by
  refine (Edia_le_treeErr (by rw [numLeaves_uniform]; exact hN)).trans ?_
  refine treeErr_uniform_le r k₀ m₀ fun i hi => ?_
  have hsub : cellIcc (k₀ + r) (m₀ * 2 ^ r + i) ⊆ cellIcc k₀ m₀ :=
    cell_sub_of_desc (by omega) (by rw [show k₀ + r - k₀ = r by omega]; exact desc_index m₀ r i hi)
  refine (locErr_le_sub hf hM hsub).trans (le_of_eq ?_)
  rw [cell_len_desc k₀ r m₀]
  field_simp

/-- **Teorema V.6.1**, `N = 2^r`: `σ_N^{dia}(f) ≤ M L²/(8N²)` -/
theorem tree_rate_pow (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀))
    (hM : ∀ x ∈ cellIcc k₀ m₀, |derivWithin (derivWithin f (cellIcc k₀ m₀)) (cellIcc k₀ m₀) x| ≤ M)
    (r : ℕ) :
    Edia f k₀ m₀ (2 ^ r) ≤ M * (cR k₀ m₀ - cL k₀ m₀) ^ 2 / (8 * ((2 ^ r : ℕ) : ℝ) ^ 2) := by
  push_cast
  exact tree_rate_aux hf hM r _ le_rfl

/-- **Teorema V.6.1**, `N ≥ 2` qualquer: `σ_N^{dia}(f) ≤ M L²/(2N²)` -/
theorem tree_rate (hf : ContDiffOn ℝ 2 f (cellIcc k₀ m₀))
    (hM : ∀ x ∈ cellIcc k₀ m₀, |derivWithin (derivWithin f (cellIcc k₀ m₀)) (cellIcc k₀ m₀) x| ≤ M)
    {N : ℕ} (hN : 2 ≤ N) :
    Edia f k₀ m₀ N ≤ M * (cR k₀ m₀ - cL k₀ m₀) ^ 2 / (2 * (N : ℝ) ^ 2) := by
  have hab := cL_lt_cR k₀ m₀
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM _ (by rw [cellIcc_eq]; exact ⟨le_rfl, hab.le⟩))
  set r := Nat.log 2 N
  have h1 : 2 ^ r ≤ N := Nat.pow_log_le_self 2 (by omega)
  have h2 : N < 2 ^ (r + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have h2' : (N : ℝ) < 2 * 2 ^ r := by rw [← pow_succ']; exact_mod_cast h2
  have hN0 : (0 : ℝ) < N := by positivity
  refine (tree_rate_aux hf hM r N h1).trans ?_
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  nlinarith

end rate

/-! ## Racionalização na mesma árvore -/

/-- extremos racionais de `J_{k,m}` -/
def lq (k : ℕ) (m : ℤ) : ℚ := m / 2 ^ k
def rq (k : ℕ) (m : ℤ) : ℚ := (m + 1) / 2 ^ k

lemma lq_cast (k : ℕ) (m : ℤ) : ((lq k m : ℚ) : ℝ) = cL k m := by simp [lq, cL]
lemma rq_cast (k : ℕ) (m : ℤ) : ((rq k m : ℚ) : ℝ) = cR k m := by simp [rq, cR]

lemma lq_ne_rq (k : ℕ) (m : ℤ) : lq k m ≠ rq k m := by
  intro h
  have := congrArg (fun q : ℚ => (q : ℝ)) h
  simp only [lq_cast, rq_cast] at this
  exact (cL_lt_cR k m).ne this

lemma lq_mem (k : ℕ) (m : ℤ) : ((lq k m : ℚ) : ℝ) ∈ cellIcc k m := by
  rw [lq_cast, cellIcc_eq]; exact ⟨le_rfl, (cL_lt_cR k m).le⟩

lemma rq_mem (k : ℕ) (m : ℤ) : ((rq k m : ℚ) : ℝ) ∈ cellIcc k m := by
  rw [rq_cast, cellIcc_eq]; exact ⟨(cL_lt_cR k m).le, le_rfl⟩

lemma lq_child_left (k : ℕ) (m : ℤ) : lq (k + 1) (2 * m) = lq k m := by
  unfold lq; push_cast; rw [pow_succ]; field_simp

lemma rq_child_right (k : ℕ) (m : ℤ) : rq (k + 1) (2 * m + 1) = rq k m := by
  unfold rq; push_cast; rw [pow_succ]; field_simp; ring

lemma rq_child_left (k : ℕ) (m : ℤ) : rq (k + 1) (2 * m) = lq (k + 1) (2 * m + 1) := by
  unfold rq lq; push_cast; ring

/-- átomo da folha `J_{k,m}` interpolando os valores nodais `v` -/
def leafAtom (v : ℚ → ℚ) (k : ℕ) (m : ℤ) : Atom :=
  if h : v (lq k m) ≠ v (rq k m) then Atom.ofEndpoints k m _ _ h else ⟨k, m, 0, 1, one_ne_zero⟩

/-- a montagem com valores nodais `v` sobre a forma `Λ` -/
def realize (v : ℚ → ℚ) : DShape → ℕ → ℤ → LTree
  | .leaf, k, m => .leaf (leafAtom v k m)
  | .node l r, k, m => .node (realize v l (k + 1) (2 * m)) (realize v r (k + 1) (2 * m + 1))

/-- forma de uma representação -/
def shapeL : LTree → DShape
  | .leaf _ => .leaf
  | .node l r => .node (shapeL l) (shapeL r)

lemma shapeL_realize (v : ℚ → ℚ) : ∀ (T : DShape) (k : ℕ) (m : ℤ), shapeL (realize v T k m) = T
  | .leaf, _, _ => rfl
  | .node l r, k, m => by simp only [realize, shapeL, shapeL_realize v l, shapeL_realize v r]

section realize

variable {v : ℚ → ℚ} {S : Set ℝ}
  (hv : ∀ t t' : ℚ, (t : ℝ) ∈ S → (t' : ℝ) ∈ S → v t = v t' → t = t')
include hv

lemma leafAtom_ne {k : ℕ} {m : ℤ} (hsub : cellIcc k m ⊆ S) : v (lq k m) ≠ v (rq k m) :=
  fun h => lq_ne_rq k m (hv _ _ (hsub (lq_mem k m)) (hsub (rq_mem k m)) h)

lemma realize_lval : ∀ (T : DShape) (k : ℕ) (m : ℤ), cellIcc k m ⊆ S →
    (realize v T k m).lval = v (lq k m)
  | .leaf, k, m, hsub => by
      simp only [realize, LTree.lval, leafAtom, dif_pos (leafAtom_ne hv hsub),
        Atom.ofEndpoints_lval]
  | .node l _, k, m, hsub => by
      simp only [realize, LTree.lval]
      rw [realize_lval l _ _ ((cell_child_left_sub k m).trans hsub), lq_child_left]

lemma realize_rval : ∀ (T : DShape) (k : ℕ) (m : ℤ), cellIcc k m ⊆ S →
    (realize v T k m).rval = v (rq k m)
  | .leaf, k, m, hsub => by
      simp only [realize, LTree.rval, leafAtom, dif_pos (leafAtom_ne hv hsub),
        Atom.ofEndpoints_rval]
  | .node _ r, k, m, hsub => by
      simp only [realize, LTree.rval]
      rw [realize_rval r _ _ ((cell_child_right_sub k m).trans hsub), rq_child_right]

lemma realize_WF : ∀ (T : DShape) (k : ℕ) (m : ℤ), cellIcc k m ⊆ S → WF k m (realize v T k m)
  | .leaf, k, m, _ => by
      simp only [realize, WF, leafAtom]; split_ifs <;> exact ⟨rfl, rfl⟩
  | .node l r, k, m, hsub => by
      have hl := (cell_child_left_sub k m).trans hsub
      have hr := (cell_child_right_sub k m).trans hsub
      refine ⟨realize_WF l _ _ hl, realize_WF r _ _ hr, ?_⟩
      rw [realize_rval hv l _ _ hl, realize_lval hv r _ _ hr, rq_child_left]

/-- erro da montagem racional: `|f - g| ≤ ‖f - P_Λ f‖ + η` se `|f - v| ≤ η` nos nós -/
lemma realize_error {f : ℝ → ℝ} {η : ℝ} (hf : ContinuousOn f S)
    (hη : ∀ t : ℚ, (t : ℝ) ∈ S → |f t - v t| ≤ η) :
    ∀ (T : DShape) (k : ℕ) (m : ℤ), cellIcc k m ⊆ S → ∀ x ∈ cellIcc k m,
      |f x - (realize v T k m).eval k m x| ≤ T.treeErr f k m + η
  | .leaf, k, m, hsub, x, hx => by
      have hne := leafAtom_ne hv hsub
      simp only [realize, LTree.eval, DShape.treeErr, leafAtom, dif_pos hne]
      rw [Atom.eval_interp, Atom.ofEndpoints_lval, Atom.ofEndpoints_rval]
      simp only [Atom.ofEndpoints]
      have hθ := theta_mem hx
      have hA : |f (cL k m) - (v (lq k m) : ℝ)| ≤ η := by
        have := hη _ (hsub (lq_mem k m)); rwa [lq_cast] at this
      have hB : |f (cR k m) - (v (rq k m) : ℝ)| ≤ η := by
        have := hη _ (hsub (rq_mem k m)); rwa [rq_cast] at this
      have hc := convex_comb_dist hθ.1 hθ.2 hA hB
      rw [← linInterp_cell] at hc
      have hloc := le_locErr (hf.mono hsub) hx
      calc |f x - ((v (lq k m) : ℝ) + ((v (rq k m) : ℝ) - v (lq k m)) * 2 ^ k * (x - cL k m))|
          ≤ |f x - linInterp f (cL k m) (cR k m) x| +
            |linInterp f (cL k m) (cR k m) x -
              ((1 - 2 ^ k * (x - cL k m)) * (v (lq k m) : ℝ) +
                2 ^ k * (x - cL k m) * (v (rq k m) : ℝ))| := by
            have e : (v (lq k m) : ℝ) + ((v (rq k m) : ℝ) - v (lq k m)) * 2 ^ k * (x - cL k m) =
                (1 - 2 ^ k * (x - cL k m)) * (v (lq k m) : ℝ) +
                  2 ^ k * (x - cL k m) * (v (rq k m) : ℝ) := by ring
            rw [e]; exact abs_sub_le _ _ _
        _ ≤ locErr f k m + η := add_le_add hloc hc
  | .node l r, k, m, hsub, x, hx => by
      have hl := (cell_child_left_sub k m).trans hsub
      have hr := (cell_child_right_sub k m).trans hsub
      simp only [realize, LTree.eval, DShape.treeErr]
      rw [cellIcc_eq] at hx
      split_ifs with hxc
      · have := realize_error hf hη l _ _ hl x (by
          rw [cellIcc_eq, cL_child_left, cR_child_left]; exact ⟨hx.1, hxc.le⟩)
        linarith [le_max_left (l.treeErr f (k + 1) (2 * m)) (r.treeErr f (k + 1) (2 * m + 1))]
      · have := realize_error hf hη r _ _ hr x (by
          rw [cellIcc_eq, cR_child_right]; exact ⟨not_lt.mp hxc, hx.2⟩)
        linarith [le_max_right (l.treeErr f (k + 1) (2 * m)) (r.treeErr f (k + 1) (2 * m + 1))]

end realize

/-- valores nodais racionais injetivos: `v(t) = round(Q f(t))/Q + (t - a)/(2Q)` -/
noncomputable def qv (f : ℝ → ℝ) (Q : ℕ) (a t : ℚ) : ℚ :=
  ((round ((Q : ℝ) * f t) : ℤ) : ℚ) / Q + (t - a) / (2 * Q)

lemma qv_injective {f : ℝ → ℝ} {Q : ℕ} (hQ : 0 < Q) {a t t' : ℚ} (ht : a ≤ t ∧ t ≤ a + 1)
    (ht' : a ≤ t' ∧ t' ≤ a + 1) (h : qv f Q a t = qv f Q a t') : t = t' := by
  unfold qv at h
  set n := round ((Q : ℝ) * f t)
  set n' := round ((Q : ℝ) * f t')
  have hQ' : (0 : ℚ) < Q := by exact_mod_cast hQ
  have h2 : (2 * (n - n') : ℚ) = t' - t := by
    field_simp at h; linarith
  have hb1 : (2 * (n - n') : ℤ) ≤ 1 := by
    have : (2 * (n - n') : ℚ) ≤ 1 := by rw [h2]; linarith
    exact_mod_cast this
  have hb2 : -1 ≤ (2 * (n - n') : ℤ) := by
    have : (-1 : ℚ) ≤ 2 * (n - n') := by rw [h2]; linarith
    exact_mod_cast this
  have hnn : n = n' := by omega
  rw [hnn, sub_self, mul_zero] at h2
  linarith

lemma qv_err {f : ℝ → ℝ} {Q : ℕ} (hQ : 0 < Q) {a t : ℚ} (ht : a ≤ t ∧ t ≤ a + 1) :
    |f t - qv f Q a t| ≤ 1 / Q := by
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hr := abs_sub_round ((Q : ℝ) * f t)
  have e1 : |f t - ((round ((Q : ℝ) * f t) : ℤ) : ℝ) / Q| = |(Q : ℝ) * f t - round ((Q : ℝ) * f t)| / Q := by
    rw [← abs_of_pos hQ', ← abs_div, abs_of_pos hQ']; congr 1; field_simp
  have hta : ((t : ℝ) - a) / (2 * Q) ≤ 1 / (2 * Q) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : (t : ℝ) ≤ a + 1 := by exact_mod_cast ht.2
    linarith
  have hta0 : 0 ≤ ((t : ℝ) - a) / (2 * Q) := by
    apply div_nonneg _ (by positivity)
    have : (a : ℝ) ≤ t := by exact_mod_cast ht.1
    linarith
  unfold qv
  push_cast
  calc |f t - ((round ((Q : ℝ) * f t) : ℤ) / (Q : ℝ) + ((t : ℝ) - a) / (2 * Q))|
      ≤ |f t - ((round ((Q : ℝ) * f t) : ℤ) : ℝ) / Q| + ((t : ℝ) - a) / (2 * Q) := by
        rw [show f t - ((round ((Q : ℝ) * f t) : ℤ) / (Q : ℝ) + ((t : ℝ) - a) / (2 * Q)) =
          (f t - ((round ((Q : ℝ) * f t) : ℤ) : ℝ) / Q) - ((t : ℝ) - a) / (2 * Q) by ring]
        exact (abs_sub _ _).trans (by rw [abs_of_nonneg hta0])
    _ ≤ (1 / 2) / Q + 1 / (2 * Q) := by
        rw [e1]; gcongr
    _ = 1 / Q := by field_simp; ring

/-- **Teorema V.6.1**, racionalização: para toda árvore finita `Λ` com raiz `K` e `δ > 0`, há
uma montagem racional na mesma árvore cujo erro é menor que `‖f - P_Λ f‖_{∞,K} + δ`. -/
theorem tree_rationalization {f : ℝ → ℝ} {k₀ : ℕ} {m₀ : ℤ} (hf : ContinuousOn f (cellIcc k₀ m₀))
    (T : DShape) {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : LTree, WF k₀ m₀ R ∧ shapeL R = T ∧
      ∀ x ∈ cellIcc k₀ m₀, |f x - R.eval k₀ m₀ x| < T.treeErr f k₀ m₀ + δ := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  set Q := n + 1
  have hQ : 0 < Q := Nat.succ_pos n
  set a := lq k₀ m₀
  -- `K ⊆ [a, a+1]` em ℚ
  have hK : ∀ t : ℚ, (t : ℝ) ∈ cellIcc k₀ m₀ → a ≤ t ∧ t ≤ a + 1 := by
    intro t ht
    rw [cellIcc_eq] at ht
    have hlen : cR k₀ m₀ - cL k₀ m₀ ≤ 1 := by
      rw [cell_len]; exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    constructor
    · have : (a : ℝ) ≤ t := by rw [lq_cast]; exact ht.1
      exact_mod_cast this
    · have : (t : ℝ) ≤ a + 1 := by rw [lq_cast]; linarith [ht.2]
      exact_mod_cast this
  have hv : ∀ t t' : ℚ, (t : ℝ) ∈ cellIcc k₀ m₀ → (t' : ℝ) ∈ cellIcc k₀ m₀ →
      qv f Q a t = qv f Q a t' → t = t' :=
    fun t t' ht ht' h => qv_injective hQ (hK t ht) (hK t' ht') h
  have hη : ∀ t : ℚ, (t : ℝ) ∈ cellIcc k₀ m₀ → |f t - qv f Q a t| ≤ 1 / Q :=
    fun t ht => qv_err hQ (hK t ht)
  refine ⟨realize (qv f Q a) T k₀ m₀, realize_WF hv T k₀ m₀ subset_rfl,
    shapeL_realize _ T k₀ m₀, fun x hx => ?_⟩
  have := realize_error hv hf hη T k₀ m₀ subset_rfl x hx
  have hQd : (1 : ℝ) / Q < δ := by simpa [Q] using hn
  linarith

end Pendencias
