module
public import RequestProject.Chain
public import RequestProject.Bridge

/-!
# Seção 8: extensão ReLU por recursão finita

Formalização da Seção 8 (`sec:relu`).
-/

@[expose] public section

open scoped Classical

noncomputable section

namespace Montagens

open Atom

variable {α β : ℝ} {Λ : Finset Atom}

namespace NormChain

variable (q : NormChain α β Λ)

/-- O índice `0 : Fin M` (válido porque `M ≥ 1`). -/
def i0 : Fin q.M := ⟨0, q.hM⟩

/-- Inclinações `s_j = a_j.s`. -/
def sl (j : Fin q.M) : ℚ := (q.a j).s

/-- `c₀ = u(a₀)`. -/
def c0 : ℚ := (q.a q.i0).u

/-- `w_j = s_j - s_{j-1}` (usado para `1 ≤ j < M`). -/
def wt (j : Fin q.M) : ℚ := q.sl j - q.sl ⟨j.val - 1, by omega⟩

end NormChain

/-- `ρ(x) = max {0, x}`. -/
def relu (x : ℝ) : ℝ := max 0 x

theorem continuous_relu : Continuous relu := by unfold relu; fun_prop

namespace NormChain

variable (q : NormChain α β Λ)

/-- As funções parciais `F_r`, por recursão em `r < M`:
`F₀(x) = c₀ + s₀ x`, `F_{r+1}(x) = F_r(x) + (s_{r+1} - s_r) ρ(x - t_{r+1})`. -/
def Fpart : (r : ℕ) → r < q.M → ℝ → ℝ
  | 0, _, x => (q.c0 : ℝ) + (q.sl q.i0 : ℝ) * x
  | r + 1, h, x => Fpart r (by omega) x +
      ((q.sl ⟨r + 1, h⟩ - q.sl ⟨r, by omega⟩ : ℚ) : ℝ) *
        relu (x - ((q.t ⟨r + 1, by omega⟩ : ℚ) : ℝ))

/-- `R(q) := F_{M-1}`. -/
def Rext : ℝ → ℝ := q.Fpart (q.M - 1) (by have := q.hM; omega)

theorem Sset_succ (r : ℕ) (hr : r + 1 < q.M) :
    Finset.univ.filter (fun j : Fin q.M => 1 ≤ j.val ∧ j.val ≤ r + 1) =
      insert ⟨r + 1, hr⟩ (Finset.univ.filter (fun j : Fin q.M => 1 ≤ j.val ∧ j.val ≤ r)) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
  omega

/-- Lema `lem:sum` (expansão da recursão). -/
theorem Fpart_sum (r : ℕ) (hr : r < q.M) (x : ℝ) :
    q.Fpart r hr x = (q.c0 : ℝ) + (q.sl q.i0 : ℝ) * x +
      ∑ j ∈ Finset.univ.filter (fun j : Fin q.M => 1 ≤ j.val ∧ j.val ≤ r),
        (q.wt j : ℝ) * relu (x - ((q.t j.castSucc : ℚ) : ℝ)) := by
  induction r with
  | zero =>
    have : Finset.univ.filter (fun j : Fin q.M => 1 ≤ j.val ∧ j.val ≤ 0) = ∅ := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      omega
    rw [this, Finset.sum_empty, add_zero]; rfl
  | succ r ih =>
    rw [Sset_succ q r hr, Finset.sum_insert (by simp)]
    rw [Fpart, ih (by omega)]
    have e1 : q.wt ⟨r + 1, hr⟩ = q.sl ⟨r + 1, hr⟩ - q.sl ⟨r, by omega⟩ := rfl
    have e2 : (Fin.castSucc ⟨r + 1, hr⟩ : Fin (q.M + 1)) = ⟨r + 1, by omega⟩ := rfl
    rw [e1, e2]; ring

/-- Fórmula (`eq:relu_sum`). -/
theorem Rext_sum (x : ℝ) :
    q.Rext x = (q.c0 : ℝ) + (q.sl q.i0 : ℝ) * x +
      ∑ j ∈ Finset.univ.filter (fun j : Fin q.M => 1 ≤ j.val),
        (q.wt j : ℝ) * relu (x - ((q.t j.castSucc : ℚ) : ℝ)) := by
  rw [Rext, Fpart_sum]
  congr 2
  apply Finset.filter_congr
  intro j _; constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, by omega⟩

theorem line_c0 : (q.a q.i0).line = fun x => (q.c0 : ℝ) + (q.sl q.i0 : ℝ) * x := by
  funext x; rw [(line_forms _).1 x]; rfl

/-- Fórmula (`eq:relu_anchor`). -/
theorem Rext_anchor (x : ℝ) :
    q.Rext x = (q.a q.i0).line ((q.t 0 : ℚ) : ℝ) +
      (q.sl q.i0 : ℝ) * (x - ((q.t 0 : ℚ) : ℝ)) +
      ∑ j ∈ Finset.univ.filter (fun j : Fin q.M => 1 ≤ j.val),
        (q.wt j : ℝ) * relu (x - ((q.t j.castSucc : ℚ) : ℝ)) := by
  rw [q.Rext_sum, line_c0]; ring

/-- Se `M = 1`, `R(q) = ℓ_{a₀}` em toda a reta. -/
theorem Rext_of_M_eq_one (hM1 : q.M = 1) : q.Rext = (q.a q.i0).line := by
  funext x
  rw [q.Rext_sum, line_c0]
  have : Finset.univ.filter (fun j : Fin q.M => 1 ≤ j.val) = ∅ := by
    ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    have := j.isLt; omega
  rw [this, Finset.sum_empty, add_zero]

/-- Lema `lem:incident` (identidade de duas retas incidentes). -/
theorem incident (j : ℕ) (hj : j + 1 < q.M)
    (h : (q.a ⟨j + 1, hj⟩).line ((q.t ⟨j + 1, by omega⟩ : ℚ) : ℝ) =
      (q.a ⟨j, by omega⟩).line ((q.t ⟨j + 1, by omega⟩ : ℚ) : ℝ)) (x : ℝ) :
    (q.a ⟨j + 1, hj⟩).line x - (q.a ⟨j, by omega⟩).line x =
      ((q.sl ⟨j + 1, hj⟩ - q.sl ⟨j, by omega⟩ : ℚ) : ℝ) *
        (x - ((q.t ⟨j + 1, by omega⟩ : ℚ) : ℝ)) := by
  rw [(line_forms _).1, (line_forms _).1] at h ⊢
  simp only [sl, Atom.b] at h ⊢
  push_cast
  linear_combination h

/-- O índice `M - 1 : Fin M`. -/
def iLast : Fin q.M := ⟨q.M - 1, by have := q.hM; omega⟩

theorem continuous_Fpart (r : ℕ) (hr : r < q.M) : Continuous (q.Fpart r hr) := by
  induction r with
  | zero => show Continuous (fun x => (q.c0 : ℝ) + (q.sl q.i0 : ℝ) * x); fun_prop
  | succ r ih =>
    have := ih (by omega)
    show Continuous (fun x => q.Fpart r (by omega) x +
      ((q.sl ⟨r + 1, hr⟩ - q.sl ⟨r, by omega⟩ : ℚ) : ℝ) *
        relu (x - ((q.t ⟨r + 1, by omega⟩ : ℚ) : ℝ)))
    have hr' := continuous_relu
    fun_prop

theorem t_strictMono : StrictMono q.t := Fin.strictMono_iff_lt_succ.2 q.t_lt

theorem t_le {i j : Fin (q.M + 1)} (h : i.val ≤ j.val) : q.t i ≤ q.t j :=
  q.t_strictMono.monotone h

theorem a_mem (j : Fin q.M) : q.a j ∈ NormK α β Λ := by
  rw [← q.a_image]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

theorem agree_consec (hA : Agree (NormK α β Λ)) (r : ℕ) (hr : r + 1 < q.M) :
    (q.a ⟨r + 1, hr⟩).line ((q.t ⟨r + 1, by omega⟩ : ℚ) : ℝ) =
      (q.a ⟨r, by omega⟩).line ((q.t ⟨r + 1, by omega⟩ : ℚ) : ℝ) := by
  apply hA _ (q.a_mem _) _ (q.a_mem _)
  refine ⟨?_, ?_⟩
  · rw [q.Ja_eq]
    have e : (Fin.castSucc ⟨r + 1, hr⟩ : Fin (q.M + 1)) = ⟨r + 1, by omega⟩ := rfl
    rw [e]
    exact ⟨le_rfl, by exact_mod_cast q.t_le (by simp)⟩
  · rw [q.Ja_eq]
    have e : (Fin.succ ⟨r, by omega⟩ : Fin (q.M + 1)) = ⟨r + 1, by omega⟩ := rfl
    rw [e]
    exact ⟨by exact_mod_cast q.t_le (by simp), le_rfl⟩

/-- `F_r(x) = ℓ_{a_r}(x)` para `x ≥ t_r`. -/
theorem Fpart_eq_line (hA : Agree (NormK α β Λ)) (r : ℕ) (hr : r < q.M) (x : ℝ)
    (hx : ((q.t ⟨r, by omega⟩ : ℚ) : ℝ) ≤ x) : q.Fpart r hr x = (q.a ⟨r, hr⟩).line x := by
  induction r with
  | zero => rw [Fpart]; exact (congrFun q.line_c0 x).symm
  | succ r ih =>
    have hx' : ((q.t ⟨r, by omega⟩ : ℚ) : ℝ) ≤ x :=
      le_trans (by exact_mod_cast q.t_le (by simp)) hx
    rw [Fpart, ih (by omega) hx']
    have hrelu : relu (x - ((q.t ⟨r + 1, by omega⟩ : ℚ) : ℝ)) =
        x - ((q.t ⟨r + 1, by omega⟩ : ℚ) : ℝ) := by
      unfold relu; exact max_eq_right (by linarith)
    rw [hrelu, ← q.incident r hr (q.agree_consec hA r hr) x]
    ring

/-- Os termos posteriores a `j` se anulam para `x ≤ t_{j+1}`. -/
theorem Fpart_stable (j : ℕ) (hj : j < q.M) (x : ℝ)
    (hx : x ≤ ((q.t ⟨j + 1, by omega⟩ : ℚ) : ℝ)) :
    ∀ k (hk : j + k < q.M), q.Fpart (j + k) hk x = q.Fpart j hj x := by
  intro k
  induction k with
  | zero => intro hk; rfl
  | succ k ih =>
    intro hk
    have e : j + (k + 1) = (j + k) + 1 := by omega
    have hrelu : relu (x - ((q.t ⟨j + k + 1, by omega⟩ : ℚ) : ℝ)) = 0 := by
      unfold relu; apply max_eq_left
      have : ((q.t ⟨j + 1, by omega⟩ : ℚ) : ℝ) ≤ ((q.t ⟨j + k + 1, by omega⟩ : ℚ) : ℝ) := by
        exact_mod_cast q.t_le (by simp)
      linarith
    simp only [e]
    rw [Fpart, hrelu, mul_zero, add_zero, ih (by omega)]

theorem Fpart_congr {r r' : ℕ} (e : r = r') (h : r < q.M) (h' : r' < q.M) (x : ℝ) :
    q.Fpart r h x = q.Fpart r' h' x := by subst e; rfl

theorem Rext_eq_Fpart_of_le (j : ℕ) (hj : j < q.M) (x : ℝ)
    (hx : x ≤ ((q.t ⟨j + 1, by omega⟩ : ℚ) : ℝ)) : q.Rext x = q.Fpart j hj x := by
  unfold Rext
  rw [q.Fpart_congr (show q.M - 1 = j + (q.M - 1 - j) by omega) _ (by omega)]
  exact q.Fpart_stable j hj x hx _ _

/-- Teorema `thm:extension` (correção da extensão). Os parâmetros de
(`eq:relu_sum`) são racionais por tipo (`c₀`, `s₀`, `w_j`, `t_j : ℚ`). -/
theorem extension (hK : α < β) {g : CK α β} (h : LocalRep α β g Λ) :
    Continuous q.Rext ∧
    (∀ j : Fin q.M, ∀ x : ℝ, ((q.t j.castSucc : ℚ) : ℝ) ≤ x →
        x ≤ ((q.t j.succ : ℚ) : ℝ) → q.Rext x = (q.a j).line x) ∧
    (∀ z : Set.Icc α β, q.Rext z = g z) ∧
    (∀ x : ℝ, x ≤ ((q.t 0 : ℚ) : ℝ) → q.Rext x = (q.a q.i0).line x) ∧
    (∀ x : ℝ, ((q.t q.iLast.castSucc : ℚ) : ℝ) ≤ x → q.Rext x = (q.a q.iLast).line x) ∧
    (∀ j : Fin (q.M + 1), 1 ≤ j.val → j.val < q.M →
        ((q.t j : ℚ) : ℝ) ∈ Kint α β ∩ Dy) ∧
    (∀ hM : 1 < q.M, ∀ x : ℝ, x ≤ ((q.t ⟨1, by omega⟩ : ℚ) : ℝ) →
        q.Rext x = (q.a q.i0).line x) := by
  obtain ⟨-, ⟨hCov, -⟩, -, ⟨⟨-, -, hMatch⟩, hA⟩, -⟩ := normalization hK h
  have hM := q.hM
  have hpiece : ∀ j : Fin q.M, ∀ x : ℝ, ((q.t j.castSucc : ℚ) : ℝ) ≤ x →
      x ≤ ((q.t j.succ : ℚ) : ℝ) → q.Rext x = (q.a j).line x := by
    intro j x hx1 hx2
    rw [q.Rext_eq_Fpart_of_le j.val j.isLt x hx2]
    exact q.Fpart_eq_line hA j.val j.isLt x hx1
  have hfirst : ∀ x : ℝ, x ≤ ((q.t ⟨1, by omega⟩ : ℚ) : ℝ) →
      q.Rext x = (q.a q.i0).line x := by
    intro x hx
    rw [q.Rext_eq_Fpart_of_le 0 hM x hx, Fpart]
    exact (congrFun q.line_c0 x).symm
  refine ⟨q.continuous_Fpart _ _, hpiece, ?_, ?_, ?_, ?_, fun _ => hfirst⟩
  · intro z
    obtain ⟨b, hb, hzb⟩ := hCov z z.2
    rw [← q.a_image, Finset.mem_image] at hb
    obtain ⟨j, -, rfl⟩ := hb
    rw [q.Ja_eq] at hzb
    rw [hpiece j z hzb.1 hzb.2]
    exact (hMatch _ (q.a_mem j) z (by rw [q.Ja_eq]; exact hzb)).symm
  · intro x hx
    apply hfirst
    exact le_trans hx (by exact_mod_cast q.t_le (by simp))
  · intro x hx
    unfold Rext
    exact q.Fpart_eq_line hA _ _ x hx
  · intro j hj1 hj2
    refine ⟨q.t_inner j hj1 hj2, ?_⟩
    have e : j = (⟨j.val - 1, by omega⟩ : Fin q.M).succ := Fin.ext (by simp; omega)
    rw [e, ← q.a_right]
    exact (geometry _).2.2.2.2.2.2.2.2.2.1

/-- Forma local à esquerda: `R(q)` é a primeira reta em `(-∞, α + η]`. -/
theorem left_form (hK : α < β) {g : CK α β} (h : LocalRep α β g Λ) :
    ∃ η > 0, ∀ x ≤ α + η, q.Rext x = ((q.a q.i0).u : ℝ) + ((q.a q.i0).b : ℝ) * x := by
  have hext := q.extension hK h
  rcases Nat.lt_or_ge 1 q.M with hM | hM
  · have hin := q.t_inner ⟨1, by omega⟩ le_rfl hM
    refine ⟨((q.t ⟨1, by omega⟩ : ℚ) : ℝ) - α, by linarith [hin.1], fun x hx => ?_⟩
    rw [hext.2.2.2.2.2.2 hM x (by linarith), (line_forms _).1]
  · have hM1 : q.M = 1 := le_antisymm hM q.hM
    refine ⟨β - α, by linarith, fun x _ => ?_⟩
    rw [q.Rext_of_M_eq_one hM1, (line_forms _).1]

/-- Forma local à direita: `R(q)` é a última reta em `[β - η, ∞)`. -/
theorem right_form (hK : α < β) {g : CK α β} (h : LocalRep α β g Λ) :
    ∃ η > 0, ∀ x, β - η ≤ x →
      q.Rext x = ((q.a q.iLast).u : ℝ) + ((q.a q.iLast).b : ℝ) * x := by
  have hext := q.extension hK h
  rcases Nat.lt_or_ge 1 q.M with hM | hM
  · have hin := q.t_inner q.iLast.castSucc (by simp [iLast]; omega) (by simp [iLast]; omega)
    refine ⟨β - ((q.t q.iLast.castSucc : ℚ) : ℝ), by linarith [hin.2], fun x hx => ?_⟩
    rw [hext.2.2.2.2.1 x (by linarith), (line_forms _).1]
  · have hM1 : q.M = 1 := le_antisymm hM q.hM
    have e : q.iLast = q.i0 := Fin.ext (by simp [iLast, i0]; omega)
    refine ⟨β - α, by linarith, fun x _ => ?_⟩
    rw [q.Rext_of_M_eq_one hM1, e, (line_forms _).1]

end NormChain

/-- Lema `lem:two_points` (unicidade de uma reta a partir de dois pontos). -/
theorem affine_eq_of_two_points {c s c' s' x₁ x₂ : ℝ} (hx : x₁ ≠ x₂)
    (h₁ : c + s * x₁ = c' + s' * x₁) (h₂ : c + s * x₂ = c' + s' * x₂) :
    ∀ x : ℝ, c + s * x = c' + s' * x := by
  have hs : s = s' := by
    have : (s - s') * (x₂ - x₁) = 0 := by linear_combination h₂ - h₁
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd (by linarith : x₁ = x₂) hx
  have hc : c = c' := by subst hs; linarith
  intro x; rw [hs, hc]

theorem agree_left_of_affine (hK : α < β) {F1 F2 : ℝ → ℝ}
    (h12 : ∀ x, α ≤ x → x ≤ β → F1 x = F2 x) {c s c' s' η η' : ℝ} (hη : 0 < η) (hη' : 0 < η')
    (h1 : ∀ x ≤ α + η, F1 x = c + s * x) (h2 : ∀ x ≤ α + η', F2 x = c' + s' * x) :
    ∀ x ≤ α, F1 x = F2 x := by
  set d := min (β - α) (min η η') with hd
  have hd0 : 0 < d := lt_min (by linarith) (lt_min hη hη')
  have hd1 : d ≤ β - α := min_le_left _ _
  have hd2 : d ≤ η := le_trans (min_le_right _ _) (min_le_left _ _)
  have hd3 : d ≤ η' := le_trans (min_le_right _ _) (min_le_right _ _)
  have key : ∀ y, α ≤ y → y ≤ α + d → c + s * y = c' + s' * y := by
    intro y hy1 hy2
    rw [← h1 y (by linarith), ← h2 y (by linarith)]
    exact h12 y hy1 (by linarith)
  have hall := affine_eq_of_two_points (x₁ := α + d / 3) (x₂ := α + 2 * d / 3)
    (by intro h; linarith) (key _ (by linarith) (by linarith)) (key _ (by linarith) (by linarith))
  intro x hx
  rw [h1 x (by linarith), h2 x (by linarith), hall x]

theorem agree_right_of_affine (hK : α < β) {F1 F2 : ℝ → ℝ}
    (h12 : ∀ x, α ≤ x → x ≤ β → F1 x = F2 x) {c s c' s' η η' : ℝ} (hη : 0 < η) (hη' : 0 < η')
    (h1 : ∀ x, β - η ≤ x → F1 x = c + s * x) (h2 : ∀ x, β - η' ≤ x → F2 x = c' + s' * x) :
    ∀ x, β ≤ x → F1 x = F2 x := by
  set d := min (β - α) (min η η') with hd
  have hd0 : 0 < d := lt_min (by linarith) (lt_min hη hη')
  have hd1 : d ≤ β - α := min_le_left _ _
  have hd2 : d ≤ η := le_trans (min_le_right _ _) (min_le_left _ _)
  have hd3 : d ≤ η' := le_trans (min_le_right _ _) (min_le_right _ _)
  have key : ∀ y, β - d ≤ y → y ≤ β → c + s * y = c' + s' * y := by
    intro y hy1 hy2
    rw [← h1 y (by linarith), ← h2 y (by linarith)]
    exact h12 y (by linarith) hy2
  have hall := affine_eq_of_two_points (x₁ := β - d / 3) (x₂ := β - 2 * d / 3)
    (by intro h; linarith) (key _ (by linarith) (by linarith)) (key _ (by linarith) (by linarith))
  intro x hx
  rw [h1 x (by linarith), h2 x (by linarith), hall x]

/-- Teorema `thm:unique` (independência da testemunha). -/
theorem Rext_unique (hK : α < β) {g : CK α β} {Λ Λ' : Finset Atom}
    (h : LocalRep α β g Λ) (h' : LocalRep α β g Λ')
    (q : NormChain α β Λ) (q' : NormChain α β Λ') : q.Rext = q'.Rext := by
  have hK12 : ∀ x, α ≤ x → x ≤ β → q.Rext x = q'.Rext x := by
    intro x h1 h2
    have e1 := (q.extension hK h).2.2.1 ⟨x, h1, h2⟩
    have e2 := (q'.extension hK h').2.2.1 ⟨x, h1, h2⟩
    simp only at e1 e2
    rw [e1, e2]
  obtain ⟨η, hη, hl⟩ := q.left_form hK h
  obtain ⟨η', hη', hl'⟩ := q'.left_form hK h'
  obtain ⟨θ, hθ, hr⟩ := q.right_form hK h
  obtain ⟨θ', hθ', hr'⟩ := q'.right_form hK h'
  funext x
  rcases le_or_gt x α with hx | hx
  · exact agree_left_of_affine hK hK12 hη hη' hl hl' x hx
  rcases le_or_gt β x with hx' | hx'
  · exact agree_right_of_affine hK hK12 hθ hθ' hr hr' x hx'
  · exact hK12 x hx.le hx'.le

/-- A extensão `R(q)` como função contínua `ℝ → ℝ`. -/
def NormChain.RextC (hK : α < β) {g : CK α β} (h : LocalRep α β g Λ)
    (q : NormChain α β Λ) : C(ℝ, ℝ) :=
  ⟨q.Rext, (q.extension hK h).1⟩

/-- O operador de extensão das montagens `ℰ_K : {g : C_K | g ∈ 𝒜^loc(K)} → C(ℝ, ℝ)`,
definido como a extensão `R(q)` produzida por uma representação local e
pela cadeia construída no Teorema `thm:chain`. -/
def extOp (hK : α < β) (g : {g : CK α β // g ∈ Aloc α β}) : C(ℝ, ℝ) :=
  (chainOf hK (Classical.choose_spec (show ∃ Λ, LocalRep α β g.1 Λ from g.2))).RextC hK
    (Classical.choose_spec (show ∃ Λ, LocalRep α β g.1 Λ from g.2))

/-- `ℰ_K(g)` coincide com `R(q)` para qualquer representação local e qualquer
cadeia válida (independência da prova, da testemunha e da cadeia). -/
theorem extOp_eq (hK : α < β) (g : {g : CK α β // g ∈ Aloc α β}) {Λ : Finset Atom}
    (h : LocalRep α β g.1 Λ) (q : NormChain α β Λ) : ⇑(extOp hK g) = q.Rext :=
  Rext_unique hK (Classical.choose_spec (show ∃ Λ, LocalRep α β g.1 Λ from g.2)) h _ q

/-- `Res_K(ℰ_K(g)) = g`. -/
theorem Res_extOp (hK : α < β) (g : {g : CK α β // g ∈ Aloc α β})
    (hc : ContOn α β (extOp hK g)) : Res (extOp hK g) hc = g.1 := by
  obtain ⟨Λ, h⟩ := (show ∃ Λ, LocalRep α β g.1 Λ from g.2)
  ext z
  change extOp hK g z = g.1 z
  rw [extOp_eq hK g h (chainOf hK h)]
  exact (NormChain.extension _ hK h).2.2.1 z

end Montagens

end
