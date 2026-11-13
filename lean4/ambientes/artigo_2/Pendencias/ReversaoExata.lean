import Pendencias.MarcadaParticao

/-!
# Reversibilidade exata: transporte dos parâmetros e realização

As definições usam funções em `[0,1]`, como no TeX. As árvores continuam avaliadas
em `ℝ`; `EqOn` exprime a igualdade das suas restrições ao domínio do enunciado.
-/

noncomputable section

namespace Pendencias.Marcada.RealReLU

open Artigo Set Classical

/-- Pertinência à classe marcada do TeX, como função no domínio `[0,1]`: uma árvore
marcada bem formada tem a mesma restrição ao intervalo. O uso de `EqOn` evita impor
condições a valores externos ao domínio que o TeX não menciona. -/
def MarkedRealizable {M : ℕ} (R : RealReLU M) : Prop :=
  ∃ T : MTree, MTree.MWF 0 0 T ∧ EqOn (MTree.eval 0 0 T) R.eval (Icc 0 1)

/-- Condições (marked-reversal-conditions) do TeX: os coeficientes são racionais
e cada quebra é a inclusão real de um racional de denominador potência de dois.
Essa última caracterização é exatamente a definição de número diádico. -/
def Arithmetic {M : ℕ} (R : RealReLU M) : Prop :=
  (∃ c : ℚ, R.c = (c : ℝ)) ∧ (∃ q : ℚ, R.q = (q : ℝ)) ∧
    (∀ i, ∃ a : ℚ, R.a i = (a : ℝ)) ∧
      ∀ i, ∃ t : ℚ, IsDyadic t ∧ R.τ i = (t : ℝ)

/-- Dados racionais da mesma fórmula do TeX quando as condições aritméticas valem.
A inclusão de `ℚ` em `ℝ` é injetiva, portanto as escolhas de testemunhas não mudam
parâmetros nem a função; a igualdade de avaliação é provada em `rationalData_eval`. -/
def rationalData {M : ℕ} (R : RealReLU M) (h : R.Arithmetic) : RedReLU :=
  ⟨h.1.choose, h.2.1.choose,
    List.ofFn fun i ↦ ((h.2.2.1 i).choose, (h.2.2.2 i).choose)⟩

lemma rationalData_eval {M : ℕ} (R : RealReLU M) (h : R.Arithmetic) :
    (R.rationalData h).eval = R.eval := by
  funext x
  simp only [RedReLU.eval, rationalData, List.map_ofFn, List.sum_ofFn, Function.comp_apply]
  rw [← h.1.choose_spec, ← h.2.1.choose_spec]
  unfold eval
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← (h.2.2.1 i).choose_spec, ← (h.2.2.2 i).choose_spec.2]

lemma rationalData_breaks {M : ℕ} (R : RealReLU M) (h : R.Arithmetic) :
    (R.rationalData h).breaks = Finset.univ.image (fun i ↦ (h.2.2.2 i).choose) := by
  ext t
  simp [RedReLU.breaks, rationalData, List.map_ofFn]

lemma rationalData_dyadic {M : ℕ} (R : RealReLU M) (h : R.Arithmetic) :
    ∀ t ∈ (R.rationalData h).breaks, IsDyadic t := by
  rw [R.rationalData_breaks h]
  intro t ht
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ht
  exact (h.2.2.2 i).choose_spec.1

lemma rationalData_interior {M : ℕ} (R : RealReLU M) (hR : R.Reduced) (h : R.Arithmetic) :
    ∀ t ∈ (R.rationalData h).breaks, (0 : ℝ) < t ∧ (t : ℝ) < 1 := by
  rw [R.rationalData_breaks h]
  intro t ht
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ht
  rw [← (h.2.2.2 i).choose_spec.2]
  exact hR.2.1 i

lemma rationalData_knots_injective {M : ℕ} (R : RealReLU M) (hR : R.Reduced)
    (h : R.Arithmetic) : Function.Injective (fun i ↦ (h.2.2.2 i).choose) := by
  intro i j hij
  apply hR.1.injective
  rw [(h.2.2.2 i).choose_spec.2, (h.2.2.2 j).choose_spec.2]
  exact congrArg (fun t : ℚ ↦ (t : ℝ)) hij

lemma rationalData_card {M : ℕ} (R : RealReLU M) (hR : R.Reduced) (h : R.Arithmetic) :
    (R.rationalData h).breaks.card = M := by
  rw [R.rationalData_breaks h, Finset.card_image_of_injective _
    (R.rationalData_knots_injective hR h), Finset.card_univ, Fintype.card_fin]

lemma rationalData_depth_sum {M : ℕ} (R : RealReLU M) (hR : R.Reduced) (h : R.Arithmetic) :
    (∑ t ∈ (R.rationalData h).breaks, Nat.log 2 t.den) =
      ∑ i, Nat.log 2 ((h.2.2.2 i).choose).den := by
  rw [R.rationalData_breaks h, Finset.sum_image]
  intro i _ j _ hij
  exact R.rationalData_knots_injective hR h hij

theorem marked_realizable_of_arithmetic {M : ℕ} (R : RealReLU M) (hR : R.Reduced)
    (h : R.Arithmetic) : R.MarkedRealizable := by
  let r := R.rationalData h
  let T := r.canonTree (canonShape r.breaks r.depth 0 0) 0 0
  obtain ⟨hw, he, _, _⟩ := r.canonTree_representation_bounds
    (R.rationalData_dyadic h) (R.rationalData_interior hR h)
  refine ⟨T, hw, ?_⟩
  rw [← R.rationalData_eval h]
  exact he

/-- Equivalência funcional e aritmética da primeira afirmação da reversibilidade rasa.
As afirmações sobre árvore mínima e biblioteca sem folhas planas são separadas. -/
theorem marked_realizable_iff {M : ℕ} (R : RealReLU M) (hR : R.Reduced) :
    R.MarkedRealizable ↔ R.Arithmetic := by
  constructor
  · rintro ⟨T, hw, he⟩
    exact R.parameters_necessary hR T hw he
  · exact R.marked_realizable_of_arithmetic hR

/-- A montagem associada à árvore `𝒯(S)` do TeX, com os dados aritméticos já
certificados. Cada folha recebe o valor no centro e a inclinação da própria função. -/
def canonicalTree {M : ℕ} (R : RealReLU M) (h : R.Arithmetic) : MTree :=
  let r := R.rationalData h
  r.canonTree (canonShape r.breaks r.depth 0 0) 0 0

/-- Profundidade diádica reduzida da quebra `i`: o logaritmo em base dois do
denominador reduzido da sua única representação racional. Como a quebra é diádica,
esse denominador é exatamente uma potência de dois, sem arredondamento. -/
def dyadicDepth {M : ℕ} (R : RealReLU M) (h : R.Arithmetic) (i : Fin M) : ℕ :=
  Nat.log 2 ((h.2.2.2 i).choose).den

theorem canonicalTree_spec {M : ℕ} (R : RealReLU M) (hR : R.Reduced) (h : R.Arithmetic) :
    MTree.MWF 0 0 (R.canonicalTree h) ∧
      EqOn (MTree.eval 0 0 (R.canonicalTree h)) R.eval (Icc 0 1) ∧
        M + 1 ≤ (R.canonicalTree h).numLeaves ∧
          (R.canonicalTree h).numLeaves ≤ 1 + ∑ i, R.dyadicDepth h i := by
  obtain ⟨hw, he, hlo, hhi⟩ := (R.rationalData h).canonTree_representation_bounds
    (R.rationalData_dyadic h) (R.rationalData_interior hR h)
  refine ⟨hw, ?_, ?_, ?_⟩
  · rw [← R.rationalData_eval h]
    exact he
  · simpa only [R.rationalData_card hR h] using hlo
  · simpa only [R.rationalData_depth_sum hR h, dyadicDepth] using hhi

lemma rationalData_breaks_sub_cuts {M : ℕ} (R : RealReLU M) (hR : R.Reduced)
    (h : R.Arithmetic) (T : MTree) (he : EqOn (MTree.eval 0 0 T) R.eval (Icc 0 1)) :
    (R.rationalData h).breaks ⊆ T.cuts 0 0 := by
  rw [R.rationalData_breaks h]
  intro t ht
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨s, hs, heq⟩ := R.breaks_mem_cuts hR T he i
  have hts : (h.2.2.2 i).choose = s := by
    apply Rat.cast_injective (α := ℝ)
    exact (h.2.2.2 i).choose_spec.2.symm.trans heq
  rwa [hts]

/-- Toda árvore que realiza a função refina a árvore canônica; a hipótese de forma
reduzida impede que saltos zero ou quebras canceladas criem fronteiras artificiais. -/
theorem realizes_refines_canonical {M : ℕ} (R : RealReLU M) (hR : R.Reduced)
    (h : R.Arithmetic) (T : MTree) (he : EqOn (MTree.eval 0 0 T) R.eval (Icc 0 1)) :
    T.shape.Refines (R.canonicalTree h).shape := by
  dsimp only [canonicalTree]
  rw [RedReLU.canonTree_shape]
  apply canonShape_least
  exact leavesAvoid_mono (R.rationalData_breaks_sub_cuts hR h T he) (T.leavesAvoid_cuts 0 0)

/-- Unicidade da árvore menos refinada que realiza a função, como forma diádica:
qualquer outra realização que também seja menos refinada tem a mesma árvore. -/
theorem canonicalTree_unique_least {M : ℕ} (R : RealReLU M) (hR : R.Reduced)
    (h : R.Arithmetic) (T : MTree) (he : EqOn (MTree.eval 0 0 T) R.eval (Icc 0 1))
    (hleast : ∀ U : MTree, MTree.MWF 0 0 U →
      EqOn (MTree.eval 0 0 U) R.eval (Icc 0 1) → U.shape.Refines T.shape) :
    T.shape = (R.canonicalTree h).shape := by
  obtain ⟨hw, hec, _, _⟩ := R.canonicalTree_spec hR h
  exact DShape.Refines.antisymm (R.realizes_refines_canonical hR h T he)
    (hleast _ hw hec)

/-- A unicidade também inclui os rótulos atômicos: a função realizada fixa o valor
central e a inclinação em cada folha, além da forma diádica da árvore mínima. -/
theorem canonicalTree_unique_least_labeled {M : ℕ} (R : RealReLU M) (hR : R.Reduced)
    (h : R.Arithmetic) (T : MTree) (hwT : MTree.MWF 0 0 T)
    (he : EqOn (MTree.eval 0 0 T) R.eval (Icc 0 1))
    (hleast : ∀ U : MTree, MTree.MWF 0 0 U →
      EqOn (MTree.eval 0 0 U) R.eval (Icc 0 1) → U.shape.Refines T.shape) :
    T = R.canonicalTree h := by
  obtain ⟨hw, hec, _, _⟩ := R.canonicalTree_spec hR h
  apply T.eq_of_shape_eval _ 0 0 hwT hw (R.canonicalTree_unique_least hR h T he hleast)
  intro x hx
  have hx' : x ∈ Icc (0 : ℝ) 1 := by simpa only [cellIcc, Int.cast_zero, pow_zero,
    zero_div, zero_add, div_one] using hx
  exact (he hx').trans (hec hx').symm

end Pendencias.Marcada.RealReLU
