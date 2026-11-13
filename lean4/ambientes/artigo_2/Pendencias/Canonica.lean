import Pendencias.Marcada

/-!
# Árvores canônicas: ordem de refinamento e minimalidade

Lemas auxiliares para a reversibilidade rasa. Este módulo não afirma o fechamento
do item IV.5.2: ainda faltam a equivalência funcional, as cotas de folhas e a
caracterização das inclinações não nulas.
-/

namespace Pendencias.Marcada

open Artigo

/-- Condição que define `𝒯(S)` no TeX: nenhuma célula-folha contém uma quebra de `S`
no interior. Usa exatamente as células `J_{k,m}` enumeradas por `cellsOf`. -/
def LeavesAvoid (S : Finset ℚ) (T : DShape) (k : ℕ) (m : ℤ) : Prop :=
  ∀ J ∈ cellsOf T k m, ∀ τ ∈ S, ¬ (cL J.1 J.2 < τ ∧ (τ : ℝ) < cR J.1 J.2)

lemma leavesAvoid_leaf (S : Finset ℚ) (k : ℕ) (m : ℤ) :
    LeavesAvoid S .leaf k m ↔ ∀ τ ∈ S, ¬ (cL k m < τ ∧ (τ : ℝ) < cR k m) := by
  simp [LeavesAvoid, cellsOf]

lemma leavesAvoid_node (S : Finset ℚ) (l r : DShape) (k : ℕ) (m : ℤ) :
    LeavesAvoid S (.node l r) k m ↔
      LeavesAvoid S l (k + 1) (2 * m) ∧ LeavesAvoid S r (k + 1) (2 * m + 1) := by
  simp only [LeavesAvoid, cellsOf, List.mem_append]
  constructor
  · intro h
    exact ⟨fun J hJ => h J (Or.inl hJ), fun J hJ => h J (Or.inr hJ)⟩
  · rintro ⟨hl, hr⟩ J (hJ | hJ)
    · exact hl J hJ
    · exact hr J hJ

/-- Toda árvore cujas folhas separam as quebras refina a árvore construída por `canonShape`.
Não há hipótese de profundidade sobre a árvore candidata; a construção truncada já é
menos refinada do que qualquer separação completa das quebras. Usa a ordem
`DShape.Refines` já definida no acervo, que substitui folhas por subárvores. -/
theorem canonShape_least (S : Finset ℚ) :
    ∀ (d k : ℕ) (m : ℤ) (T : DShape), LeavesAvoid S T k m →
      DShape.Refines T (canonShape S d k m) := by
  intro d
  induction d with
  | zero => intro k m T _; cases T <;> trivial
  | succ d ih =>
      intro k m T hT
      unfold canonShape
      split_ifs with hex
      · cases T with
        | leaf =>
            obtain ⟨τ, hτ, hinside⟩ := hex
            exact False.elim ((leavesAvoid_leaf S k m).mp hT τ hτ hinside)
        | node l r =>
            obtain ⟨hl, hr⟩ := (leavesAvoid_node S l r k m).mp hT
            exact ⟨ih _ _ _ hl, ih _ _ _ hr⟩
      · cases T <;> trivial

/-- A construção é a única árvore menos refinada que separa `S`, quando `d` cobre as
profundidades diádicas das quebras. Isto certifica a minimalidade combinatória de `𝒯(S)`;
a equivalência entre separar quebras e realizar a função é uma obrigação separada. -/
theorem canonShape_unique_least (S : Finset ℚ) (d k : ℕ) (m : ℤ)
    (hdepth : ∀ τ ∈ S, τ.den ∣ 2 ^ (k + d)) :
    LeavesAvoid S (canonShape S d k m) k m ∧
      ∀ T, LeavesAvoid S T k m →
        (∀ U, LeavesAvoid S U k m → DShape.Refines U T) → T = canonShape S d k m := by
  have hcan : LeavesAvoid S (canonShape S d k m) k m :=
    canonShape_no_interior S d k m hdepth
  exact ⟨hcan, fun T hT hleast =>
    DShape.Refines.antisymm (canonShape_least S d k m T hT) (hleast _ hcan)⟩

/-- A árvore canônica não depende do limite de profundidade usado para construí-la,
desde que ambos os limites cubram as profundidades diádicas das quebras. -/
theorem canonShape_independent_depth (S : Finset ℚ) (d e k : ℕ) (m : ℤ)
    (hd : ∀ τ ∈ S, τ.den ∣ 2 ^ (k + d)) (he : ∀ τ ∈ S, τ.den ∣ 2 ^ (k + e)) :
    canonShape S d k m = canonShape S e k m := by
  exact DShape.Refines.antisymm
    (canonShape_least S e k m _ (canonShape_no_interior S d k m hd))
    (canonShape_least S d k m _ (canonShape_no_interior S e k m he))

/-- Separar as mesmas quebras exige pelo menos tantas folhas quanto a árvore canônica. -/
theorem canonShape_min_leaves (S : Finset ℚ) (d k : ℕ) (m : ℤ) (T : DShape)
    (hT : LeavesAvoid S T k m) :
    (canonShape S d k m).numLeaves ≤ T.numLeaves :=
  (canonShape_least S d k m T hT).numLeaves_le

end Pendencias.Marcada
