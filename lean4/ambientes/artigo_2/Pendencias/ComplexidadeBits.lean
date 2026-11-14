import Pendencias.ComplexidadeDensa
import RequestProject.BitComplexity

/-!
# III.9.3 — parte 1: crescimento em bits dos custos da recorrência densa
-/

namespace Pendencias.DenseDP

open Artigo Classical LTree

variable (S : Setup)

/-- `B_cost`: a cota explícita de `Setup.bit_complexity` para o comprimento em bits dos custos,
`2 (P (5B + 6⌈log₂H⌉ + 2(k₀+D) + 9) + 2B + 2⌈log₂L⌉ + 2) + 3`
`= O(P (B_𝒵 + D + k₀ + log 2H) + B_𝒵 + log 2L)`. -/
def Bcost (S : Setup) (B L : ℕ) : ℕ :=
  2 * (S.data.length * (5 * B + 6 * Nat.clog 2 S.H + 2 * (S.k₀ + S.D) + 9) +
    2 * B + 2 * Nat.clog 2 L + 2) + 3

/-- hipóteses de tamanho da instância: `B` limita `bl` de abscissas, respostas, pesos e
penalidades; `L` limita o comprimento dos fluxos das representações do catálogo (eq. stream-length). -/
structure BitHyp (S : Setup) (B L : ℕ) : Prop where
  hdata : ∀ p ∈ S.data, bl p.1 ≤ B ∧ bl p.2.1 ≤ B ∧ bl p.2.2 ≤ B
  hlb : bl S.lb ≤ B
  hls : bl S.ls ≤ B
  hL : ∀ (k r : ℕ) (m : ℤ) (R : LTree), IsDesc S.k₀ S.m₀ k m r → WF k m R →
    r + R.depth ≤ S.D → R.maxHeight ≤ S.H → (serRec R).length ≤ L

lemma isDesc_cell {r j : ℕ} (hj : j < 2 ^ r) :
    IsDesc S.k₀ S.m₀ (S.k₀ + r) (cellM S r j) r := by
  refine ⟨rfl, ?_⟩
  unfold cellM
  have hpos : (2 : ℤ) ^ r ≠ 0 := by positivity
  rw [add_comm, Int.add_mul_ediv_right _ _ hpos]
  have : (j : ℤ) / 2 ^ r = 0 := Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast hj)
  rw [this, zero_add]

lemma inf_costW_attained (s : Finset LTree) (q : ℚ) (h : s.inf S.costW = (q : WithTop ℚ)) :
    ∃ R ∈ s, S.costT R = q := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp at h
  · obtain ⟨R, hR, hmin⟩ := s.exists_min_image S.costW hne
    have heq : s.inf S.costW = S.costW R := le_antisymm (Finset.inf_le hR) (Finset.le_inf hmin)
    rw [heq] at h
    refine ⟨R, hR, ?_⟩
    unfold Setup.costW at h
    exact_mod_cast h

lemma costT_bits {B L : ℕ} (hb : BitHyp S B L) {d r j : ℕ} {u v : ℚ} {R : LTree}
    (hj : j < 2 ^ r) (hrd : r + d ≤ S.D) (hR : R ∈ S.Rset d (S.k₀ + r) (cellM S r j) u v) :
    bl (S.costT R) ≤ Bcost S B L := by
  obtain ⟨hdep, hh, hW, -, -⟩ := (S.mem_Rset).mp hR
  have hd := isDesc_cell S hj
  exact S.bit_complexity hb.hdata hb.hlb hb.hls hd hW (by omega) hh
    (hb.hL _ _ _ R hd hW (by omega) hh)

/-- **Crescimento em bits (árvore variável)**: todo valor finito `C_d(J;u,v)` da recorrência tem
`bl ≤ B_cost`. -/
theorem Cvar_bits (hH : 2 ≤ S.H) {B L : ℕ} (hb : BitHyp S B L) (d r j : ℕ) (u v : ℚ)
    (hj : j < 2 ^ r) (hrd : r + d ≤ S.D) (q : ℚ)
    (hq : S.Cvar d (S.k₀ + r) (cellM S r j) u v = (q : WithTop ℚ)) : bl q ≤ Bcost S B L := by
  rw [S.variable_correctness hH d (S.k₀ + r) r (cellM S r j) u v (isDesc_cell S hj) hrd] at hq
  obtain ⟨R, hR, rfl⟩ := inf_costW_attained S _ q hq
  exact costT_bits S hb hj hrd hR

/-- **Crescimento em bits (orçamento)**: todo valor finito `C_{d,n}(J;u,v)` tem `bl ≤ B_cost`. -/
theorem Cb_bits (hH : 2 ≤ S.H) {B L : ℕ} (hb : BitHyp S B L) (d n r j : ℕ) (u v : ℚ)
    (hj : j < 2 ^ r) (hrd : r + d ≤ S.D) (q : ℚ)
    (hq : S.Cb d n (S.k₀ + r) (cellM S r j) u v = (q : WithTop ℚ)) : bl q ≤ Bcost S B L := by
  rw [S.leaf_budget hH d n (S.k₀ + r) r (cellM S r j) u v (isDesc_cell S hj) hrd] at hq
  obtain ⟨R, hR, rfl⟩ := inf_costW_attained S _ q hq
  exact costT_bits S hb hj hrd ((S.mem_RsetN).mp hR).1

/-- soma de dois racionais de `≤ b` bits tem `≤ 4b + 5` bits -/
lemma bl_add_le {x y : ℚ} {b : ℕ} (hx : bl x ≤ b) (hy : bl y ≤ b) : bl (x + y) ≤ 4 * b + 5 := by
  have := bl_le_of_QB (((QB_of_bl x).mono hx).add ((QB_of_bl y).mono hy))
  omega


lemma B_le_Bcost (B L : ℕ) : B ≤ Bcost S B L := by unfold Bcost; omega

/-- **Operandos de um candidato**: se os custos dos filhos têm `≤ B_cost` bits, a soma
`c_L + c_R` tem `≤ 4 B_cost + 5` bits e o candidato com penalidade
`λ_bits + λ_split + c_L + c_R` tem `≤ 16 B_cost + 25` bits. -/
theorem candidate_bits {B L : ℕ} (hb : BitHyp S B L) {q1 q2 : ℚ}
    (h1 : bl q1 ≤ Bcost S B L) (h2 : bl q2 ≤ Bcost S B L) :
    bl (q1 + q2) ≤ 4 * Bcost S B L + 5 ∧
      bl (S.lb + S.ls + (q1 + q2)) ≤ 16 * Bcost S B L + 25 := by
  have hs := bl_add_le h1 h2
  have hB := B_le_Bcost S B L
  have hpen : bl (S.lb + S.ls) ≤ 4 * Bcost S B L + 5 :=
    (bl_add_le hb.hlb hb.hls).trans (by omega)
  exact ⟨hs, (bl_add_le hpen hs).trans (by omega)⟩

/-- **Somas parciais da perda local** (inicialização direta): para um átomo admissível de uma
célula do catálogo, toda soma parcial sobre um trecho dos dados — os acumuladores de `lossTm`,
por `lossTm_val` — tem `≤ B_cost` bits. -/
theorem partial_loss_bits {B L : ℕ} (hb : BitHyp S B L) (a : Atom) (ha : a.height ≤ S.H)
    (hak : a.k ≤ S.k₀ + S.D) (ps : List (ℚ × ℚ × ℚ)) (hps : ∀ p ∈ ps, p ∈ S.data)
    (hlen : ps.length ≤ S.data.length) :
    bl (((ps.filter fun p => S.owns a.k a.m p.1).map fun p =>
      p.2.2 * (p.2.1 - lineJ a.k a.m a.lval a.rval p.1) ^ 2).sum) ≤ Bcost S B L := by
  set eT := 5 * B + 6 * Nat.clog 2 S.H + 2 * (S.k₀ + S.D) + 8 with heT
  set l' := ps.filter fun p => S.owns a.k a.m p.1 with hl'
  have hterm : ∀ p ∈ l', QB eT (p.2.2 * (p.2.1 - lineJ a.k a.m a.lval a.rval p.1) ^ 2) := by
    intro p hp
    have hpd : p ∈ S.data := hps p (List.mem_filter.mp hp).1
    obtain ⟨h1, h2, h3⟩ := hb.hdata p hpd
    exact (QB_term ha ((QB_of_bl _).mono h1) ((QB_of_bl _).mono h2) ((QB_of_bl _).mono h3)).mono
      (by omega)
  have hlen' : l'.length ≤ S.data.length := (List.length_filter_le _ _).trans hlen
  have hQ := (QB_sum _ l' hterm).mono (Nat.mul_le_mul_right (eT + 1) hlen')
  have := bl_le_of_QB hQ
  refine this.trans ?_
  have e : eT + 1 = 5 * B + 6 * Nat.clog 2 S.H + 2 * (S.k₀ + S.D) + 9 := rfl
  rw [e]
  unfold Bcost
  omega

/-- **Acumuladores de `lossTm`**: numa célula admissível `(u,v) ∈ 𝒫_H(J_{k,m})` do catálogo
(`k ≤ k₀ + D`), o acumulador após qualquer trecho `ps` dos dados — valor de `lossTm` partindo de
`0` — tem `≤ B_cost` bits. -/
theorem lossTm_acc_bits {B L : ℕ} (hb : BitHyp S B L) (hH : 2 ≤ S.H) (k : ℕ) (m : ℤ) (u v : ℚ)
    (hp : (u, v) ∈ PH S.H k m) (hk : k ≤ S.k₀ + S.D) (ps : List (ℚ × ℚ × ℚ))
    (hps : ∀ p ∈ ps, p ∈ S.data) (hlen : ps.length ≤ S.data.length) :
    bl ((lossTm S k m u v ps 0).val) ≤ Bcost S B L := by
  obtain ⟨b, ⟨hbh, hbk, hbm⟩, hbuv⟩ := (endpoint_dictionary hH).1.2.2 (Finset.mem_coe.mpr hp)
  simp only [Prod.mk.injEq] at hbuv
  obtain ⟨rfl, rfl⟩ := hbuv
  subst hbk hbm
  rw [lossTm_val, zero_add]
  exact partial_loss_bits S hb b hbh hk ps hps hlen

/-! ## Modelo de custo em bits -/

/-- Modelo de custo em bits (hipótese do TeX, "algoritmos inteiros usuais"): `MZ b` limita a
multiplicação de inteiros de `b` bits; `arith b` é o custo de uma soma, comparação ou redução
de frações com operandos de até `b` bits, suposto `≤ cA · MZ(b) · ⌈log₂(2b)⌉`. Estas cotas são
hipóteses do modelo, não demonstradas em Lean (não há modelo de máquina). -/
structure BitModel where
  MZ : ℕ → ℕ
  arith : ℕ → ℕ
  cA : ℕ
  arith_le : ∀ b, arith b ≤ cA * (MZ b * Nat.clog 2 (2 * b))

/-- bits de uma entrada armazenada: custo (`b`), fluxo ou apontador (`L`) e índices (`idx`) -/
def entryBits (b L idx : ℕ) : ℕ := b + L + idx

/-- cota do custo em bits de UMA operação unitária da execução densa, com operandos de até `b`
bits: aritmética racional (`arith b`), comparação shortlex de empate (`L`) e acesso a uma
entrada da memória (`entryBits`). -/
def opBits (bm : BitModel) (b L idx : ℕ) : ℕ := bm.arith b + L + entryBits b L idx

lemma opBits_le (bm : BitModel) (b L idx : ℕ) :
    opBits bm b L idx ≤ bm.cA * (bm.MZ b * Nat.clog 2 (2 * b)) + 2 * L + b + idx := by
  unfold opBits entryBits
  have := bm.arith_le b
  omega

/-- multiplicação escolar: `MZ(b) = b²` -/
def schoolModel (cA : ℕ) : BitModel :=
  ⟨fun b => b ^ 2, fun b => cA * (b ^ 2 * Nat.clog 2 (2 * b)), cA, fun _ => le_rfl⟩

/-- índices de uma posição: `⌈log₂(S_D M + 1)⌉` bits -/
noncomputable def idxBits (S : Setup) : ℕ := Nat.clog 2 ((2 ^ (S.D + 1) - 1) * S.V.card + 1)

/-- **Teorema III.9.3 (cota grosseira de complexidade de bits)** — enunciado formal reunido.
Seja `B_cost = Bcost S B L` e `b = 16 B_cost + 25` (cota de todos os operandos: entradas,
somas de candidatos, candidatos com penalidade e somas parciais da perda).
1. *Crescimento*: todo custo finito `Cvar`/`Cb` da recorrência tem `bl ≤ B_cost`.
2. *Tempo em bits* (cada operação unitária de III.9.1 custa no máximo `opBits bm b L idx`):
   sem orçamento, com custos locais calculados sobre `P` observações,
   `≤ (S_D M² (4M+6) + 4 S_D P M²) · opBits`; com orçamento `N`,
   `≤ (S_D M² (4P+3) + S_D M² N (4NM+2)) · opBits`; e
   `opBits ≤ cA · MZ(b) ⌈log₂ 2b⌉ + 2L + b + idx`.
3. *Memória em bits*: `S_D M² · (B_cost + L + idx)`, resp. `S_D N M² · (B_cost + L + idx)`. -/
theorem bit_complexity_dense (hH : 2 ≤ S.H) {B L : ℕ} (hb : BitHyp S B L) (bm : BitModel)
    (N : ℕ) :
    -- 1. crescimento
    (∀ r j u v, r ≤ S.D → j < 2 ^ r → u ∈ S.V → v ∈ S.V → ∀ q : ℚ,
      ((denseRun S (leafInit S)).val.tab (r, j, u, v)).1 = (q : WithTop ℚ) →
        bl q ≤ Bcost S B L) ∧
    (∀ r j u v n, r ≤ S.D → j < 2 ^ r → u ∈ S.V → v ∈ S.V → 1 ≤ n → n ≤ N → ∀ q : ℚ,
      ((denseRunB S N (leafInit S)).val.tab (r, j, u, v, n)).1 = (q : WithTop ℚ) →
        bl q ≤ Bcost S B L) ∧
    -- 2. tempo em bits
    ((denseRun S (leafInit S)).ticks * opBits bm (16 * Bcost S B L + 25) L (idxBits S) ≤
      ((2 ^ (S.D + 1) - 1) * S.V.card ^ 2 * (4 * S.V.card + 6) +
        4 * ((2 ^ (S.D + 1) - 1) * S.data.length * S.V.card ^ 2)) *
        opBits bm (16 * Bcost S B L + 25) L (idxBits S)) ∧
    ((denseRunB S N (leafInit S)).ticks * opBits bm (16 * Bcost S B L + 25) L (idxBits S) ≤
      ((2 ^ (S.D + 1) - 1) * ((4 * S.data.length + 3) * S.V.card ^ 2) +
        (2 ^ (S.D + 1) - 1) * (S.V.card ^ 2 * N * (4 * (N * S.V.card) + 2))) *
        opBits bm (16 * Bcost S B L + 25) L (idxBits S)) ∧
    (opBits bm (16 * Bcost S B L + 25) L (idxBits S) ≤
      bm.cA * (bm.MZ (16 * Bcost S B L + 25) * Nat.clog 2 (2 * (16 * Bcost S B L + 25))) +
        2 * L + (16 * Bcost S B L + 25) + idxBits S) ∧
    -- 3. memória em bits
    ((denseRun S (leafInit S)).val.dom.card * entryBits (Bcost S B L) L (idxBits S) =
      (2 ^ (S.D + 1) - 1) * S.V.card ^ 2 * (Bcost S B L + L + idxBits S)) ∧
    ((denseRunB S N (leafInit S)).val.dom.card * entryBits (Bcost S B L) L (idxBits S) =
      (2 ^ (S.D + 1) - 1) * N * S.V.card ^ 2 * (Bcost S B L + L + idxBits S)) := by
  obtain ⟨a1, a2, a3, -⟩ := dense_variable_init S hH
  obtain ⟨b1, b2, b3, -⟩ := dense_budget_init S hH N
  refine ⟨?_, ?_, Nat.mul_le_mul_right _ a3, Nat.mul_le_mul_right _ b3, opBits_le _ _ _ _, ?_, ?_⟩
  · intro r j u v hr hj hu hv q hq
    rw [a1 r j u v hr hj hu hv] at hq
    exact Cvar_bits S hH hb (S.D - r) r j u v hj (by omega) q hq
  · intro r j u v n hr hj hu hv hn1 hn2 q hq
    rw [b1 r j u v n hr hj hu hv hn1 hn2] at hq
    exact Cb_bits S hH hb (S.D - r) n r j u v hj (by omega) q hq
  · rw [a2]; rfl
  · rw [b2]; rfl

end Pendencias.DenseDP
