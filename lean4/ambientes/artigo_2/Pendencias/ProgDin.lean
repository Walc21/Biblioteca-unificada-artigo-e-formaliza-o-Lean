import RequestProject.DP
import RequestProject.Budgets

/-!
# III.6.3 (rotulação exata de uma árvore fixa) e III.7.4 (seletor exato por programação
dinâmica) — programas e suas provas

Para cada estado `(u, v)` a tabela guarda o candidato de menor chave total `κ` (eq. tie-key:
custo, depois o fluxo `ser_rec` em shortlex); os candidatos de um nó interno são as colagens
`node l r` das entradas dos filhos com o mesmo valor intermediário `w`; a entrada só é substituída
quando a chave completa diminui (`kselect`). Guardar a árvore ótima de cada entrada equivale a
guardar os apontadores para os dois filhos.

* `fixTable`, `fixRoot` (III.6.3) e `varTable`, `varRoot` (III.7.4);
* cada entrada é o `κ`-mínimo de `𝔑_H(T_J;u,v)` (resp. `𝔑_{d,H}(J;u,v)`), vazia exatamente
  quando o conjunto é vazio (`fixTable_spec`, `varTable_spec`), graças ao Lema 5.2
  (`tie_concatenation`);
* o custo da entrada é `C_T(J;u,v)` (resp. `C_d(J;u,v)`) (`fixTable_cost`, `varTable_cost`);
* a raiz devolve a única representação `κ`-mínima de `fixed_global` / `variable_global`
  (`fixRoot_spec`, `varRoot_spec`), cujo custo é o ótimo global.
-/

namespace Pendencias

open Artigo LTree

namespace DPprog

variable (S : Setup)

/-! ## Seleção pela chave `κ` -/

def kbest (a b : LTree) : LTree := if S.kappa a ≤ S.kappa b then a else b

lemma kappa_kbest (a b : LTree) : S.kappa (kbest S a b) = min (S.kappa a) (S.kappa b) := by
  unfold kbest
  split_ifs with h
  · exact (min_eq_left h).symm
  · exact (min_eq_right (le_of_not_ge h)).symm

lemma kbest_mem (a b : LTree) : kbest S a b = a ∨ kbest S a b = b := by
  unfold kbest; split_ifs <;> simp

def okbest : Option LTree → Option LTree → Option LTree
  | none, x => x
  | x, none => x
  | some a, some b => some (kbest S a b)

instance : Std.Commutative (okbest S) where
  comm x y := by
    rcases x with _ | a <;> rcases y with _ | b <;> simp only [okbest]
    exact congrArg some (S.kappa_injective (by rw [kappa_kbest, kappa_kbest, min_comm]))

instance : Std.Associative (okbest S) where
  assoc x y z := by
    rcases x with _ | a <;> rcases y with _ | b <;> rcases z with _ | c <;> simp only [okbest]
    exact congrArg some (S.kappa_injective (by simp only [kappa_kbest, min_assoc]))

/-- a entrada de menor chave `κ` de um conjunto finito de candidatos -/
def kselect (s : Finset LTree) : Option LTree := s.fold (okbest S) none some

lemma kselect_empty : kselect S ∅ = none := by simp [kselect]

lemma kselect_spec : ∀ s : Finset LTree, s.Nonempty →
    ∃ R, kselect S s = some R ∧ R ∈ s ∧ ∀ R' ∈ s, S.kappa R ≤ S.kappa R' := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro h; exact absurd h Finset.not_nonempty_empty
  | insert a s ha ih =>
      intro _
      unfold kselect
      rw [Finset.fold_insert ha]
      rcases s.eq_empty_or_nonempty with rfl | hs
      · refine ⟨a, by simp [okbest], Finset.mem_insert_self a ∅, fun R' hR' => ?_⟩
        simp at hR'; rw [hR']
      · obtain ⟨R0, h0, hR0, hmin⟩ := ih hs
        unfold kselect at h0
        rw [h0]
        refine ⟨kbest S a R0, rfl, ?_, fun R' hR' => ?_⟩
        · rcases kbest_mem S a R0 with h | h <;> rw [h]
          · exact Finset.mem_insert_self a s
          · exact Finset.mem_insert_of_mem hR0
        · rw [kappa_kbest]
          rcases Finset.mem_insert.mp hR' with rfl | hR'
          · exact min_le_left _ _
          · exact (min_le_right _ _).trans (hmin R' hR')

lemma kselect_eq_none_iff (s : Finset LTree) : kselect S s = none ↔ s = ∅ := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨R, hR, -⟩ := kselect_spec S s (Finset.nonempty_iff_ne_empty.mpr hne)
    rw [h] at hR; cases hR
  · rintro rfl; exact kselect_empty S

lemma costW_le_of_kappa {R R' : LTree} (h : S.kappa R ≤ S.kappa R') : S.costW R ≤ S.costW R' := by
  simp only [Setup.kappa, Prod.Lex.toLex_le_toLex] at h
  unfold Setup.costW
  rcases h with h | ⟨h, -⟩
  · exact_mod_cast h.le
  · rw [h]

/-- especificação comum de uma entrada de tabela -/
def IsEntry (o : Option LTree) (s : Finset LTree) : Prop :=
  (o = none ↔ s = ∅) ∧ ∀ R, o = some R → R ∈ s ∧ ∀ R' ∈ s, S.kappa R ≤ S.kappa R'

lemma isEntry_kselect (s : Finset LTree) : IsEntry S (kselect S s) s := by
  refine ⟨kselect_eq_none_iff S s, fun R hR => ?_⟩
  obtain ⟨R0, h0, hR0, hmin⟩ := kselect_spec S s (Finset.nonempty_iff_ne_empty.mpr (by
    intro he; rw [he, kselect_empty] at hR; cases hR))
  rw [hR] at h0; cases h0
  exact ⟨hR0, hmin⟩

/-- custo de uma entrada (`+∞` se vazia) -/
def entryCost (o : Option LTree) : WithTop ℚ := o.elim ⊤ S.costW

lemma entryCost_eq {o : Option LTree} {s : Finset LTree} (h : IsEntry S o s) :
    entryCost S o = s.inf S.costW := by
  rcases o with _ | R
  · rw [h.1.mp rfl]; rfl
  · obtain ⟨hR, hmin⟩ := h.2 R rfl
    exact le_antisymm (Finset.le_inf fun R' hR' => costW_le_of_kappa S (hmin R' hR')) (Finset.inf_le hR)

/-- candidatos de colagem pelo valor intermediário `w` -/
noncomputable def glue (oL oR : ℚ → Option LTree) : Finset LTree :=
  S.V.biUnion fun w => ((oL w).toFinset ×ˢ (oR w).toFinset).image fun p => node p.1 p.2

/-- colar entradas ótimas dá uma entrada ótima da colagem dos conjuntos (Lema 5.2) -/
lemma isEntry_glue {oL oR : ℚ → Option LTree} {sL sR : ℚ → Finset LTree}
    (hL : ∀ w, IsEntry S (oL w) (sL w)) (hR : ∀ w, IsEntry S (oR w) (sR w)) :
    IsEntry S (kselect S (glue S oL oR))
      (S.V.biUnion fun w => (sL w ×ˢ sR w).image fun p => node p.1 p.2) := by
  classical
  have hsub : glue S oL oR ⊆ S.V.biUnion fun w => (sL w ×ˢ sR w).image fun p => node p.1 p.2 := by
    intro R hR
    simp only [glue, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product,
      Option.mem_toFinset, Option.mem_def, Prod.exists] at hR ⊢
    obtain ⟨w, hw, l, r, ⟨hl, hr⟩, rfl⟩ := hR
    exact ⟨w, hw, l, r, ⟨((hL w).2 l hl).1, ((hR w).2 r hr).1⟩, rfl⟩
  -- todo candidato do conjunto completo é dominado por um candidato da colagem
  have hdom : ∀ R' ∈ S.V.biUnion (fun w => (sL w ×ˢ sR w).image fun p => node p.1 p.2),
      ∃ R ∈ glue S oL oR, S.kappa R ≤ S.kappa R' := by
    intro R' hR'
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_product, Prod.exists] at hR'
    obtain ⟨w, hw, l', r', ⟨hl', hr'⟩, rfl⟩ := hR'
    obtain ⟨l, hl⟩ := Option.ne_none_iff_exists'.mp (fun h =>
      Finset.notMem_empty l' ((hL w).1.mp h ▸ hl'))
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp (fun h =>
      Finset.notMem_empty r' ((hR w).1.mp h ▸ hr'))
    refine ⟨node l r, ?_, tie_concatenation S (((hL w).2 l hl).2 l' hl') (((hR w).2 r hr).2 r' hr')⟩
    simp only [glue, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product,
      Option.mem_toFinset, Option.mem_def, Prod.exists]
    exact ⟨w, hw, l, r, ⟨hl, hr⟩, rfl⟩
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun R hR => ?_⟩
  · rw [kselect_eq_none_iff] at h
    rw [Finset.eq_empty_iff_forall_notMem]
    intro R' hR'
    obtain ⟨R, hR, -⟩ := hdom R' hR'
    rw [h] at hR; exact Finset.notMem_empty R hR
  · rw [kselect_eq_none_iff]
    exact Finset.subset_empty.mp (h ▸ hsub)
  · obtain ⟨hRs, hmin⟩ := (isEntry_kselect S _).2 R hR
    refine ⟨hsub hRs, fun R' hR' => ?_⟩
    obtain ⟨R0, hR0, hk⟩ := hdom R' hR'
    exact (hmin R0 hR0).trans hk

/-! ## III.6.3 — árvore fixa -/

/-- tabela da rotulação exata da forma fixa `T` em `J_{k,m}` para o estado `(u,v)` -/
noncomputable def fixTable : Setup.Shape → ℕ → ℤ → ℚ → ℚ → Option LTree
  | .leaf, k, m, u, v => kselect S (S.Rset 0 k m u v)
  | .node TL TR, k, m, u, v =>
      kselect S (glue S (fun w => fixTable TL (k + 1) (2 * m) u w)
        (fun w => fixTable TR (k + 1) (2 * m + 1) w v))

theorem fixTable_spec (hH : 2 ≤ S.H) : ∀ (T : Setup.Shape) (k r : ℕ) (m : ℤ) (u v : ℚ),
    IsDesc S.k₀ S.m₀ k m r → r + T.depth ≤ S.D →
      IsEntry S (fixTable S T k m u v) (S.RsetS T k m u v) := by
  intro T
  induction T with
  | leaf => intro k r m u v _ _; rw [S.RsetS_leaf]; exact isEntry_kselect S _
  | node TL TR ihl ihr =>
      intro k r m u v hd hdD
      rw [S.RsetS_node hH hd hdD]
      simp only [Setup.Shape.depth] at hdD
      exact isEntry_glue S (fun w => ihl _ _ _ u w hd.left (by omega))
        (fun w => ihr _ _ _ w v hd.right (by omega))

/-- **III.6.3**: o custo da entrada é `C_T(J;u,v)` -/
theorem fixTable_cost (hH : 2 ≤ S.H) (T : Setup.Shape) {k r : ℕ} {m : ℤ} (u v : ℚ)
    (hd : IsDesc S.k₀ S.m₀ k m r) (hdD : r + T.depth ≤ S.D) :
    entryCost S (fixTable S T k m u v) = S.Cfix T k m u v := by
  rw [entryCost_eq S (fixTable_spec S hH T k r m u v hd hdD), S.fixed_correctness hH T k r m u v hd hdD]

/-- raiz: menor entrada finita sobre os estados `(u,v)` -/
noncomputable def fixRoot (T : Setup.Shape) : Option LTree :=
  kselect S ((S.V ×ˢ S.V).biUnion fun p => (fixTable S T S.k₀ S.m₀ p.1 p.2).toFinset)

lemma RepShape_eq (hH : 2 ≤ S.H) (T : Setup.Shape) (hT : T.depth ≤ S.D) :
    S.RepShape T = (S.V ×ˢ S.V).biUnion fun p => S.RsetS T S.k₀ S.m₀ p.1 p.2 := by
  classical
  ext R
  simp only [Setup.RepShape, Finset.mem_filter, mem_RepCat, Finset.mem_biUnion, Finset.mem_product,
    Prod.exists, Setup.mem_RsetS]
  constructor
  · rintro ⟨⟨hW, hd, hh⟩, hs⟩
    have := rootvals_mem (D := S.D) hH (IsDesc.root S.k₀ S.m₀) hW (by omega) hh
    exact ⟨R.lval, R.rval, ⟨this.1, this.2⟩, hs, hh, hW, rfl, rfl⟩
  · rintro ⟨u, v, -, hs, hh, hW, -, -⟩
    exact ⟨⟨hW, by rw [← Setup.depth_shapeOf, hs]; exact hT, hh⟩, hs⟩

/-- raiz de uma união de entradas ótimas -/
lemma isEntry_root {ι : Type*} [DecidableEq ι] (I : Finset ι) {o : ι → Option LTree}
    {s : ι → Finset LTree} (h : ∀ i ∈ I, IsEntry S (o i) (s i)) :
    IsEntry S (kselect S (I.biUnion fun i => (o i).toFinset)) (I.biUnion s) := by
  classical
  have hsub : I.biUnion (fun i => (o i).toFinset) ⊆ I.biUnion s := by
    intro R hR
    simp only [Finset.mem_biUnion, Option.mem_toFinset, Option.mem_def] at hR ⊢
    obtain ⟨i, hi, hR⟩ := hR
    exact ⟨i, hi, ((h i hi).2 R hR).1⟩
  have hdom : ∀ R' ∈ I.biUnion s, ∃ R ∈ I.biUnion (fun i => (o i).toFinset),
      S.kappa R ≤ S.kappa R' := by
    intro R' hR'
    obtain ⟨i, hi, hR'⟩ := Finset.mem_biUnion.mp hR'
    obtain ⟨R, hR⟩ := Option.ne_none_iff_exists'.mp (fun hn =>
      Finset.notMem_empty R' ((h i hi).1.mp hn ▸ hR'))
    exact ⟨R, Finset.mem_biUnion.mpr ⟨i, hi, by simp [hR]⟩, ((h i hi).2 R hR).2 R' hR'⟩
  refine ⟨⟨fun hn => ?_, fun he => ?_⟩, fun R hR => ?_⟩
  · rw [kselect_eq_none_iff] at hn
    rw [Finset.eq_empty_iff_forall_notMem]
    intro R' hR'
    obtain ⟨R, hR, -⟩ := hdom R' hR'
    rw [hn] at hR; exact Finset.notMem_empty R hR
  · rw [kselect_eq_none_iff]; exact Finset.subset_empty.mp (he ▸ hsub)
  · obtain ⟨hRs, hmin⟩ := (isEntry_kselect S _).2 R hR
    refine ⟨hsub hRs, fun R' hR' => ?_⟩
    obtain ⟨R0, hR0, hk⟩ := hdom R' hR'
    exact (hmin R0 hR0).trans hk

/-- **Algoritmo III.6.3 (correção)**: a raiz devolve a única rotulação `κ`-mínima de `T`
(a de `fixed_global`), com custo igual a `min_{u,v} C_T(K;u,v)`; devolve `none` exatamente
quando `T` não admite rotulação. -/
theorem fixRoot_spec (hH : 2 ≤ S.H) (T : Setup.Shape) (hT : T.depth ≤ S.D) :
    (fixRoot S T = none ↔ S.RepShape T = ∅) ∧
    ∀ R, fixRoot S T = some R →
      R ∈ S.RepShape T ∧ (∀ R' ∈ S.RepShape T, S.kappa R ≤ S.kappa R') ∧
      S.costW R = (S.V ×ˢ S.V).inf (fun p => S.Cfix T S.k₀ S.m₀ p.1 p.2) := by
  classical
  have h := isEntry_root S (S.V ×ˢ S.V) (s := fun p => S.RsetS T S.k₀ S.m₀ p.1 p.2)
    (fun p _ => fixTable_spec S hH T S.k₀ 0 S.m₀ p.1 p.2 (IsDesc.root _ _) (by omega))
  rw [← RepShape_eq S hH T hT] at h
  refine ⟨h.1, fun R hR => ⟨(h.2 R hR).1, (h.2 R hR).2, ?_⟩⟩
  rw [(S.fixed_global hH T hT).1, ← entryCost_eq S h]
  unfold fixRoot at hR
  rw [hR]; rfl

/-! ## III.7.4 — seletor sobre a árvore diádica completa -/

/-- tabela `C_d(J;u,v)` com o candidato folha e as colagens pelo valor intermediário -/
noncomputable def varTable : ℕ → ℕ → ℤ → ℚ → ℚ → Option LTree
  | 0, k, m, u, v => kselect S (S.Rset 0 k m u v)
  | d + 1, k, m, u, v =>
      kselect S (S.Rset 0 k m u v ∪ glue S (fun w => varTable d (k + 1) (2 * m) u w)
        (fun w => varTable d (k + 1) (2 * m + 1) w v))

theorem varTable_spec (hH : 2 ≤ S.H) : ∀ (d k r : ℕ) (m : ℤ) (u v : ℚ),
    IsDesc S.k₀ S.m₀ k m r → r + d ≤ S.D →
      IsEntry S (varTable S d k m u v) (S.Rset d k m u v) := by
  classical
  intro d
  induction d with
  | zero => intro k r m u v _ _; exact isEntry_kselect S _
  | succ d ih =>
      intro k r m u v hd hdD
      rw [S.Rset_succ hH hd hdD, varTable]
      have hg := isEntry_glue S (fun w => ih _ _ _ u w hd.left (by omega))
        (fun w => ih _ _ _ w v hd.right (by omega))
      set G := glue S (fun w => varTable S d (k + 1) (2 * m) u w)
        (fun w => varTable S d (k + 1) (2 * m + 1) w v)
      set B := S.V.biUnion fun w =>
        (S.Rset d (k + 1) (2 * m) u w ×ˢ S.Rset d (k + 1) (2 * m + 1) w v).image fun p => node p.1 p.2
      have hGB : G ⊆ B := by
        intro R hR
        have hne : kselect S G ≠ none := by
          rw [Ne, kselect_eq_none_iff]; exact Finset.ne_empty_of_mem hR
        -- todo candidato de `G` é uma colagem de entradas, logo está em `B`
        simp only [G, glue, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product,
          Option.mem_toFinset, Option.mem_def, Prod.exists] at hR
        obtain ⟨w, hw, l, r', ⟨hl, hr⟩, rfl⟩ := hR
        simp only [B, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product, Prod.exists]
        exact ⟨w, hw, l, r', ⟨((ih _ _ _ u w hd.left (by omega)).2 l hl).1,
          ((ih _ _ _ w v hd.right (by omega)).2 r' hr).1⟩, rfl⟩
      have hdomB : ∀ R' ∈ B, ∃ R ∈ G, S.kappa R ≤ S.kappa R' := by
        intro R' hR'
        obtain ⟨R, hR⟩ := Option.ne_none_iff_exists'.mp (fun hn =>
          Finset.notMem_empty R' (hg.1.mp hn ▸ hR'))
        exact ⟨R, ((isEntry_kselect S G).2 R hR).1, (hg.2 R hR).2 R' hR'⟩
      refine ⟨⟨fun hn => ?_, fun he => ?_⟩, fun R hR => ?_⟩
      · rw [kselect_eq_none_iff, Finset.union_eq_empty] at hn
        rw [Finset.union_eq_empty]
        refine ⟨hn.1, Finset.eq_empty_iff_forall_notMem.mpr fun R' hR' => ?_⟩
        obtain ⟨R, hR, -⟩ := hdomB R' hR'
        rw [hn.2] at hR; exact Finset.notMem_empty R hR
      · rw [Finset.union_eq_empty] at he
        rw [kselect_eq_none_iff, Finset.union_eq_empty]
        exact ⟨he.1, Finset.subset_empty.mp (he.2 ▸ hGB)⟩
      · obtain ⟨hRs, hmin⟩ := (isEntry_kselect S _).2 R hR
        refine ⟨Finset.union_subset_union subset_rfl hGB hRs, fun R' hR' => ?_⟩
        rcases Finset.mem_union.mp hR' with h0 | hB
        · exact hmin R' (Finset.mem_union_left _ h0)
        · obtain ⟨R0, hR0, hk⟩ := hdomB R' hB
          exact (hmin R0 (Finset.mem_union_right _ hR0)).trans hk

/-- **III.7.4**: o custo da entrada é `C_d(J;u,v)` -/
theorem varTable_cost (hH : 2 ≤ S.H) (d : ℕ) {k r : ℕ} {m : ℤ} (u v : ℚ)
    (hd : IsDesc S.k₀ S.m₀ k m r) (hdD : r + d ≤ S.D) :
    entryCost S (varTable S d k m u v) = S.Cvar d k m u v := by
  rw [entryCost_eq S (varTable_spec S hH d k r m u v hd hdD), S.variable_correctness hH d k r m u v hd hdD]

/-- raiz do seletor -/
noncomputable def varRoot : Option LTree :=
  kselect S ((S.V ×ˢ S.V).biUnion fun p => (varTable S S.D S.k₀ S.m₀ p.1 p.2).toFinset)

lemma RepCat_eq (hH : 2 ≤ S.H) :
    RepCat S.H S.D S.k₀ S.m₀ = (S.V ×ˢ S.V).biUnion fun p => S.Rset S.D S.k₀ S.m₀ p.1 p.2 := by
  classical
  ext R
  simp only [mem_RepCat, Finset.mem_biUnion, Finset.mem_product, Prod.exists, Setup.mem_Rset]
  constructor
  · rintro ⟨hW, hd, hh⟩
    have := rootvals_mem (D := S.D) hH (IsDesc.root S.k₀ S.m₀) hW (by omega) hh
    exact ⟨R.lval, R.rval, ⟨this.1, this.2⟩, hd, hh, hW, rfl, rfl⟩
  · rintro ⟨u, v, -, hd, hh, hW, -, -⟩
    exact ⟨hW, hd, hh⟩

/-- **Algoritmo III.7.4 (correção)**: a raiz devolve o ótimo global `C⋆_{D,H}(K)` e a única
representação `κ`-mínima de `variable_global` (independente da ordem de enumeração). -/
theorem varRoot_spec (hH : 2 ≤ S.H) :
    (varRoot S = none ↔ RepCat S.H S.D S.k₀ S.m₀ = ∅) ∧
    ∀ R, varRoot S = some R →
      R ∈ RepCat S.H S.D S.k₀ S.m₀ ∧ (∀ R' ∈ RepCat S.H S.D S.k₀ S.m₀, S.kappa R ≤ S.kappa R') ∧
      S.costW R = S.Cstar := by
  classical
  have h := isEntry_root S (S.V ×ˢ S.V) (s := fun p => S.Rset S.D S.k₀ S.m₀ p.1 p.2)
    (fun p _ => varTable_spec S hH S.D S.k₀ 0 S.m₀ p.1 p.2 (IsDesc.root _ _) (by omega))
  rw [← RepCat_eq S hH] at h
  refine ⟨h.1, fun R hR => ⟨(h.2 R hR).1, (h.2 R hR).2, ?_⟩⟩
  rw [(S.variable_global hH).1, ← entryCost_eq S h]
  unfold varRoot at hR
  rw [hR]; rfl

end DPprog

end Pendencias
