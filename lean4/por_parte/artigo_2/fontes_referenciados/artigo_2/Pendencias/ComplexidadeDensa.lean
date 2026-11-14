import RequestProject.Complexity
import Mathlib

/-!
# III.9.1 — complexidade em número de estados (`map:artigo_2:9.1`)

Implementação densa da recorrência `Cvar` (árvore variável, III.7.1) e da recorrência com
orçamento de folhas `Cb` (III.8.1), com **modelo de custo explícito** e **memória explícita**.

* `Tm α`: computação com contador de operações unitárias; `Mem κ E`: memória densa (leitura e
  escrita em tempo unitário) com o conjunto `dom` das posições escritas; o número de entradas
  usadas é `dom.card`.
* `fillList`/`runFrom` (motor genérico): preenchimento ascendente por níveis `D, D-1, …, 0`; o
  teorema `runFrom_spec` prova, por indução nos níveis, que a tabela coincide com a especificação
  e que o número de operações é a soma dos custos das entradas escritas.
* Árvore variável: `entryTm`/`denseRun` (cada entrada varre os `M` valores intermediários: 2
  leituras, 1 soma e 1 comparação por candidato; mais penalidade e comparação com a folha);
  `specE_cost` liga a tabela a `Setup.Cvar`; `denseRun_dom_card` (memória `S_D M²`);
  `denseRun_ticks_le` (tempo `≤ S_D M² (cL + 4M + 3)`); `rebuild_spec` (apontadores reconstroem
  uma representação ótima em `Rset`).
* Orçamento `N`: `entryTmB`/`denseRunB` (pares `(n_L, w)`); `specEB_cost` liga a `Setup.Cb`;
  `denseRunB_dom_card` (`S_D N M²`); `denseRunB_ticks_le` e `denseRunB_ticks_le'` (tempo, com o custo
  de folha pago só nas posições `n = 1`); `rebuildB_spec` (`RsetN`: exatamente `n` folhas).
* Custos de folha: `leafPre` (pré-computados, 1 operação) e `leafInit` (perda local calculada
  sobre as `P` observações, `4P + 3` operações; `leafInit_val` prova que o valor é `Φ_H`).
* Teoremas finais: `dense_variable_complexity`, `dense_budget_complexity`,
  `dense_variable_init`, `dense_budget_init` e o enunciado reunido `state_complexity_dense`.

Modelo: operações unitárias para leitura/escrita da tabela, soma e comparação no corpo ordenado
dos custos, como no TeX (comparações de chave e fluxos contam como unitárias). As definições são
`noncomputable` apenas porque o alfabeto `Setup.V` e `Setup.Phi` o são; a semântica de custo é a
de `Tm`.
-/

/-!
# III.9.1 — parte 1: modelo de custo (`Tm`), memória densa e motor de preenchimento

* `Tm α`: computação com contador de operações unitárias (escritor com `ℕ`).
* `Mem κ E`: memória densa: uma função `tab` (acesso aleatório em tempo unitário) com o
  conjunto `dom` de posições escritas; o número de entradas usadas é `dom.card`.
* `fillList`: percorre uma lista de posições, calcula cada entrada com um programa `entryOf`
  (que lê a memória) e a escreve (1 operação).
* `runFrom`: preenche os níveis `R, R-1, …, 0` (programação dinâmica ascendente).
-/

namespace Pendencias.DenseDP

open Classical

/-- Computação com contagem de operações unitárias. -/
structure Tm (α : Type) where
  val : α
  ticks : ℕ

instance : Monad Tm where
  pure a := ⟨a, 0⟩
  bind m f := ⟨(f m.val).val, m.ticks + (f m.val).ticks⟩

namespace Tm

/-- `n` operações unitárias -/
def tick (n : ℕ := 1) : Tm Unit := ⟨(), n⟩

@[simp] lemma pure_val {α : Type} (a : α) : (pure a : Tm α).val = a := rfl
@[simp] lemma pure_ticks {α : Type} (a : α) : (pure a : Tm α).ticks = 0 := rfl
@[simp] lemma bind_val {α β : Type} (m : Tm α) (f : α → Tm β) : (m >>= f).val = (f m.val).val := rfl
@[simp] lemma bind_ticks {α β : Type} (m : Tm α) (f : α → Tm β) :
    (m >>= f).ticks = m.ticks + (f m.val).ticks := rfl
@[simp] lemma tick_val (n : ℕ) : (tick n).val = () := rfl
@[simp] lemma tick_ticks (n : ℕ) : (tick n).ticks = n := rfl

end Tm

open Tm

/-- Memória densa: `tab` é lida em tempo unitário; `dom` registra as posições escritas. -/
structure Mem (κ E : Type) where
  tab : κ → E
  dom : Finset κ

/-- escrita de uma entrada -/
noncomputable def Mem.write {κ E : Type} (m : Mem κ E) (k : κ) (e : E) : Mem κ E :=
  ⟨Function.update m.tab k e, insert k m.dom⟩

/-- Percorre `keys`; cada posição é calculada por `entryOf` (que lê a memória) e escrita, ao
custo de uma operação de escrita. -/
noncomputable def fillList {κ E : Type} (entryOf : Mem κ E → κ → Tm E) :
    List κ → Mem κ E → Tm (Mem κ E)
  | [], m => pure m
  | k :: ks, m => do
      let e ← entryOf m k
      tick 1
      fillList entryOf ks (m.write k e)

theorem fillList_spec {κ E : Type} (entryOf : Mem κ E → κ → Tm E) (spec : κ → E)
    (deps : κ → Finset κ) (c : κ → ℕ)
    (hent : ∀ m k, (∀ k' ∈ deps k, m.tab k' = spec k') →
      (entryOf m k).val = spec k ∧ (entryOf m k).ticks = c k) :
    ∀ (keys : List κ) (m : Mem κ E),
      (∀ k ∈ keys, ∀ k' ∈ deps k, m.tab k' = spec k' ∧ k' ∉ keys) →
      (∀ k, (fillList entryOf keys m).val.tab k = if k ∈ keys then spec k else m.tab k) ∧
      (fillList entryOf keys m).val.dom = m.dom ∪ keys.toFinset ∧
      (fillList entryOf keys m).ticks = (keys.map fun k => c k + 1).sum := by
  intro keys
  induction keys with
  | nil => intro m _; simp [fillList]
  | cons k ks ih =>
      intro m hm
      have hk := hent m k (fun k' hk' => (hm k (List.mem_cons_self) k' hk').1)
      have hm' : ∀ k2 ∈ ks, ∀ k' ∈ deps k2, (m.write k (spec k)).tab k' = spec k' ∧ k' ∉ ks := by
        intro k2 hk2 k' hk'
        obtain ⟨h1, h2⟩ := hm k2 (List.mem_cons_of_mem _ hk2) k' hk'
        have hne : k' ≠ k := fun e => h2 (e ▸ List.mem_cons_self)
        refine ⟨?_, fun h => h2 (List.mem_cons_of_mem _ h)⟩
        simp [Mem.write, Function.update_of_ne hne, h1]
      obtain ⟨i1, i2, i3⟩ := ih (m.write k (spec k)) hm'
      have hv : (fillList entryOf (k :: ks) m).val =
          (fillList entryOf ks (m.write k (spec k))).val := by
        show (fillList entryOf ks (m.write k (entryOf m k).val)).val = _
        rw [hk.1]
      have ht : (fillList entryOf (k :: ks) m).ticks =
          c k + 1 + (fillList entryOf ks (m.write k (spec k))).ticks := by
        show (entryOf m k).ticks + (1 + (fillList entryOf ks (m.write k (entryOf m k).val)).ticks) = _
        rw [hk.1, hk.2]; ring
      refine ⟨fun k0 => ?_, ?_, ?_⟩
      · rw [hv, i1 k0]
        by_cases h0 : k0 = k
        · subst h0; by_cases h1 : k0 ∈ ks <;> simp [h1, Mem.write]
        · by_cases h1 : k0 ∈ ks
          · simp [h1]
          · simp [h0, h1, Mem.write]
      · rw [hv, i2]
        ext x; simp [Mem.write]
      · rw [ht, i3]; simp

/-- Preenche os níveis `R, R-1, …, 0`; `levelKeys r` lista as posições do nível `r`. -/
noncomputable def runFrom {κ E : Type} (levelKeys : ℕ → List κ) (entryOf : Mem κ E → κ → Tm E) :
    ℕ → Mem κ E → Tm (Mem κ E)
  | 0, m => fillList entryOf (levelKeys 0) m
  | r + 1, m => do
      let m' ← fillList entryOf (levelKeys (r + 1)) m
      runFrom levelKeys entryOf r m'

theorem runFrom_spec {κ E : Type} (levelKeys : ℕ → List κ) (lvl : κ → ℕ)
    (entryOf : Mem κ E → κ → Tm E) (spec : κ → E) (deps : κ → Finset κ) (c : κ → ℕ)
    (hent : ∀ m k, (∀ k' ∈ deps k, m.tab k' = spec k') →
      (entryOf m k).val = spec k ∧ (entryOf m k).ticks = c k)
    (hlvl : ∀ r, ∀ k ∈ levelKeys r, lvl k = r)
    (hdeps : ∀ r, ∀ k ∈ levelKeys r, ∀ k' ∈ deps k, k' ∈ levelKeys (r + 1)) :
    ∀ (R : ℕ) (m : Mem κ E), (∀ r > R, ∀ k ∈ levelKeys r, m.tab k = spec k) →
      (∀ r ≤ R, ∀ k ∈ levelKeys r, (runFrom levelKeys entryOf R m).val.tab k = spec k) ∧
      (∀ r > R, ∀ k ∈ levelKeys r, (runFrom levelKeys entryOf R m).val.tab k = spec k) ∧
      (runFrom levelKeys entryOf R m).val.dom =
        m.dom ∪ (Finset.range (R + 1)).biUnion (fun r => (levelKeys r).toFinset) ∧
      (runFrom levelKeys entryOf R m).ticks =
        ((List.range (R + 1)).map fun r => ((levelKeys r).map fun k => c k + 1).sum).sum := by
  intro R
  induction R with
  | zero =>
      intro m hm
      have hfl := fillList_spec entryOf spec deps c hent (levelKeys 0) m (by
        intro k hk k' hk'
        have h1 : k' ∈ levelKeys 1 := hdeps 0 k hk k' hk'
        refine ⟨hm 1 (by omega) k' h1, fun h => ?_⟩
        have := hlvl 0 k' h; have := hlvl 1 k' h1; omega)
      obtain ⟨f1, f2, f3⟩ := hfl
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro r hr k hk
        have : r = 0 := by omega
        subst this
        simp [runFrom, f1 k, hk]
      · intro r hr k hk
        have hk0 : k ∉ levelKeys 0 := fun h => by
          have := hlvl 0 k h; have := hlvl r k hk; omega
        simp [runFrom, f1 k, hk0, hm r hr k hk]
      · simp [runFrom, f2]
      · simp [runFrom, f3]
  | succ R ih =>
      intro m hm
      have hfl := fillList_spec entryOf spec deps c hent (levelKeys (R + 1)) m (by
        intro k hk k' hk'
        have h1 : k' ∈ levelKeys (R + 2) := hdeps (R + 1) k hk k' hk'
        refine ⟨hm (R + 2) (by omega) k' h1, fun h => ?_⟩
        have := hlvl (R + 1) k' h; have := hlvl (R + 2) k' h1; omega)
      obtain ⟨f1, f2, f3⟩ := hfl
      have hm' : ∀ r > R, ∀ k ∈ levelKeys r,
          (fillList entryOf (levelKeys (R + 1)) m).val.tab k = spec k := by
        intro r hr k hk
        rw [f1 k]
        by_cases hk1 : k ∈ levelKeys (R + 1)
        · simp [hk1]
        · simp only [hk1, if_false]
          exact hm r (by
            by_contra hle
            have : r = R + 1 := by omega
            subst this; exact hk1 hk) k hk
      obtain ⟨g1, g2, g3, g4⟩ := ih _ hm'
      simp only [runFrom, bind_val, bind_ticks]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro r hr k hk
        by_cases hr' : r ≤ R
        · exact g1 r hr' k hk
        · exact g2 r (by omega) k hk
      · intro r hr k hk
        exact g2 r (by omega) k hk
      · rw [g3, f2]
        ext x
        simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_range, List.mem_toFinset]
        constructor
        · rintro ((h | h) | ⟨r, hr, h⟩)
          · exact Or.inl h
          · exact Or.inr ⟨R + 1, by omega, h⟩
          · exact Or.inr ⟨r, by omega, h⟩
        · rintro (h | ⟨r, hr, h⟩)
          · exact Or.inl (Or.inl h)
          · by_cases hr' : r ≤ R
            · exact Or.inr ⟨r, by omega, h⟩
            · have : r = R + 1 := by omega
              subst this; exact Or.inl (Or.inr h)
      · rw [f3, g4]
        simp only [List.range_succ, List.map_append, List.sum_append, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil]
        ring

end Pendencias.DenseDP

/-!
# III.9.1 — parte 2: implementação densa da recorrência `C_d` (árvore variável)

Tabela densa indexada por `(r, j, u, v)`: célula `(r, j)` de profundidade relativa `r` e
fronteiras `(u, v)`. A entrada guarda o custo e o apontador de reconstrução. Os níveis são
preenchidos de `r = D` (folhas) até `r = 0` (raiz).
-/

namespace Pendencias.DenseDP

open Artigo Classical Tm

/-- posição da tabela: `(r, j, u, v)` -/
abbrev Key := ℕ × ℕ × ℚ × ℚ

/-- apontador de reconstrução: folha, ou subdivisão com valor intermediário `w` -/
inductive Ptr
  | leaf
  | split (w : ℚ)

instance : Inhabited Ptr := ⟨Ptr.leaf⟩

/-- entrada da tabela: custo e apontador -/
abbrev Entry := WithTop ℚ × Ptr

instance : Inhabited Entry := ⟨(⊤, Ptr.leaf)⟩

/-- passada pura de mínimo com argmin: estado `(melhor custo, melhor w)`; só substitui se
estritamente menor (primeiro mínimo na ordem da lista). -/
def scanPure {α : Type} (f : α → WithTop ℚ) : List α → WithTop ℚ × Option α → WithTop ℚ × Option α
  | [], s => s
  | w :: ws, s => scanPure f ws (if f w < s.1 then (f w, some w) else s)

/-- mesma passada com contagem: cada candidato custa os passos de `cand w` mais uma comparação -/
def scanTm {α : Type} (cand : α → Tm (WithTop ℚ)) :
    List α → WithTop ℚ × Option α → Tm (WithTop ℚ × Option α)
  | [], s => pure s
  | w :: ws, s => do
      let x ← cand w
      tick 1
      scanTm cand ws (if x < s.1 then (x, some w) else s)

lemma scanTm_val {α : Type} (cand : α → Tm (WithTop ℚ)) : ∀ (ws : List α) (s : WithTop ℚ × Option α),
    (scanTm cand ws s).val = scanPure (fun w => (cand w).val) ws s
  | [], s => rfl
  | w :: ws, s => by
      show (scanTm cand ws (if (cand w).val < s.1 then ((cand w).val, some w) else s)).val = _
      rw [scanTm_val cand ws]; rfl

lemma scanTm_ticks {α : Type} (cand : α → Tm (WithTop ℚ)) (c : ℕ) (hc : ∀ w, (cand w).ticks = c) :
    ∀ (ws : List α) (s : WithTop ℚ × Option α), (scanTm cand ws s).ticks = ws.length * (c + 1)
  | [], s => by simp [scanTm]
  | w :: ws, s => by
      show (cand w).ticks + (1 + (scanTm cand ws (if (cand w).val < s.1 then ((cand w).val, some w)
        else s)).ticks) = _
      rw [scanTm_ticks cand c hc ws, hc w]; simp [List.length_cons]; ring

lemma scanPure_best {α : Type} (f : α → WithTop ℚ) : ∀ (ws : List α) (s : WithTop ℚ × Option α),
    (scanPure f ws s).1 = min s.1 ((ws.map f).foldr min ⊤)
  | [], s => by simp [scanPure]
  | w :: ws, s => by
      have := scanPure_best f ws (if f w < s.1 then (f w, some w) else s)
      show (scanPure f ws _).1 = _
      rw [this]
      simp only [List.map_cons, List.foldr_cons]
      by_cases h : f w < s.1
      · rw [if_pos h]
        show min (f w) _ = _
        exact (min_eq_right (le_trans (min_le_left _ _) h.le)).symm
      · rw [if_neg h]
        push_neg at h
        rw [← min_assoc, min_eq_left h]

/-- invariante do apontador: se `some w`, então `w ∈ U` e `f w` é o custo atual; e custo
finito exige apontador. -/
lemma scanPure_ptr {α : Type} (f : α → WithTop ℚ) (U : Set α) : ∀ (ws : List α) (s : WithTop ℚ × Option α),
    (∀ w ∈ ws, w ∈ U) →
    ((∀ w, s.2 = some w → w ∈ U ∧ f w = s.1) ∧ (s.1 ≠ ⊤ → ∃ w, s.2 = some w)) →
    ((∀ w, (scanPure f ws s).2 = some w → w ∈ U ∧ f w = (scanPure f ws s).1) ∧
      ((scanPure f ws s).1 ≠ ⊤ → ∃ w, (scanPure f ws s).2 = some w))
  | [], s, _, h => h
  | w :: ws, s, hU, h => by
      simp only [scanPure]
      apply scanPure_ptr f U ws _ (fun w' hw' => hU w' (List.mem_cons_of_mem _ hw'))
      by_cases hlt : f w < s.1
      · simp only [hlt, if_true]
        refine ⟨fun w' hw' => ?_, fun _ => ⟨w, rfl⟩⟩
        have hww : w = w' := by simpa using hw'
        subst hww
        exact ⟨hU w (List.mem_cons_self), rfl⟩
      · simp only [hlt, if_false]; exact h

end Pendencias.DenseDP

/-!
# III.9.1 — parte 3: programa da entrada, especificação e correspondência com `Cvar`
-/

namespace Pendencias.DenseDP

open Artigo Classical Tm

variable (S : Setup)

/-- o alfabeto de valores `𝒱_{D,H}(K)` como lista (`M` elementos) -/
noncomputable def Vl : List ℚ := S.V.toList

lemma Vl_length : (Vl S).length = S.V.card := Finset.length_toList _

/-- soma dos custos dos dois filhos para o valor intermediário `w` -/
def childVal (g : Key → Entry) (r j : ℕ) (u v w : ℚ) : WithTop ℚ :=
  (g (r + 1, 2 * j, u, w)).1 + (g (r + 1, 2 * j + 1, w, v)).1

/-- a entrada da tabela como função pura dos filhos: candidatos `w ∈ 𝒱`, penalidade
`λ_bits + λ_split`, comparação com o custo de folha `phi` (a folha vence empates) -/
noncomputable def entryPure (phi : WithTop ℚ) (g : Key → Entry) : Key → Entry
  | (r, j, u, v) =>
    if r < S.D then
      let sc := scanPure (fun w => childVal g r j u v w) (Vl S) (⊤, none)
      let sp : WithTop ℚ := ((S.lb + S.ls : ℚ) : WithTop ℚ) + sc.1
      if phi ≤ sp then (phi, Ptr.leaf) else (sp, Ptr.split (sc.2.getD 0))
    else (phi, Ptr.leaf)

/-- programa que calcula o custo de folha de uma célula (`(r,j)`) e fronteiras `(u,v)` -/
abbrev LeafProg := ℕ → ℕ → ℚ → ℚ → Tm (WithTop ℚ)

/-- o programa denso de uma entrada: lê o custo de folha, varre os `M` valores intermediários
(2 leituras, 1 soma e 1 comparação por candidato), soma a penalidade (1) e compara com a folha (1). -/
noncomputable def entryTm (leaf : LeafProg) (m : Mem Key Entry) : Key → Tm Entry
  | (r, j, u, v) => do
    let phi ← leaf r j u v
    if r < S.D then do
      let sc ← scanTm (fun w => do tick 3; pure (childVal m.tab r j u v w)) (Vl S) (⊤, none)
      tick 1
      tick 1
      pure (let sp : WithTop ℚ := ((S.lb + S.ls : ℚ) : WithTop ℚ) + sc.1
        if phi ≤ sp then (phi, Ptr.leaf) else (sp, Ptr.split (sc.2.getD 0)))
    else pure (phi, Ptr.leaf)

lemma entryTm_val (leaf : LeafProg) (m : Mem Key Entry) (r j : ℕ) (u v : ℚ) :
    (entryTm S leaf m (r, j, u, v)).val = entryPure S (leaf r j u v).val m.tab (r, j, u, v) := by
  unfold entryTm entryPure
  by_cases h : r < S.D
  · simp only [h, if_true, bind_val, tick_val, pure_val]
    rw [scanTm_val]
    rfl
  · simp [h]

lemma entryTm_ticks (leaf : LeafProg) (m : Mem Key Entry) (r j : ℕ) (u v : ℚ) :
    (entryTm S leaf m (r, j, u, v)).ticks =
      (leaf r j u v).ticks + (if r < S.D then 4 * S.V.card + 2 else 0) := by
  unfold entryTm
  by_cases h : r < S.D
  · simp only [h, if_true, bind_ticks, tick_ticks, pure_ticks, bind_val, tick_val, pure_val]
    have := scanTm_ticks (fun w => (do tick 3; pure (childVal m.tab r j u v w) : Tm (WithTop ℚ)))
      3 (fun w => by simp) (Vl S) (⊤, none)
    rw [this, Vl_length]
    ring
  · simp [h]

/-- especificação por recursão em `d = D - r` -/
noncomputable def specE (phiv : ℕ → ℕ → ℚ → ℚ → WithTop ℚ) : ℕ → Key → Entry
  | 0, (r, j, u, v) => (phiv r j u v, Ptr.leaf)
  | d + 1, (r, j, u, v) => entryPure S (phiv r j u v) (specE phiv d) (r, j, u, v)

/-- a tabela ideal: o nível `r` usa `d = D - r` -/
noncomputable def spec (phiv : ℕ → ℕ → ℚ → ℚ → WithTop ℚ) (k : Key) : Entry :=
  specE S phiv (S.D - k.1) k

lemma entryPure_congr (phi : WithTop ℚ) (g g' : Key → Entry) (r j : ℕ) (u v : ℚ)
    (h : ∀ w, g (r + 1, 2 * j, u, w) = g' (r + 1, 2 * j, u, w) ∧
      g (r + 1, 2 * j + 1, w, v) = g' (r + 1, 2 * j + 1, w, v)) :
    entryPure S phi g (r, j, u, v) = entryPure S phi g' (r, j, u, v) := by
  unfold entryPure
  have : (fun w => childVal g r j u v w) = fun w => childVal g' r j u v w := by
    funext w; unfold childVal; rw [(h w).1, (h w).2]
  simp only [this]

lemma spec_rec (phiv : ℕ → ℕ → ℚ → ℚ → WithTop ℚ) (r j : ℕ) (u v : ℚ) (hr : r < S.D) :
    spec S phiv (r, j, u, v) = entryPure S (phiv r j u v) (spec S phiv) (r, j, u, v) := by
  obtain ⟨d, hd⟩ : ∃ d, S.D - r = d + 1 := ⟨S.D - r - 1, by omega⟩
  unfold spec
  simp only [hd, specE]
  apply entryPure_congr
  intro w
  have : S.D - (r + 1) = d := by omega
  simp [this]

lemma spec_leaf (phiv : ℕ → ℕ → ℚ → ℚ → WithTop ℚ) (j : ℕ) (u v : ℚ) :
    spec S phiv (S.D, j, u, v) = (phiv S.D j u v, Ptr.leaf) := by
  simp [spec, specE]

end Pendencias.DenseDP

/-!
# III.9.1 — parte 4: custo da tabela = `Cvar`; execução densa, memória e tempo
-/

namespace Pendencias.DenseDP

open Artigo Classical Tm

variable (S : Setup)

lemma foldr_min_eq_inf (V : Finset ℚ) (f : ℚ → WithTop ℚ) :
    (V.toList.map f).foldr min ⊤ = V.inf f := by
  have h : ∀ l : List ℚ, (l.map f).foldr min ⊤ = l.toFinset.inf f := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
        simp only [List.map_cons, List.foldr_cons, ih, List.toFinset_cons, Finset.inf_insert]
  rw [h, Finset.toList_toFinset]

/-- índice inteiro `m` da célula relativa `(r, j)` de `K = J_{k₀,m₀}`: `m₀ 2^r + j` -/
def cellM (r j : ℕ) : ℤ := S.m₀ * 2 ^ r + j

lemma cellM_left (r j : ℕ) : cellM S (r + 1) (2 * j) = 2 * cellM S r j := by
  unfold cellM; push_cast; ring

lemma cellM_right (r j : ℕ) : cellM S (r + 1) (2 * j + 1) = 2 * cellM S r j + 1 := by
  unfold cellM; push_cast; ring

/-- **Correspondência com `Cvar`**: o custo da tabela ideal é `C_{D-r}(J_{r,j};u,v)`. -/
theorem specE_cost (phiv : ℕ → ℕ → ℚ → ℚ → WithTop ℚ)
    (hphi : ∀ r j u v, phiv r j u v = S.Phi (S.k₀ + r) (cellM S r j) u v) :
    ∀ d r, S.D - r = d → ∀ j u v,
      (specE S phiv d (r, j, u, v)).1 = S.Cvar d (S.k₀ + r) (cellM S r j) u v := by
  intro d
  induction d with
  | zero => intro r hr j u v; simp [specE, Setup.Cvar, hphi]
  | succ d ih =>
      intro r hr j u v
      have hlt : r < S.D := by omega
      have hsc : (scanPure (fun w => childVal (specE S phiv d) r j u v w) (Vl S) (⊤, none)).1 =
          S.V.inf fun w => S.Cvar d (S.k₀ + r + 1) (2 * cellM S r j) u w +
            S.Cvar d (S.k₀ + r + 1) (2 * cellM S r j + 1) w v := by
        rw [scanPure_best, min_eq_right le_top, Vl, ← foldr_min_eq_inf]
        congr 2
        funext w
        unfold childVal
        rw [ih (r + 1) (by omega) (2 * j) u w, ih (r + 1) (by omega) (2 * j + 1) w v,
          cellM_left, cellM_right]
        rfl
      simp only [specE, entryPure, if_pos hlt, Setup.Cvar, hphi, hsc]
      split_ifs with h
      · exact (min_eq_left h).symm
      · exact (min_eq_right (le_of_not_ge h)).symm

end Pendencias.DenseDP

/-!
# III.9.1 — parte 5: execução densa completa (variável), memória e tempo
-/

namespace Pendencias.DenseDP

open Artigo Classical Tm

variable (S : Setup)

/-- posições do nível `r`: células `(r,j)`, `j < 2^r`, e pares `(u,v) ∈ 𝒱²` -/
noncomputable def levelKeys (r : ℕ) : List Key :=
  if r ≤ S.D then (List.range (2 ^ r)).flatMap fun j => (Vl S).flatMap fun u =>
    (Vl S).map fun v => (r, j, u, v)
  else []

lemma mem_levelKeys {r : ℕ} {k : Key} :
    k ∈ levelKeys S r ↔ ∃ j u v, k = (r, j, u, v) ∧ r ≤ S.D ∧ j < 2 ^ r ∧ u ∈ S.V ∧ v ∈ S.V := by
  unfold levelKeys
  by_cases h : r ≤ S.D
  · simp only [h, if_true, List.mem_flatMap, List.mem_range, List.mem_map, Vl,
      Finset.mem_toList]
    constructor
    · rintro ⟨j, hj, u, hu, v, hv, rfl⟩; exact ⟨j, u, v, rfl, trivial, hj, hu, hv⟩
    · rintro ⟨j, u, v, rfl, _, hj, hu, hv⟩; exact ⟨j, hj, u, hu, v, hv, rfl⟩
  · simp [h]

lemma levelKeys_length (r : ℕ) :
    (levelKeys S r).length = if r ≤ S.D then 2 ^ r * S.V.card ^ 2 else 0 := by
  unfold levelKeys
  by_cases h : r ≤ S.D
  · simp only [h, if_true, List.length_flatMap, List.length_map, Vl_length, List.length_range]
    simp [List.map_const', mul_assoc, sq]
    exact Or.inl (Vl_length S)
  · simp [h]

/-- dependências de uma posição: as entradas dos dois filhos para todo `w ∈ 𝒱` -/
noncomputable def depsK (k : Key) : Finset Key :=
  if k.1 < S.D then
    ((Vl S).toFinset.image fun w => (k.1 + 1, 2 * k.2.1, k.2.2.1, w)) ∪
      ((Vl S).toFinset.image fun w => (k.1 + 1, 2 * k.2.1 + 1, w, k.2.2.2))
  else ∅

/-- memória inicial: nada escrito -/
noncomputable def mem0 : Mem Key Entry := ⟨fun _ => default, ∅⟩

/-- **A implementação densa**: preenche os níveis `D, D-1, …, 0` (programação dinâmica
ascendente com memoização), usando `leaf` como programa do custo de folha. -/
noncomputable def denseRun (leaf : LeafProg) : Tm (Mem Key Entry) :=
  runFrom (levelKeys S) (entryTm S leaf) S.D (mem0)

/-- tempo por entrada do nível `r`, sem o custo de folha: `4M+2` em nós internos -/
noncomputable def stepCost (S : Setup) (r : ℕ) : ℕ := if r < S.D then 4 * S.V.card + 2 else 0

lemma scanPure_congr (f f' : ℚ → WithTop ℚ) : ∀ (ws : List ℚ) (s : WithTop ℚ × Option ℚ),
    (∀ w ∈ ws, f w = f' w) → scanPure f ws s = scanPure f' ws s
  | [], s, _ => rfl
  | w :: ws, s, h => by
      simp only [scanPure]
      rw [h w List.mem_cons_self]
      exact scanPure_congr f f' ws _ (fun w' hw' => h w' (List.mem_cons_of_mem _ hw'))

lemma entryPure_congr' (phi : WithTop ℚ) (g g' : Key → Entry) (r j : ℕ) (u v : ℚ)
    (h : ∀ w ∈ Vl S, g (r + 1, 2 * j, u, w) = g' (r + 1, 2 * j, u, w) ∧
      g (r + 1, 2 * j + 1, w, v) = g' (r + 1, 2 * j + 1, w, v)) :
    entryPure S phi g (r, j, u, v) = entryPure S phi g' (r, j, u, v) := by
  unfold entryPure
  have : scanPure (fun w => childVal g r j u v w) (Vl S) (⊤, none) =
      scanPure (fun w => childVal g' r j u v w) (Vl S) (⊤, none) := by
    apply scanPure_congr
    intro w hw
    unfold childVal; rw [(h w hw).1, (h w hw).2]
  simp only [this]

lemma spec_ge (phiv : ℕ → ℕ → ℚ → ℚ → WithTop ℚ) {r : ℕ} (hr : S.D ≤ r) (j : ℕ) (u v : ℚ) :
    spec S phiv (r, j, u, v) = (phiv r j u v, Ptr.leaf) := by
  have : S.D - r = 0 := Nat.sub_eq_zero_of_le hr
  simp [spec, this, specE]

lemma mem_depsK_left {r j : ℕ} {u v w : ℚ} (hr : r < S.D) (hw : w ∈ Vl S) :
    (r + 1, 2 * j, u, w) ∈ depsK S (r, j, u, v) := by
  simp only [depsK, hr, if_true, Finset.mem_union, Finset.mem_image, List.mem_toFinset]
  exact Or.inl ⟨w, hw, rfl⟩

lemma mem_depsK_right {r j : ℕ} {u v w : ℚ} (hr : r < S.D) (hw : w ∈ Vl S) :
    (r + 1, 2 * j + 1, w, v) ∈ depsK S (r, j, u, v) := by
  simp only [depsK, hr, if_true, Finset.mem_union, Finset.mem_image, List.mem_toFinset]
  exact Or.inr ⟨w, hw, rfl⟩

theorem denseRun_spec (leaf : LeafProg) (phiv : ℕ → ℕ → ℚ → ℚ → WithTop ℚ) (cL : ℕ)
    (hv : ∀ r j u v, (leaf r j u v).val = phiv r j u v)
    (ht : ∀ r j u v, (leaf r j u v).ticks = cL) :
    (∀ r ≤ S.D, ∀ k ∈ levelKeys S r, (denseRun S leaf).val.tab k = spec S phiv k) ∧
    (denseRun S leaf).val.dom =
      (Finset.range (S.D + 1)).biUnion (fun r => (levelKeys S r).toFinset) ∧
    (denseRun S leaf).ticks =
      ((List.range (S.D + 1)).map fun r =>
        ((levelKeys S r).map fun _ => cL + stepCost S r + 1).sum).sum := by
  have hmain := runFrom_spec (levelKeys S) (fun k : Key => k.1) (entryTm S leaf) (spec S phiv)
    (depsK S) (fun k => cL + stepCost S k.1) ?_ ?_ ?_ S.D (mem0) ?_
  · obtain ⟨h1, h2, h3, h4⟩ := hmain
    refine ⟨fun r hr k hk => h1 r hr k hk, ?_, ?_⟩
    · rw [denseRun, h3]; ext x; simp [mem0]
    · rw [denseRun, h4]
      congr 1
      apply List.map_congr_left
      intro r hr
      apply congrArg
      apply List.map_congr_left
      intro k hk
      obtain ⟨j, u, v, rfl, -⟩ := (mem_levelKeys S).mp hk
      rfl
  · intro m k hdep
    obtain ⟨r, j, u, v⟩ := k
    refine ⟨?_, ?_⟩
    · rw [entryTm_val]
      simp only [hv]
      by_cases hr : r < S.D
      · rw [spec_rec S phiv r j u v hr]
        apply entryPure_congr'
        intro w hw
        exact ⟨hdep _ (mem_depsK_left S hr hw), hdep _ (mem_depsK_right S hr hw)⟩
      · have hge : S.D ≤ r := Nat.not_lt.mp hr
        rw [spec_ge S phiv hge]
        simp [entryPure, hr]
    · rw [entryTm_ticks, ht]; simp [stepCost]
  · intro r k hk
    obtain ⟨j, u, v, rfl, -⟩ := (mem_levelKeys S).mp hk
    rfl
  · intro r k hk k' hk'
    obtain ⟨j, u, v, rfl, hrD, hj, hu, hv⟩ := (mem_levelKeys S).mp hk
    by_cases hr : r < S.D
    · simp only [depsK, hr, if_true, Finset.mem_union, Finset.mem_image, List.mem_toFinset] at hk'
      rcases hk' with ⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩
      · exact (mem_levelKeys S).mpr ⟨2 * j, u, w, rfl, by omega, by rw [pow_succ]; omega, hu,
          by simpa [Vl] using hw⟩
      · exact (mem_levelKeys S).mpr ⟨2 * j + 1, w, v, rfl, by omega, by rw [pow_succ]; omega,
          by simpa [Vl] using hw, hv⟩
    · simp [depsK, hr] at hk'
  · intro r hr k hk
    obtain ⟨j, u, v, rfl, hrD, -⟩ := (mem_levelKeys S).mp hk
    omega

end Pendencias.DenseDP

/-!
# III.9.1 — parte 6: memória, tempo e teorema da árvore variável
-/

namespace Pendencias.DenseDP

open Artigo Classical Tm

variable (S : Setup)

/-- **Memória**: a tabela densa tem exatamente `S_D M²` entradas. -/
theorem denseRun_dom_card (leaf : LeafProg) (phiv : ℕ → ℕ → ℚ → ℚ → WithTop ℚ) (cL : ℕ)
    (hv : ∀ r j u v, (leaf r j u v).val = phiv r j u v)
    (ht : ∀ r j u v, (leaf r j u v).ticks = cL) :
    (denseRun S leaf).val.dom.card = (2 ^ (S.D + 1) - 1) * S.V.card ^ 2 := by
  obtain ⟨-, hdom, -⟩ := denseRun_spec S leaf phiv cL hv ht
  rw [hdom]
  let φ : (ℕ × ℕ) × ℚ × ℚ → Key := fun p => (p.1.1, p.1.2, p.2.1, p.2.2)
  have hφ : Function.Injective φ := by
    rintro ⟨⟨a, b⟩, c, d⟩ ⟨⟨a', b'⟩, c', d'⟩ h
    simp only [φ, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    rfl
  have himg : (Finset.range (S.D + 1)).biUnion (fun r => (levelKeys S r).toFinset) =
      (cellsD S.D ×ˢ (S.V ×ˢ S.V)).image φ := by
    ext k
    simp only [Finset.mem_biUnion, Finset.mem_range, List.mem_toFinset, mem_levelKeys,
      Finset.mem_image, Finset.mem_product, cellsD, Finset.mem_biUnion, Finset.mem_image, φ]
    constructor
    · rintro ⟨r, hr, j, u, v, rfl, hrD, hj, hu, hv'⟩
      exact ⟨⟨(r, j), u, v⟩, ⟨⟨r, by omega, j, by simpa using hj, rfl⟩, hu, hv'⟩, rfl⟩
    · rintro ⟨⟨⟨r, j⟩, u, v⟩, ⟨⟨r', hr', j', hj', hrj⟩, hu, hv'⟩, rfl⟩
      simp only [Prod.mk.injEq] at hrj
      obtain ⟨rfl, rfl⟩ := hrj
      exact ⟨r', hr', j', u, v, rfl, by omega, by simpa using hj', hu, hv'⟩
  rw [himg, Finset.card_image_of_injective _ hφ, Finset.card_product, Finset.card_product,
    card_cellsD]
  ring

lemma sum_range_pow_le (X : ℕ) (g : ℕ → ℕ) :
    ∀ n, (∀ r < n, g r ≤ 2 ^ r * X) → ((List.range n).map g).sum ≤ (2 ^ n - 1) * X := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
      intro h
      rw [List.range_succ, List.map_append, List.sum_append]
      have := ih (fun r hr => h r (by omega))
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      have h2 := h n (by omega)
      have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      calc _ ≤ (2 ^ n - 1) * X + 2 ^ n * X := Nat.add_le_add this h2
        _ = (2 ^ (n + 1) - 1) * X := by
            rw [pow_succ]
            zify [hp, show 1 ≤ 2 ^ n * 2 by omega]
            ring

/-- **Tempo**: exatamente `∑_r 2^r M² (cL + 1 + stepCost r)` operações, em particular
`≤ S_D M² (cL + 4M + 3)`. -/
theorem denseRun_ticks_le (leaf : LeafProg) (phiv : ℕ → ℕ → ℚ → ℚ → WithTop ℚ) (cL : ℕ)
    (hv : ∀ r j u v, (leaf r j u v).val = phiv r j u v)
    (ht : ∀ r j u v, (leaf r j u v).ticks = cL) :
    (denseRun S leaf).ticks ≤ (2 ^ (S.D + 1) - 1) * S.V.card ^ 2 * (cL + 4 * S.V.card + 3) := by
  obtain ⟨-, -, htk⟩ := denseRun_spec S leaf phiv cL hv ht
  rw [htk]
  rw [mul_comm _ (S.V.card ^ 2), mul_assoc, mul_comm (2 ^ (S.D + 1) - 1) _, ← mul_assoc]
  have hlev := sum_range_pow_le (S.V.card ^ 2 * (cL + 4 * S.V.card + 3))
    (fun r => ((levelKeys S r).map fun _ => cL + stepCost S r + 1).sum) (S.D + 1) ?_
  · calc _ ≤ _ := hlev
      _ = _ := by ring
  · intro r hr
    have hr' : r ≤ S.D := by omega
    simp only [List.map_const', List.sum_replicate, levelKeys_length, if_pos hr', smul_eq_mul]
    have hsc : stepCost S r ≤ 4 * S.V.card + 2 := by
      unfold stepCost; split_ifs <;> omega
    calc 2 ^ r * S.V.card ^ 2 * (cL + stepCost S r + 1)
        ≤ 2 ^ r * S.V.card ^ 2 * (cL + 4 * S.V.card + 3) :=
          Nat.mul_le_mul le_rfl (by omega)
      _ = 2 ^ r * (S.V.card ^ 2 * (cL + 4 * S.V.card + 3)) := by ring

end Pendencias.DenseDP

/-!
# III.9.1 — parte 7: reconstrução da árvore ótima pelos apontadores
-/

namespace Pendencias.DenseDP

open Artigo Classical Tm LTree

variable (S : Setup)

/-- folha de reconstrução: o átomo determinado pela célula e pelas fronteiras `(u,v)`, quando
`(u,v)` é admissível (`Φ_H < ∞`) -/
noncomputable def mkLeaf (k : ℕ) (m : ℤ) (u v : ℚ) : Option LTree :=
  if h : (u, v) ∈ PH S.H k m then some (LTree.leaf (Atom.ofEndpoints k m u v (mem_PH.mp h).1))
  else none

/-- reconstrução seguindo os apontadores da tabela `tab`: folha, ou nó com filhos
`(r+1, 2j, u, w)` e `(r+1, 2j+1, w, v)` -/
noncomputable def rebuild (tab : Key → Entry) : ℕ → ℕ → ℕ → ℚ → ℚ → Option LTree
  | 0, r, j, u, v => mkLeaf S (S.k₀ + r) (cellM S r j) u v
  | d + 1, r, j, u, v =>
      match (tab (r, j, u, v)).2 with
      | Ptr.leaf => mkLeaf S (S.k₀ + r) (cellM S r j) u v
      | Ptr.split w => do
          let l ← rebuild tab d (r + 1) (2 * j) u w
          let rr ← rebuild tab d (r + 1) (2 * j + 1) w v
          some (LTree.node l rr)

lemma mkLeaf_spec (hH : 2 ≤ S.H) (k : ℕ) (m : ℤ) (u v : ℚ) (hp : (u, v) ∈ PH S.H k m) :
    ∃ R, mkLeaf S k m u v = some R ∧ R ∈ S.Rset 0 k m u v ∧ S.costW R = S.Phi k m u v := by
  obtain ⟨b, ⟨hb, hbk, hbm⟩, hbuv⟩ := (endpoint_dictionary hH).1.2.2 (Finset.mem_coe.mpr hp)
  simp only [Prod.mk.injEq] at hbuv
  obtain ⟨rfl, rfl⟩ := hbuv
  subst hbk hbm
  have hne := (mem_PH.mp hp).1
  have hba : Atom.ofEndpoints b.k b.m b.lval b.rval hne = b := b.eq_ofEndpoints.symm
  refine ⟨LTree.leaf b, ?_, ?_, ?_⟩
  · unfold mkLeaf; rw [dif_pos hp]; simp only [hba]
  · rw [S.mem_Rset]
    refine ⟨by simp [depth], ?_, ⟨rfl, rfl⟩, rfl, rfl⟩
    rw [maxHeight_le_iff]
    intro c hc
    simp only [leaves, List.mem_singleton] at hc
    subst hc; exact hb
  · rw [S.Phi_atom hb]; rfl

theorem rebuild_spec (hH : 2 ≤ S.H) (phiv : ℕ → ℕ → ℚ → ℚ → WithTop ℚ)
    (hphi : ∀ r j u v, phiv r j u v = S.Phi (S.k₀ + r) (cellM S r j) u v)
    (tab : Key → Entry)
    (htab : ∀ r j u v, r ≤ S.D → j < 2 ^ r → u ∈ S.V → v ∈ S.V →
      tab (r, j, u, v) = spec S phiv (r, j, u, v)) :
    ∀ d r, S.D - r = d → ∀ j u v, j < 2 ^ r → u ∈ S.V → v ∈ S.V →
      (spec S phiv (r, j, u, v)).1 ≠ ⊤ →
      ∃ R, rebuild S tab d r j u v = some R ∧ R ∈ S.Rset d (S.k₀ + r) (cellM S r j) u v ∧
        S.costW R = (spec S phiv (r, j, u, v)).1 := by
  intro d
  induction d with
  | zero =>
      intro r hr j u v hj hu hv hfin
      have hge : S.D ≤ r := by omega
      rw [spec_ge S phiv hge, hphi] at hfin
      have hp : (u, v) ∈ PH S.H (S.k₀ + r) (cellM S r j) := by
        by_contra hnot
        apply hfin
        simp only [Setup.Phi, dif_neg hnot]
      obtain ⟨R, h1, h2, h3⟩ := mkLeaf_spec S hH _ _ u v hp
      refine ⟨R, ?_, h2, ?_⟩
      · simpa [rebuild] using h1
      · rw [spec_ge S phiv hge]; simp only [hphi]; exact h3
  | succ d ih =>
      intro r hr j u v hj hu hv hfin
      have hlt : r < S.D := by omega
      have hkey := htab r j u v hlt.le hj hu hv
      have hrec := spec_rec S phiv r j u v hlt
      unfold entryPure at hrec
      simp only [hlt, if_true] at hrec
      have hptr0 := scanPure_ptr (fun w => childVal (spec S phiv) r j u v w) (↑S.V : Set ℚ)
        (Vl S) (⊤, none) (fun w hw => by simpa [Vl] using hw)
        ⟨fun w h => by simp at h, fun h => absurd rfl h⟩
      generalize hsc : scanPure (fun w => childVal (spec S phiv) r j u v w) (Vl S) (⊤, none) = sc
        at hrec hptr0
      by_cases hle : phiv r j u v ≤ ((S.lb + S.ls : ℚ) : WithTop ℚ) + sc.1
      · have hspec : spec S phiv (r, j, u, v) = (phiv r j u v, Ptr.leaf) := by
          rw [hrec, if_pos hle]
        rw [hspec] at hfin
        simp only at hfin
        rw [hphi] at hfin
        have hp : (u, v) ∈ PH S.H (S.k₀ + r) (cellM S r j) := by
          by_contra hnot
          apply hfin
          simp only [Setup.Phi, dif_neg hnot]
        obtain ⟨R, h1, h2, h3⟩ := mkLeaf_spec S hH _ _ u v hp
        refine ⟨R, ?_, ?_, ?_⟩
        · simp [rebuild, hkey, hspec, h1]
        · rw [S.mem_Rset] at h2 ⊢
          obtain ⟨hd, hrest⟩ := h2
          exact ⟨by omega, hrest⟩
        · rw [hspec, ← hphi] at *
          exact h3
      · have hspec : spec S phiv (r, j, u, v) =
            (((S.lb + S.ls : ℚ) : WithTop ℚ) + sc.1, Ptr.split (sc.2.getD 0)) := by
          rw [hrec, if_neg hle]
        rw [hspec] at hfin
        simp only at hfin
        have hsc1 : sc.1 ≠ ⊤ := fun h => hfin (by rw [h]; simp)
        obtain ⟨hw, hex⟩ := hptr0
        obtain ⟨w, hw2⟩ := hex hsc1
        obtain ⟨hwV, hfw⟩ := hw w hw2
        have hwV' : w ∈ S.V := hwV
        have hfw' : childVal (spec S phiv) r j u v w = sc.1 := hfw
        have hfin2 : childVal (spec S phiv) r j u v w ≠ ⊤ := by rw [hfw']; exact hsc1
        unfold childVal at hfin2
        have hc1 : (spec S phiv (r + 1, 2 * j, u, w)).1 ≠ ⊤ := fun h => hfin2 (by rw [h]; simp)
        have hc2 : (spec S phiv (r + 1, 2 * j + 1, w, v)).1 ≠ ⊤ := fun h => hfin2 (by rw [h]; simp)
        obtain ⟨Rl, hl1, hl2, hl3⟩ := ih (r + 1) (by omega) (2 * j) u w
          (by rw [pow_succ]; omega) hu hwV' hc1
        obtain ⟨Rr, hr1, hr2, hr3⟩ := ih (r + 1) (by omega) (2 * j + 1) w v
          (by rw [pow_succ]; omega) hwV' hv hc2
        rw [cellM_left] at hl2
        rw [cellM_right] at hr2
        have hgetD : sc.2.getD 0 = w := by rw [hw2]; rfl
        refine ⟨LTree.node Rl Rr, ?_, ?_, ?_⟩
        · simp only [rebuild, hkey, hspec, hgetD, hl1, hr1]
          rfl
        · rw [S.mem_Rset] at hl2 hr2 ⊢
          obtain ⟨d1, h1, w1, lv1, rv1⟩ := hl2
          obtain ⟨d2, h2, w2, lv2, rv2⟩ := hr2
          refine ⟨?_, (maxHeight_node _ _).mpr ⟨h1, h2⟩, ⟨w1, w2, by rw [rv1, lv2]⟩, ?_, ?_⟩
          · simp only [depth]; omega
          · simpa [LTree.lval] using lv1
          · simpa [LTree.rval] using rv2
        · rw [S.costW_node, hl3, hr3, hspec]
          simp only
          rw [← hfw']
          unfold childVal
          rw [add_comm]

end Pendencias.DenseDP

/-!
# III.9.1 — parte 8: teorema da árvore variável (custos de folha pré-computados)
-/

namespace Pendencias.DenseDP

open Artigo Classical Tm LTree

variable (S : Setup)

/-- custo de folha pré-computado: uma leitura da tabela de `Φ_H` (1 operação) -/
noncomputable def leafPre : LeafProg := fun r j u v => do
  tick 1
  pure (S.Phi (S.k₀ + r) (cellM S r j) u v)

/-- **Teorema III.9.1 (árvore variável)**. A implementação densa `denseRun S (leafPre S)`
(programação dinâmica ascendente com memoização e apontadores) satisfaz:
(a) toda entrada `(r,j,u,v)` com `u,v ∈ 𝒱` guarda `C_{D-r}(J_{r,j};u,v)` (`Cvar`);
(b) a memória usa exatamente `S_D M²` entradas (custo + apontador);
(c) o número de operações é `≤ S_D M² (4M + 4) ≤ 8 S_D M³`;
(d) os apontadores reconstroem uma representação ótima: se `C_D(K;u,v) < ∞`, a árvore
reconstruída pertence a `𝔑_{D,H}(K;u,v)` e tem custo `C_D(K;u,v)`. -/
theorem dense_variable_complexity (hH : 2 ≤ S.H) :
    (∀ r j u v, r ≤ S.D → j < 2 ^ r → u ∈ S.V → v ∈ S.V →
      ((denseRun S (leafPre S)).val.tab (r, j, u, v)).1 =
        S.Cvar (S.D - r) (S.k₀ + r) (cellM S r j) u v) ∧
    (denseRun S (leafPre S)).val.dom.card = (2 ^ (S.D + 1) - 1) * S.V.card ^ 2 ∧
    (denseRun S (leafPre S)).ticks ≤ (2 ^ (S.D + 1) - 1) * S.V.card ^ 2 * (4 * S.V.card + 4) ∧
    (denseRun S (leafPre S)).ticks ≤ 8 * (2 ^ (S.D + 1) - 1) * S.V.card ^ 3 ∧
    (∀ u v, u ∈ S.V → v ∈ S.V → S.Cvar S.D S.k₀ S.m₀ u v ≠ ⊤ →
      ∃ R, rebuild S (denseRun S (leafPre S)).val.tab S.D 0 0 u v = some R ∧
        R ∈ S.Rset S.D S.k₀ S.m₀ u v ∧ S.costW R = S.Cvar S.D S.k₀ S.m₀ u v) := by
  set phiv : ℕ → ℕ → ℚ → ℚ → WithTop ℚ := fun r j u v => S.Phi (S.k₀ + r) (cellM S r j) u v
    with hphiv
  have hv : ∀ r j u v, (leafPre S r j u v).val = phiv r j u v := fun r j u v => rfl
  have ht : ∀ r j u v, (leafPre S r j u v).ticks = 1 := fun r j u v => rfl
  have hphi : ∀ r j u v, phiv r j u v = S.Phi (S.k₀ + r) (cellM S r j) u v := fun _ _ _ _ => rfl
  obtain ⟨hspec, -, -⟩ := denseRun_spec S (leafPre S) phiv 1 hv ht
  have htab : ∀ r j u v, r ≤ S.D → j < 2 ^ r → u ∈ S.V → v ∈ S.V →
      (denseRun S (leafPre S)).val.tab (r, j, u, v) = spec S phiv (r, j, u, v) := by
    intro r j u v hr hj hu hv'
    exact hspec r hr _ ((mem_levelKeys S).mpr ⟨j, u, v, rfl, hr, hj, hu, hv'⟩)
  have hcost : ∀ r j u v, r ≤ S.D → j < 2 ^ r → u ∈ S.V → v ∈ S.V →
      (spec S phiv (r, j, u, v)).1 = S.Cvar (S.D - r) (S.k₀ + r) (cellM S r j) u v := by
    intro r j u v hr hj hu hv'
    exact specE_cost S phiv hphi (S.D - r) r rfl j u v
  refine ⟨?_, denseRun_dom_card S (leafPre S) phiv 1 hv ht, ?_, ?_, ?_⟩
  · intro r j u v hr hj hu hv'
    rw [htab r j u v hr hj hu hv', hcost r j u v hr hj hu hv']
  · have := denseRun_ticks_le S (leafPre S) phiv 1 hv ht
    calc _ ≤ _ := this
      _ = _ := by ring_nf
  · have := denseRun_ticks_le S (leafPre S) phiv 1 hv ht
    refine this.trans ?_
    by_cases hM : S.V.card = 0
    · simp [hM]
    · have h1 : 1 ≤ S.V.card := Nat.one_le_iff_ne_zero.mpr hM
      have : S.V.card ^ 2 * (1 + 4 * S.V.card + 3) ≤ 8 * S.V.card ^ 3 := by
        nlinarith [Nat.mul_le_mul_left (S.V.card ^ 2) h1]
      calc (2 ^ (S.D + 1) - 1) * S.V.card ^ 2 * (1 + 4 * S.V.card + 3)
          = (2 ^ (S.D + 1) - 1) * (S.V.card ^ 2 * (1 + 4 * S.V.card + 3)) := by ring
        _ ≤ (2 ^ (S.D + 1) - 1) * (8 * S.V.card ^ 3) := Nat.mul_le_mul le_rfl this
        _ = 8 * (2 ^ (S.D + 1) - 1) * S.V.card ^ 3 := by ring
  · intro u v hu hv' hfin
    have hroot := hcost 0 0 u v (Nat.zero_le _) (by simp) hu hv'
    have hcell : cellM S 0 0 = S.m₀ := by simp [cellM]
    have hfin' : (spec S phiv (0, 0, u, v)).1 ≠ ⊤ := by
      rw [hroot]; simpa [hcell] using hfin
    obtain ⟨R, h1, h2, h3⟩ := rebuild_spec S hH phiv hphi _ htab S.D 0 (by simp) 0 u v
      (by simp) hu hv' hfin'
    refine ⟨R, h1, ?_, ?_⟩
    · simpa [hcell] using h2
    · rw [h3, hroot]; simp [hcell]

end Pendencias.DenseDP

/-!
# III.9.1 — parte 9: implementação densa com orçamento de até `N` folhas

Tabela indexada por `(r, j, u, v, n)`, `1 ≤ n ≤ N`. Entrada: custo `C_{D-r,n}(J_{r,j};u,v)` e
apontador `(n_L, w)`. Cada entrada com `n ≥ 2` varre os pares `(n_L, w)`, `1 ≤ n_L < n`, `w ∈ 𝒱`.
-/

namespace Pendencias.DenseDP

open Artigo Classical Tm

variable (S : Setup)

/-- posição da tabela com orçamento: `(r, j, u, v, n)` -/
abbrev BKey := ℕ × ℕ × ℚ × ℚ × ℕ

/-- apontador com orçamento: folha, ou subdivisão `(n_L, w)` -/
inductive BPtr
  | leaf
  | split (nL : ℕ) (w : ℚ)

instance : Inhabited BPtr := ⟨BPtr.leaf⟩

abbrev BEntry := WithTop ℚ × BPtr

instance : Inhabited BEntry := ⟨(⊤, BPtr.leaf)⟩

/-- pares `(n_L, w)`, `1 ≤ n_L < n`, `w ∈ 𝒱` -/
noncomputable def pairsL (n : ℕ) : List (ℕ × ℚ) :=
  (List.range' 1 (n - 1)).flatMap fun nL => (Vl S).map fun w => (nL, w)

lemma mem_pairsL {n : ℕ} {p : ℕ × ℚ} :
    p ∈ pairsL S n ↔ 1 ≤ p.1 ∧ p.1 < n ∧ p.2 ∈ S.V := by
  obtain ⟨nL, w⟩ := p
  simp only [pairsL, List.mem_flatMap, List.mem_range'_1, List.mem_map, Vl, Finset.mem_toList,
    Prod.mk.injEq]
  constructor
  · rintro ⟨a, ⟨h1, h2⟩, w', hw', rfl, rfl⟩; exact ⟨h1, by omega, hw'⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨nL, ⟨h1, by omega⟩, w, h3, rfl, rfl⟩

lemma pairsL_length (n : ℕ) : (pairsL S n).length = (n - 1) * S.V.card := by
  simp only [pairsL, List.length_flatMap, List.length_map, Vl_length, List.length_range']
  simp [List.map_const', List.sum_replicate]


/-- soma dos custos dos dois filhos para o par `(n_L, w)` -/
def childValB (g : BKey → BEntry) (r j : ℕ) (u v : ℚ) (n : ℕ) (p : ℕ × ℚ) : WithTop ℚ :=
  (g (r + 1, 2 * j, u, p.2, p.1)).1 + (g (r + 1, 2 * j + 1, p.2, v, n - p.1)).1

/-- entrada com orçamento como função pura: `n = 1` é folha (`phi`); `n ≥ 2` em nó interno é
`λ_bits + λ_split + min_{(n_L,w)}`; `n ≥ 2` no último nível é `+∞`. -/
noncomputable def entryPureB (phi : WithTop ℚ) (g : BKey → BEntry) : BKey → BEntry
  | (r, j, u, v, n) =>
    if n = 1 then (phi, BPtr.leaf)
    else if r < S.D then
      let sc := scanPure (fun p => childValB g r j u v n p) (pairsL S n) (⊤, none)
      (((S.lb + S.ls : ℚ) : WithTop ℚ) + sc.1,
        BPtr.split (sc.2.getD (1, 0)).1 (sc.2.getD (1, 0)).2)
    else (⊤, BPtr.leaf)

/-- o programa denso de uma entrada com orçamento: `n = 1` lê o custo de folha; `n ≥ 2` varre
os `(n-1) M` pares (2 leituras, 1 soma, 1 comparação cada) e soma a penalidade (1). -/
noncomputable def entryTmB (leaf : LeafProg) (m : Mem BKey BEntry) : BKey → Tm BEntry
  | (r, j, u, v, n) =>
    if n = 1 then do
      let phi ← leaf r j u v
      pure (phi, BPtr.leaf)
    else if r < S.D then do
      let sc ← scanTm (fun p => do tick 3; pure (childValB m.tab r j u v n p)) (pairsL S n)
        (⊤, none)
      tick 1
      pure (((S.lb + S.ls : ℚ) : WithTop ℚ) + sc.1,
        BPtr.split (sc.2.getD (1, 0)).1 (sc.2.getD (1, 0)).2)
    else pure (⊤, BPtr.leaf)

lemma entryTmB_val (leaf : LeafProg) (m : Mem BKey BEntry) (r j : ℕ) (u v : ℚ) (n : ℕ) :
    (entryTmB S leaf m (r, j, u, v, n)).val =
      entryPureB S (leaf r j u v).val m.tab (r, j, u, v, n) := by
  unfold entryTmB entryPureB
  by_cases h1 : n = 1
  · simp [h1]
  · by_cases h : r < S.D
    · simp only [h1, h, if_true, if_false, bind_val, tick_val, pure_val]
      rw [scanTm_val]
      rfl
    · simp [h1, h]

lemma entryTmB_ticks (leaf : LeafProg) (m : Mem BKey BEntry) (r j : ℕ) (u v : ℚ) (n : ℕ) :
    (entryTmB S leaf m (r, j, u, v, n)).ticks =
      if n = 1 then (leaf r j u v).ticks
      else if r < S.D then 4 * ((n - 1) * S.V.card) + 1 else 0 := by
  unfold entryTmB
  by_cases h1 : n = 1
  · simp [h1]
  · by_cases h : r < S.D
    · simp only [h1, h, if_true, if_false, bind_ticks, tick_ticks, pure_ticks, bind_val]
      have := scanTm_ticks (fun p => (do tick 3; pure (childValB m.tab r j u v n p) :
        Tm (WithTop ℚ))) 3 (fun w => by simp) (pairsL S n) (⊤, none)
      rw [this, pairsL_length]
      ring
    · simp [h1, h]

/-- especificação por recursão em `d = D - r` -/
noncomputable def specEB (phiv : ℕ → ℕ → ℚ → ℚ → WithTop ℚ) : ℕ → BKey → BEntry
  | 0, (r, j, u, v, n) => (if n = 1 then phiv r j u v else ⊤, BPtr.leaf)
  | d + 1, (r, j, u, v, n) => entryPureB S (phiv r j u v) (specEB phiv d) (r, j, u, v, n)

noncomputable def specB (phiv : ℕ → ℕ → ℚ → ℚ → WithTop ℚ) (k : BKey) : BEntry :=
  specEB S phiv (S.D - k.1) k

lemma scanPure_congr_gen {α : Type} (f f' : α → WithTop ℚ) :
    ∀ (ws : List α) (s : WithTop ℚ × Option α), (∀ w ∈ ws, f w = f' w) →
      scanPure f ws s = scanPure f' ws s
  | [], s, _ => rfl
  | w :: ws, s, h => by
      simp only [scanPure]
      rw [h w List.mem_cons_self]
      exact scanPure_congr_gen f f' ws _ (fun w' hw' => h w' (List.mem_cons_of_mem _ hw'))

lemma entryPureB_congr (phi : WithTop ℚ) (g g' : BKey → BEntry) (r j : ℕ) (u v : ℚ) (n : ℕ)
    (h : ∀ p ∈ pairsL S n, g (r + 1, 2 * j, u, p.2, p.1) = g' (r + 1, 2 * j, u, p.2, p.1) ∧
      g (r + 1, 2 * j + 1, p.2, v, n - p.1) = g' (r + 1, 2 * j + 1, p.2, v, n - p.1)) :
    entryPureB S phi g (r, j, u, v, n) = entryPureB S phi g' (r, j, u, v, n) := by
  unfold entryPureB
  have : scanPure (fun p => childValB g r j u v n p) (pairsL S n) (⊤, none) =
      scanPure (fun p => childValB g' r j u v n p) (pairsL S n) (⊤, none) := by
    apply scanPure_congr_gen
    intro p hp
    unfold childValB; rw [(h p hp).1, (h p hp).2]
  simp only [this]

lemma specB_rec (phiv : ℕ → ℕ → ℚ → ℚ → WithTop ℚ) (r j : ℕ) (u v : ℚ) (n : ℕ) (hr : r < S.D) :
    specB S phiv (r, j, u, v, n) = entryPureB S (phiv r j u v) (specB S phiv) (r, j, u, v, n) := by
  obtain ⟨d, hd⟩ : ∃ d, S.D - r = d + 1 := ⟨S.D - r - 1, by omega⟩
  unfold specB
  simp only [hd, specEB]
  apply entryPureB_congr
  intro p hp
  have : S.D - (r + 1) = d := by omega
  simp [this]

lemma specB_ge (phiv : ℕ → ℕ → ℚ → ℚ → WithTop ℚ) {r : ℕ} (hr : S.D ≤ r) (j : ℕ) (u v : ℚ)
    (n : ℕ) : specB S phiv (r, j, u, v, n) = (if n = 1 then phiv r j u v else ⊤, BPtr.leaf) := by
  have : S.D - r = 0 := Nat.sub_eq_zero_of_le hr
  simp [specB, this, specEB]

lemma foldr_min_eq_inf_gen {α : Type} [DecidableEq α] (l : List α) (f : α → WithTop ℚ) :
    (l.map f).foldr min ⊤ = l.toFinset.inf f := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.foldr_cons, ih, List.toFinset_cons, Finset.inf_insert]

lemma pairs_inf (n : ℕ) (F : ℕ × ℚ → WithTop ℚ) :
    ((pairsL S n).map F).foldr min ⊤ = (Finset.Ico 1 n).inf fun nL => S.V.inf fun w => F (nL, w) := by
  rw [foldr_min_eq_inf_gen]
  have : (pairsL S n).toFinset = Finset.Ico 1 n ×ˢ S.V := by
    ext ⟨nL, w⟩
    simp only [mem_pairsL, Finset.mem_product, Finset.mem_Ico, List.mem_toFinset]
    tauto
  rw [this, Finset.inf_product_left]

/-- **Correspondência com `Cb`** -/
theorem specEB_cost (phiv : ℕ → ℕ → ℚ → ℚ → WithTop ℚ)
    (hphi : ∀ r j u v, phiv r j u v = S.Phi (S.k₀ + r) (cellM S r j) u v) :
    ∀ d r, S.D - r = d → ∀ j u v n,
      (specEB S phiv d (r, j, u, v, n)).1 = S.Cb d n (S.k₀ + r) (cellM S r j) u v := by
  intro d
  induction d with
  | zero => intro r hr j u v n; simp [specEB, Setup.Cb, hphi]
  | succ d ih =>
      intro r hr j u v n
      have hlt : r < S.D := by omega
      by_cases hn : n = 1
      · simp [specEB, entryPureB, Setup.Cb, hn, hphi]
      · have hsc : (scanPure (fun p => childValB (specEB S phiv d) r j u v n p) (pairsL S n)
            (⊤, none)).1 = (Finset.Ico 1 n).inf fun nL => S.V.inf fun w =>
              S.Cb d nL (S.k₀ + r + 1) (2 * cellM S r j) u w +
                S.Cb d (n - nL) (S.k₀ + r + 1) (2 * cellM S r j + 1) w v := by
          rw [scanPure_best, min_eq_right le_top, pairs_inf]
          congr 1; funext nL; congr 1; funext w
          unfold childValB
          rw [ih (r + 1) (by omega) (2 * j) u w nL, ih (r + 1) (by omega) (2 * j + 1) w v (n - nL),
            cellM_left, cellM_right]
          rfl
        simp only [specEB, entryPureB, hn, if_false, if_pos hlt, Setup.Cb, hsc]

end Pendencias.DenseDP

/-!
# III.9.1 — parte 10: execução com orçamento, memória `S_D N M²` e tempo `O(S_D N² M³)`
-/

namespace Pendencias.DenseDP

open Artigo Classical Tm

variable (S : Setup)

/-- posições do nível `r`: `(r,j,u,v,n)` com `j < 2^r`, `u,v ∈ 𝒱`, `1 ≤ n ≤ N` -/
noncomputable def levelKeysB (N r : ℕ) : List BKey :=
  if r ≤ S.D then (List.range (2 ^ r)).flatMap fun j => (Vl S).flatMap fun u =>
    (Vl S).flatMap fun v => (List.range' 1 N).map fun n => (r, j, u, v, n)
  else []

lemma mem_levelKeysB {N r : ℕ} {k : BKey} :
    k ∈ levelKeysB S N r ↔ ∃ j u v n, k = (r, j, u, v, n) ∧ r ≤ S.D ∧ j < 2 ^ r ∧ u ∈ S.V ∧
      v ∈ S.V ∧ 1 ≤ n ∧ n ≤ N := by
  unfold levelKeysB
  by_cases h : r ≤ S.D
  · simp only [h, if_true, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_range'_1, Vl,
      Finset.mem_toList]
    constructor
    · rintro ⟨j, hj, u, hu, v, hv, n, ⟨hn1, hn2⟩, rfl⟩
      exact ⟨j, u, v, n, rfl, trivial, hj, hu, hv, hn1, by omega⟩
    · rintro ⟨j, u, v, n, rfl, _, hj, hu, hv, hn1, hn2⟩
      exact ⟨j, hj, u, hu, v, hv, n, ⟨hn1, by omega⟩, rfl⟩
  · simp [h]

lemma levelKeysB_length (N r : ℕ) :
    (levelKeysB S N r).length = if r ≤ S.D then 2 ^ r * S.V.card ^ 2 * N else 0 := by
  unfold levelKeysB
  by_cases h : r ≤ S.D
  · simp only [h, if_true, List.length_flatMap, List.length_map, Vl_length, List.length_range',
      List.length_range]
    simp [List.map_const', sq, mul_assoc, Vl_length]
  · simp [h]

/-- dependências de uma posição com orçamento -/
noncomputable def depsB : BKey → Finset BKey
  | (r, j, u, v, n) =>
    if r < S.D ∧ n ≠ 1 then
      (((Vl S).toFinset ×ˢ Finset.Ico 1 n).image fun p => (r + 1, 2 * j, u, p.1, p.2)) ∪
        (((Vl S).toFinset ×ˢ Finset.Ico 1 n).image fun p => (r + 1, 2 * j + 1, p.1, v, n - p.2))
    else ∅

noncomputable def memB : Mem BKey BEntry := ⟨fun _ => default, ∅⟩

/-- **A implementação densa com orçamento de folhas até `N`**. -/
noncomputable def denseRunB (N : ℕ) (leaf : LeafProg) : Tm (Mem BKey BEntry) :=
  runFrom (levelKeysB S N) (entryTmB S leaf) S.D memB

/-- tempo por entrada -/
noncomputable def cB (S : Setup) (cL : ℕ) : BKey → ℕ
  | (r, _, _, _, n) => if n = 1 then cL else if r < S.D then 4 * ((n - 1) * S.V.card) + 1 else 0

lemma mem_depsB_left {r j n : ℕ} {u v : ℚ} {p : ℕ × ℚ} (hr : r < S.D) (hp : p ∈ pairsL S n) :
    (r + 1, 2 * j, u, p.2, p.1) ∈ depsB S (r, j, u, v, n) := by
  have h := (mem_pairsL S).mp hp
  have hn : n ≠ 1 := by omega
  simp only [depsB, hr, hn, ne_eq, not_false_eq_true, and_self, if_true, Finset.mem_union,
    Finset.mem_image, Finset.mem_product, List.mem_toFinset, Finset.mem_Ico]
  exact Or.inl ⟨(p.2, p.1), ⟨by simpa [Vl] using h.2.2, h.1, h.2.1⟩, rfl⟩

lemma mem_depsB_right {r j n : ℕ} {u v : ℚ} {p : ℕ × ℚ} (hr : r < S.D) (hp : p ∈ pairsL S n) :
    (r + 1, 2 * j + 1, p.2, v, n - p.1) ∈ depsB S (r, j, u, v, n) := by
  have h := (mem_pairsL S).mp hp
  have hn : n ≠ 1 := by omega
  simp only [depsB, hr, hn, ne_eq, not_false_eq_true, and_self, if_true, Finset.mem_union,
    Finset.mem_image, Finset.mem_product, List.mem_toFinset, Finset.mem_Ico]
  exact Or.inr ⟨(p.2, p.1), ⟨by simpa [Vl] using h.2.2, h.1, h.2.1⟩, rfl⟩

theorem denseRunB_spec (N : ℕ) (leaf : LeafProg) (phiv : ℕ → ℕ → ℚ → ℚ → WithTop ℚ) (cL : ℕ)
    (hv : ∀ r j u v, (leaf r j u v).val = phiv r j u v)
    (ht : ∀ r j u v, (leaf r j u v).ticks = cL) :
    (∀ r ≤ S.D, ∀ k ∈ levelKeysB S N r, (denseRunB S N leaf).val.tab k = specB S phiv k) ∧
    (denseRunB S N leaf).val.dom =
      (Finset.range (S.D + 1)).biUnion (fun r => (levelKeysB S N r).toFinset) ∧
    (denseRunB S N leaf).ticks =
      ((List.range (S.D + 1)).map fun r =>
        ((levelKeysB S N r).map fun k => cB S cL k + 1).sum).sum := by
  have hmain := runFrom_spec (levelKeysB S N) (fun k : BKey => k.1) (entryTmB S leaf)
    (specB S phiv) (depsB S) (cB S cL) ?_ ?_ ?_ S.D memB ?_
  · obtain ⟨h1, h2, h3, h4⟩ := hmain
    refine ⟨fun r hr k hk => h1 r hr k hk, ?_, ?_⟩
    · rw [denseRunB, h3]; ext x; simp [memB]
    · rw [denseRunB, h4]
  · intro m k hdep
    obtain ⟨r, j, u, v, n⟩ := k
    refine ⟨?_, ?_⟩
    · rw [entryTmB_val]
      simp only [hv]
      by_cases hr : r < S.D
      · rw [specB_rec S phiv r j u v n hr]
        apply entryPureB_congr
        intro p hp
        exact ⟨hdep _ (mem_depsB_left S hr hp), hdep _ (mem_depsB_right S hr hp)⟩
      · have hge : S.D ≤ r := Nat.not_lt.mp hr
        rw [specB_ge S phiv hge]
        by_cases hn : n = 1 <;> simp [entryPureB, hr, hn]
    · rw [entryTmB_ticks, cB]
      by_cases hn : n = 1
      · simp [hn, ht]
      · simp [hn]
  · intro r k hk
    obtain ⟨j, u, v, n, rfl, -⟩ := (mem_levelKeysB S).mp hk
    rfl
  · intro r k hk k' hk'
    obtain ⟨j, u, v, n, rfl, hrD, hj, hu, hv', hn1, hn2⟩ := (mem_levelKeysB S).mp hk
    by_cases hr : r < S.D ∧ n ≠ 1
    · rw [depsB, if_pos hr] at hk'
      simp only [Finset.mem_union, Finset.mem_image,
        Finset.mem_product, List.mem_toFinset, Finset.mem_Ico] at hk'
      rcases hk' with ⟨⟨w, nL⟩, ⟨hw, h1, h2⟩, rfl⟩ | ⟨⟨w, nL⟩, ⟨hw, h1, h2⟩, rfl⟩
      · exact (mem_levelKeysB S).mpr ⟨2 * j, u, w, nL, rfl, by omega, by rw [pow_succ]; omega, hu,
          by simpa [Vl] using hw, h1, by omega⟩
      · exact (mem_levelKeysB S).mpr ⟨2 * j + 1, w, v, n - nL, rfl, by omega,
          by rw [pow_succ]; omega, by simpa [Vl] using hw, hv', by omega, by omega⟩
    · simp [depsB, hr] at hk'
  · intro r hr k hk
    obtain ⟨j, u, v, n, rfl, hrD, -⟩ := (mem_levelKeysB S).mp hk
    omega

/-- **Memória com orçamento**: exatamente `S_D N M²` entradas. -/
theorem denseRunB_dom_card (N : ℕ) (leaf : LeafProg) (phiv : ℕ → ℕ → ℚ → ℚ → WithTop ℚ) (cL : ℕ)
    (hv : ∀ r j u v, (leaf r j u v).val = phiv r j u v)
    (ht : ∀ r j u v, (leaf r j u v).ticks = cL) :
    (denseRunB S N leaf).val.dom.card = (2 ^ (S.D + 1) - 1) * N * S.V.card ^ 2 := by
  obtain ⟨-, hdom, -⟩ := denseRunB_spec S N leaf phiv cL hv ht
  rw [hdom]
  let φ : ((ℕ × ℕ) × ℚ × ℚ) × ℕ → BKey := fun p => (p.1.1.1, p.1.1.2, p.1.2.1, p.1.2.2, p.2)
  have hφ : Function.Injective φ := by
    rintro ⟨⟨⟨a, b⟩, c, d⟩, e⟩ ⟨⟨⟨a', b'⟩, c', d'⟩, e'⟩ h
    simp only [φ, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    rfl
  have himg : (Finset.range (S.D + 1)).biUnion (fun r => (levelKeysB S N r).toFinset) =
      ((cellsD S.D ×ˢ (S.V ×ˢ S.V)) ×ˢ Finset.Icc 1 N).image φ := by
    ext k
    simp only [Finset.mem_biUnion, Finset.mem_range, List.mem_toFinset, mem_levelKeysB,
      Finset.mem_image, Finset.mem_product, cellsD, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_Icc, φ]
    constructor
    · rintro ⟨r, hr, j, u, v, n, rfl, hrD, hj, hu, hv', hn1, hn2⟩
      exact ⟨⟨⟨(r, j), u, v⟩, n⟩, ⟨⟨⟨r, by omega, j, by simpa using hj, rfl⟩, hu, hv'⟩, hn1, hn2⟩,
        rfl⟩
    · rintro ⟨⟨⟨⟨r, j⟩, u, v⟩, n⟩, ⟨⟨⟨r', hr', j', hj', hrj⟩, hu, hv'⟩, hn1, hn2⟩, rfl⟩
      simp only [Prod.mk.injEq] at hrj
      obtain ⟨rfl, rfl⟩ := hrj
      exact ⟨r', hr', j', u, v, n, rfl, by omega, by simpa using hj', hu, hv', hn1, hn2⟩
  rw [himg, Finset.card_image_of_injective _ hφ, Finset.card_product, Finset.card_product,
    Finset.card_product, card_cellsD, Nat.card_Icc]
  simp only [Nat.add_sub_cancel]
  ring

lemma cB_le (cL N : ℕ) (k : BKey) (hk : k.2.2.2.2 ≤ N) :
    cB S cL k + 1 ≤ cL + 4 * (N * S.V.card) + 2 := by
  obtain ⟨r, j, u, v, n⟩ := k
  simp only [cB]
  split_ifs with h1 h2
  · omega
  · have : (n - 1) * S.V.card ≤ N * S.V.card := Nat.mul_le_mul_right _ (by simp at hk; omega)
    omega
  · omega

/-- **Tempo com orçamento**: `≤ S_D N M² (cL + 4 N M + 2)`. -/
theorem denseRunB_ticks_le (N : ℕ) (leaf : LeafProg) (phiv : ℕ → ℕ → ℚ → ℚ → WithTop ℚ) (cL : ℕ)
    (hv : ∀ r j u v, (leaf r j u v).val = phiv r j u v)
    (ht : ∀ r j u v, (leaf r j u v).ticks = cL) :
    (denseRunB S N leaf).ticks ≤
      (2 ^ (S.D + 1) - 1) * (S.V.card ^ 2 * N) * (cL + 4 * (N * S.V.card) + 2) := by
  obtain ⟨-, -, htk⟩ := denseRunB_spec S N leaf phiv cL hv ht
  rw [htk]
  have hlev := sum_range_pow_le (S.V.card ^ 2 * N * (cL + 4 * (N * S.V.card) + 2))
    (fun r => ((levelKeysB S N r).map fun k => cB S cL k + 1).sum) (S.D + 1) ?_
  · calc _ ≤ _ := hlev
      _ = _ := by ring
  · intro r hr
    have hr' : r ≤ S.D := by omega
    have hsum : ((levelKeysB S N r).map fun k => cB S cL k + 1).sum ≤
        (levelKeysB S N r).length * (cL + 4 * (N * S.V.card) + 2) := by
      have := List.sum_le_card_nsmul ((levelKeysB S N r).map fun k => cB S cL k + 1)
        (cL + 4 * (N * S.V.card) + 2) (by
          intro x hx
          obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
          obtain ⟨j, u, v, n, rfl, -, -, -, -, -, hn2⟩ := (mem_levelKeysB S).mp hk
          exact cB_le S cL N _ hn2)
      simpa using this
    rw [levelKeysB_length, if_pos hr'] at hsum
    calc _ ≤ _ := hsum
      _ = 2 ^ r * (S.V.card ^ 2 * N * (cL + 4 * (N * S.V.card) + 2)) := by ring

end Pendencias.DenseDP

/-!
# III.9.1 — parte 11: reconstrução com orçamento e teorema final com `N` folhas
-/

namespace Pendencias.DenseDP

open Artigo Classical Tm LTree

variable (S : Setup)

/-- reconstrução com orçamento: folha se `n = 1`; senão nó com filhos de `n_L` e `n - n_L`
folhas, seguindo o apontador `(n_L, w)` -/
noncomputable def rebuildB (tab : BKey → BEntry) : ℕ → ℕ → ℕ → ℚ → ℚ → ℕ → Option LTree
  | 0, r, j, u, v, n => if n = 1 then mkLeaf S (S.k₀ + r) (cellM S r j) u v else none
  | d + 1, r, j, u, v, n =>
      match (tab (r, j, u, v, n)).2 with
      | BPtr.leaf => if n = 1 then mkLeaf S (S.k₀ + r) (cellM S r j) u v else none
      | BPtr.split nL w => do
          let l ← rebuildB tab d (r + 1) (2 * j) u w nL
          let rr ← rebuildB tab d (r + 1) (2 * j + 1) w v (n - nL)
          some (LTree.node l rr)

theorem rebuildB_spec (hH : 2 ≤ S.H) (phiv : ℕ → ℕ → ℚ → ℚ → WithTop ℚ)
    (hphi : ∀ r j u v, phiv r j u v = S.Phi (S.k₀ + r) (cellM S r j) u v) (N : ℕ)
    (tab : BKey → BEntry)
    (htab : ∀ r j u v n, r ≤ S.D → j < 2 ^ r → u ∈ S.V → v ∈ S.V → 1 ≤ n → n ≤ N →
      tab (r, j, u, v, n) = specB S phiv (r, j, u, v, n)) :
    ∀ d r, S.D - r = d → ∀ j u v n, j < 2 ^ r → u ∈ S.V → v ∈ S.V → 1 ≤ n → n ≤ N →
      (specB S phiv (r, j, u, v, n)).1 ≠ ⊤ →
      ∃ R, rebuildB S tab d r j u v n = some R ∧
        R ∈ S.RsetN d n (S.k₀ + r) (cellM S r j) u v ∧
        S.costW R = (specB S phiv (r, j, u, v, n)).1 := by
  intro d
  induction d with
  | zero =>
      intro r hr j u v n hj hu hv hn1 hnN hfin
      have hge : S.D ≤ r := by omega
      rw [specB_ge S phiv hge] at hfin
      by_cases hn : n = 1
      · subst hn
        simp only [if_true] at hfin
        rw [hphi] at hfin
        have hp : (u, v) ∈ PH S.H (S.k₀ + r) (cellM S r j) := by
          by_contra hnot
          apply hfin
          simp only [Setup.Phi, dif_neg hnot]
        obtain ⟨R, h1, h2, h3⟩ := mkLeaf_spec S hH _ _ u v hp
        refine ⟨R, ?_, ?_, ?_⟩
        · simpa [rebuildB] using h1
        · rw [S.mem_RsetN]
          refine ⟨h2, ?_⟩
          obtain ⟨hdd, hh, hw, hlu, hlv⟩ := (S.mem_Rset).mp h2
          cases R with
          | node l r' => simp [depth] at hdd
          | leaf a => simp [numLeaves, leaves]
        · rw [specB_ge S phiv hge]; simp only [if_true, hphi]; exact h3
      · simp [hn] at hfin
  | succ d ih =>
      intro r hr j u v n hj hu hv hn1 hnN hfin
      have hlt : r < S.D := by omega
      have hkey := htab r j u v n hlt.le hj hu hv hn1 hnN
      have hrec := specB_rec S phiv r j u v n hlt
      by_cases hn : n = 1
      · subst hn
        have hspec : specB S phiv (r, j, u, v, 1) = (phiv r j u v, BPtr.leaf) := by
          rw [hrec]; simp [entryPureB]
        rw [hspec] at hfin
        simp only at hfin
        rw [hphi] at hfin
        have hp : (u, v) ∈ PH S.H (S.k₀ + r) (cellM S r j) := by
          by_contra hnot
          apply hfin
          simp only [Setup.Phi, dif_neg hnot]
        obtain ⟨R, h1, h2, h3⟩ := mkLeaf_spec S hH _ _ u v hp
        refine ⟨R, ?_, ?_, ?_⟩
        · simp [rebuildB, hkey, hspec, h1]
        · rw [S.mem_RsetN]
          obtain ⟨hdd, hh, hw, hlu, hlv⟩ := (S.mem_Rset).mp h2
          refine ⟨(S.mem_Rset).mpr ⟨by omega, hh, hw, hlu, hlv⟩, ?_⟩
          cases R with
          | node l r' => simp [depth] at hdd
          | leaf a => simp [numLeaves, leaves]
        · rw [hspec]; simp only [hphi]; exact h3
      · unfold entryPureB at hrec
        simp only [hn, if_false, hlt, if_true] at hrec
        have hptr0 := scanPure_ptr (fun p => childValB (specB S phiv) r j u v n p)
          {p : ℕ × ℚ | 1 ≤ p.1 ∧ p.1 < n ∧ p.2 ∈ S.V} (pairsL S n) (⊤, none)
          (fun p hp => (mem_pairsL S).mp hp)
          ⟨fun w h => by simp at h, fun h => absurd rfl h⟩
        generalize hsc : scanPure (fun p => childValB (specB S phiv) r j u v n p) (pairsL S n)
          (⊤, none) = sc at hrec hptr0
        have hspec : specB S phiv (r, j, u, v, n) =
            (((S.lb + S.ls : ℚ) : WithTop ℚ) + sc.1,
              BPtr.split (sc.2.getD (1, 0)).1 (sc.2.getD (1, 0)).2) := hrec
        rw [hspec] at hfin
        simp only at hfin
        have hsc1 : sc.1 ≠ ⊤ := fun h => hfin (by rw [h]; simp)
        obtain ⟨hw, hex⟩ := hptr0
        obtain ⟨⟨nL, w⟩, hw2⟩ := hex hsc1
        obtain ⟨⟨hnL1, hnL2, hwV⟩, hfw⟩ := hw (nL, w) hw2
        have hfw' : childValB (specB S phiv) r j u v n (nL, w) = sc.1 := hfw
        have hfin2 : childValB (specB S phiv) r j u v n (nL, w) ≠ ⊤ := by rw [hfw']; exact hsc1
        unfold childValB at hfin2
        simp only at hfin2
        have hc1 : (specB S phiv (r + 1, 2 * j, u, w, nL)).1 ≠ ⊤ := fun h => hfin2 (by rw [h]; simp)
        have hc2 : (specB S phiv (r + 1, 2 * j + 1, w, v, n - nL)).1 ≠ ⊤ :=
          fun h => hfin2 (by rw [h]; simp)
        simp only at hnL1 hnL2 hwV
        obtain ⟨Rl, hl1, hl2, hl3⟩ := ih (r + 1) (by omega) (2 * j) u w nL
          (by rw [pow_succ]; omega) hu hwV hnL1 (by omega) hc1
        obtain ⟨Rr, hr1, hr2, hr3⟩ := ih (r + 1) (by omega) (2 * j + 1) w v (n - nL)
          (by rw [pow_succ]; omega) hwV hv (by omega) (by omega) hc2
        rw [cellM_left] at hl2
        rw [cellM_right] at hr2
        have hgetD : sc.2.getD (1, 0) = (nL, w) := by rw [hw2]; rfl
        refine ⟨LTree.node Rl Rr, ?_, ?_, ?_⟩
        · simp only [rebuildB, hkey, hspec, hgetD, hl1, hr1]
          rfl
        · rw [S.mem_RsetN] at hl2 hr2 ⊢
          obtain ⟨hl2', hln⟩ := hl2
          obtain ⟨hr2', hrn⟩ := hr2
          rw [S.mem_Rset] at hl2' hr2'
          obtain ⟨d1, h1, w1, lv1, rv1⟩ := hl2'
          obtain ⟨d2, h2, w2, lv2, rv2⟩ := hr2'
          refine ⟨(S.mem_Rset).mpr ⟨?_, (maxHeight_node _ _).mpr ⟨h1, h2⟩,
            ⟨w1, w2, by rw [rv1, lv2]⟩, ?_, ?_⟩, ?_⟩
          · simp only [depth]; omega
          · simpa [LTree.lval] using lv1
          · simpa [LTree.rval] using rv2
          · simp only [numLeaves_node]; omega
        · rw [S.costW_node, hl3, hr3, hspec]
          simp only
          rw [← hfw']
          unfold childValB
          rw [add_comm]

end Pendencias.DenseDP

/-!
# III.9.1 — parte 12: teorema com orçamento de até `N` folhas (custos de folha pré-computados)
-/

namespace Pendencias.DenseDP

open Artigo Classical Tm LTree

variable (S : Setup)

/-- **Teorema III.9.1 (orçamento de folhas)**. A implementação densa com orçamento
`denseRunB S N (leafPre S)` satisfaz:
(a) a entrada `(r,j,u,v,n)` guarda `C_{D-r,n}(J_{r,j};u,v)` (`Cb`), `1 ≤ n ≤ N`;
(b) a memória usa exatamente `S_D N M²` entradas;
(c) o número de operações é `≤ S_D N M² (4NM + 3) ≤ 7 S_D N² M³`;
(d) os apontadores `(n_L, w)` reconstroem uma representação com exatamente `n` folhas e custo
`C_{D,n}(K;u,v)` quando este é finito. -/
theorem dense_budget_complexity (hH : 2 ≤ S.H) (N : ℕ) :
    (∀ r j u v n, r ≤ S.D → j < 2 ^ r → u ∈ S.V → v ∈ S.V → 1 ≤ n → n ≤ N →
      ((denseRunB S N (leafPre S)).val.tab (r, j, u, v, n)).1 =
        S.Cb (S.D - r) n (S.k₀ + r) (cellM S r j) u v) ∧
    (denseRunB S N (leafPre S)).val.dom.card = (2 ^ (S.D + 1) - 1) * N * S.V.card ^ 2 ∧
    (denseRunB S N (leafPre S)).ticks ≤
      (2 ^ (S.D + 1) - 1) * (S.V.card ^ 2 * N) * (4 * (N * S.V.card) + 3) ∧
    (denseRunB S N (leafPre S)).ticks ≤ 7 * (2 ^ (S.D + 1) - 1) * N ^ 2 * S.V.card ^ 3 ∧
    (∀ u v n, u ∈ S.V → v ∈ S.V → 1 ≤ n → n ≤ N → S.Cb S.D n S.k₀ S.m₀ u v ≠ ⊤ →
      ∃ R, rebuildB S (denseRunB S N (leafPre S)).val.tab S.D 0 0 u v n = some R ∧
        R ∈ S.RsetN S.D n S.k₀ S.m₀ u v ∧ S.costW R = S.Cb S.D n S.k₀ S.m₀ u v) := by
  set phiv : ℕ → ℕ → ℚ → ℚ → WithTop ℚ := fun r j u v => S.Phi (S.k₀ + r) (cellM S r j) u v
    with hphiv
  have hv : ∀ r j u v, (leafPre S r j u v).val = phiv r j u v := fun r j u v => rfl
  have ht : ∀ r j u v, (leafPre S r j u v).ticks = 1 := fun r j u v => rfl
  have hphi : ∀ r j u v, phiv r j u v = S.Phi (S.k₀ + r) (cellM S r j) u v := fun _ _ _ _ => rfl
  obtain ⟨hspec, -, -⟩ := denseRunB_spec S N (leafPre S) phiv 1 hv ht
  have htab : ∀ r j u v n, r ≤ S.D → j < 2 ^ r → u ∈ S.V → v ∈ S.V → 1 ≤ n → n ≤ N →
      (denseRunB S N (leafPre S)).val.tab (r, j, u, v, n) = specB S phiv (r, j, u, v, n) := by
    intro r j u v n hr hj hu hv' hn1 hn2
    exact hspec r hr _ ((mem_levelKeysB S).mpr ⟨j, u, v, n, rfl, hr, hj, hu, hv', hn1, hn2⟩)
  have hcost : ∀ r j u v n, (specB S phiv (r, j, u, v, n)).1 =
      S.Cb (S.D - r) n (S.k₀ + r) (cellM S r j) u v := by
    intro r j u v n
    exact specEB_cost S phiv hphi (S.D - r) r rfl j u v n
  have hticks := denseRunB_ticks_le S N (leafPre S) phiv 1 hv ht
  refine ⟨?_, denseRunB_dom_card S N (leafPre S) phiv 1 hv ht, ?_, ?_, ?_⟩
  · intro r j u v n hr hj hu hv' hn1 hn2
    rw [htab r j u v n hr hj hu hv' hn1 hn2, hcost]
  · calc _ ≤ _ := hticks
      _ = _ := by ring_nf
  · refine hticks.trans ?_
    by_cases hM : S.V.card = 0
    · simp [hM]
    · by_cases hN : N = 0
      · simp [hN]
      · have h1 : 1 ≤ S.V.card := Nat.one_le_iff_ne_zero.mpr hM
        have h2 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
        have hle : S.V.card ^ 2 * N ≤ N ^ 2 * S.V.card ^ 3 := by
          calc S.V.card ^ 2 * N = N * S.V.card ^ 2 * 1 := by ring
            _ ≤ N * S.V.card ^ 2 * (N * S.V.card) :=
                Nat.mul_le_mul le_rfl (Nat.mul_le_mul h2 h1)
            _ = N ^ 2 * S.V.card ^ 3 := by ring
        have : S.V.card ^ 2 * N * (1 + 4 * (N * S.V.card) + 2) ≤ 7 * (N ^ 2 * S.V.card ^ 3) := by
          nlinarith [hle]
        calc (2 ^ (S.D + 1) - 1) * (S.V.card ^ 2 * N) * (1 + 4 * (N * S.V.card) + 2)
            = (2 ^ (S.D + 1) - 1) * (S.V.card ^ 2 * N * (1 + 4 * (N * S.V.card) + 2)) := by ring
          _ ≤ (2 ^ (S.D + 1) - 1) * (7 * (N ^ 2 * S.V.card ^ 3)) := Nat.mul_le_mul le_rfl this
          _ = 7 * (2 ^ (S.D + 1) - 1) * N ^ 2 * S.V.card ^ 3 := by ring
  · intro u v n hu hv' hn1 hn2 hfin
    have hroot := hcost 0 0 u v n
    have hcell : cellM S 0 0 = S.m₀ := by simp [cellM]
    have hfin' : (specB S phiv (0, 0, u, v, n)).1 ≠ ⊤ := by
      rw [hroot]; simpa [hcell] using hfin
    obtain ⟨R, h1, h2, h3⟩ := rebuildB_spec S hH phiv hphi N _ htab S.D 0 (by simp) 0 u v n
      (by simp) hu hv' hn1 hn2 hfin'
    refine ⟨R, h1, ?_, ?_⟩
    · simpa [hcell] using h2
    · rw [h3, hroot]; simp [hcell]

end Pendencias.DenseDP

/-!
# III.9.1 — parte 13: custo local calculado diretamente sobre as `P` observações
-/

namespace Pendencias.DenseDP

open Artigo Classical Tm LTree

variable (S : Setup)

/-- Perda local `loss(J_{k,m};u,v)` calculada diretamente: para cada observação, 4 operações
(teste de posse, diferença com a reta, quadrado e produto, acumulação). -/
noncomputable def lossTm (k : ℕ) (m : ℤ) (u v : ℚ) : List (ℚ × ℚ × ℚ) → ℚ → Tm ℚ
  | [], acc => pure acc
  | p :: ps, acc => do
      tick 4
      lossTm k m u v ps
        (if S.owns k m p.1 then acc + p.2.2 * (p.2.1 - lineJ k m u v p.1) ^ 2 else acc)

lemma lossTm_val (k : ℕ) (m : ℤ) (u v : ℚ) : ∀ (ps : List (ℚ × ℚ × ℚ)) (acc : ℚ),
    (lossTm S k m u v ps acc).val = acc + ((ps.filter fun p => S.owns k m p.1).map fun p =>
      p.2.2 * (p.2.1 - lineJ k m u v p.1) ^ 2).sum
  | [], acc => by simp [lossTm]
  | p :: ps, acc => by
      show (lossTm S k m u v ps _).val = _
      rw [lossTm_val k m u v ps]
      by_cases h : S.owns k m p.1
      · simp [List.filter_cons, h]; ring
      · simp [List.filter_cons, h]

lemma lossTm_ticks (k : ℕ) (m : ℤ) (u v : ℚ) : ∀ (ps : List (ℚ × ℚ × ℚ)) (acc : ℚ),
    (lossTm S k m u v ps acc).ticks = 4 * ps.length
  | [], acc => by simp [lossTm]
  | p :: ps, acc => by
      show 4 + (lossTm S k m u v ps _).ticks = _
      rw [lossTm_ticks k m u v ps]; simp [List.length_cons]; ring

/-- custo de folha calculado sobre os dados. Estado admissível `(u,v) ∈ 𝒫_H(J)`: perda local
(`4P` operações) mais 3 operações (comprimento do código, soma). Estado não admissível: o custo é
`+∞` e cobra-se, como cota superior, o mesmo orçamento `4P + 3` sem efetuar aritmética sobre os
dados (assim nenhum operando cresce fora das células admissíveis). -/
noncomputable def leafInit : LeafProg := fun r j u v =>
  if h : (u, v) ∈ PH S.H (S.k₀ + r) (cellM S r j) then do
    let l ← lossTm S (S.k₀ + r) (cellM S r j) u v S.data 0
    tick 3
    pure (((l + S.lb * (1 + (gamma (nSharp (Atom.ofEndpoints (S.k₀ + r) (cellM S r j) u v
      (mem_PH.mp h).1) + 1)).length) : ℚ) : WithTop ℚ))
  else do
    tick (4 * S.data.length + 3)
    pure ⊤

lemma leafInit_val (r j : ℕ) (u v : ℚ) :
    (leafInit S r j u v).val = S.Phi (S.k₀ + r) (cellM S r j) u v := by
  unfold leafInit
  by_cases h : (u, v) ∈ PH S.H (S.k₀ + r) (cellM S r j)
  · rw [dif_pos h]
    show (((lossTm S (S.k₀ + r) (cellM S r j) u v S.data 0).val + S.lb * (1 + (gamma (nSharp
      (Atom.ofEndpoints (S.k₀ + r) (cellM S r j) u v (mem_PH.mp h).1) + 1)).length) : ℚ) :
        WithTop ℚ) = _
    rw [lossTm_val, zero_add]
    simp only [Setup.Phi, dif_pos h]
    rfl
  · rw [dif_neg h]
    simp only [Setup.Phi, dif_neg h]
    rfl

lemma leafInit_ticks (r j : ℕ) (u v : ℚ) :
    (leafInit S r j u v).ticks = 4 * S.data.length + 3 := by
  unfold leafInit
  by_cases h : (u, v) ∈ PH S.H (S.k₀ + r) (cellM S r j)
  · rw [dif_pos h]
    show (lossTm S (S.k₀ + r) (cellM S r j) u v S.data 0).ticks + (3 + 0) = _
    rw [lossTm_ticks]
  · rw [dif_neg h]
    show 4 * S.data.length + 3 + 0 = _
    rfl

end Pendencias.DenseDP

/-!
# III.9.1 — parte 14: inicialização direta sobre `P` observações (árvore variável)
-/

namespace Pendencias.DenseDP

open Artigo Classical Tm LTree

variable (S : Setup)

/-- **III.9.1, inicialização sobre `P` observações**. Com os custos de folha calculados
diretamente sobre os dados (`leafInit`, `4P + 3` operações por posição), a mesma tabela
(custos `Cvar`, apontadores, memória `S_D M²`) é obtida, e o número de operações é
`≤ S_D M² (4M + 6) + 4 S_D P M²`: o termo de inicialização é `4 S_D P M² = O(S_D P M²)`. -/
theorem dense_variable_init (hH : 2 ≤ S.H) :
    (∀ r j u v, r ≤ S.D → j < 2 ^ r → u ∈ S.V → v ∈ S.V →
      ((denseRun S (leafInit S)).val.tab (r, j, u, v)).1 =
        S.Cvar (S.D - r) (S.k₀ + r) (cellM S r j) u v) ∧
    (denseRun S (leafInit S)).val.dom.card = (2 ^ (S.D + 1) - 1) * S.V.card ^ 2 ∧
    (denseRun S (leafInit S)).ticks ≤
      (2 ^ (S.D + 1) - 1) * S.V.card ^ 2 * (4 * S.V.card + 6) +
        4 * ((2 ^ (S.D + 1) - 1) * S.data.length * S.V.card ^ 2) ∧
    (∀ u v, u ∈ S.V → v ∈ S.V → S.Cvar S.D S.k₀ S.m₀ u v ≠ ⊤ →
      ∃ R, rebuild S (denseRun S (leafInit S)).val.tab S.D 0 0 u v = some R ∧
        R ∈ S.Rset S.D S.k₀ S.m₀ u v ∧ S.costW R = S.Cvar S.D S.k₀ S.m₀ u v) := by
  set phiv : ℕ → ℕ → ℚ → ℚ → WithTop ℚ := fun r j u v => S.Phi (S.k₀ + r) (cellM S r j) u v
    with hphiv
  have hv : ∀ r j u v, (leafInit S r j u v).val = phiv r j u v := fun r j u v => leafInit_val S r j u v
  have ht : ∀ r j u v, (leafInit S r j u v).ticks = 4 * S.data.length + 3 :=
    fun r j u v => leafInit_ticks S r j u v
  have hphi : ∀ r j u v, phiv r j u v = S.Phi (S.k₀ + r) (cellM S r j) u v := fun _ _ _ _ => rfl
  obtain ⟨hspec, -, -⟩ := denseRun_spec S (leafInit S) phiv _ hv ht
  have htab : ∀ r j u v, r ≤ S.D → j < 2 ^ r → u ∈ S.V → v ∈ S.V →
      (denseRun S (leafInit S)).val.tab (r, j, u, v) = spec S phiv (r, j, u, v) := by
    intro r j u v hr hj hu hv'
    exact hspec r hr _ ((mem_levelKeys S).mpr ⟨j, u, v, rfl, hr, hj, hu, hv'⟩)
  have hcost : ∀ r j u v, r ≤ S.D → j < 2 ^ r → u ∈ S.V → v ∈ S.V →
      (spec S phiv (r, j, u, v)).1 = S.Cvar (S.D - r) (S.k₀ + r) (cellM S r j) u v := by
    intro r j u v hr hj hu hv'
    exact specE_cost S phiv hphi (S.D - r) r rfl j u v
  refine ⟨?_, denseRun_dom_card S (leafInit S) phiv _ hv ht, ?_, ?_⟩
  · intro r j u v hr hj hu hv'
    rw [htab r j u v hr hj hu hv', hcost r j u v hr hj hu hv']
  · have := denseRun_ticks_le S (leafInit S) phiv _ hv ht
    refine this.trans ?_
    apply le_of_eq
    ring
  · intro u v hu hv' hfin
    have hroot := hcost 0 0 u v (Nat.zero_le _) (by simp) hu hv'
    have hcell : cellM S 0 0 = S.m₀ := by simp [cellM]
    have hfin' : (spec S phiv (0, 0, u, v)).1 ≠ ⊤ := by
      rw [hroot]; simpa [hcell] using hfin
    obtain ⟨R, h1, h2, h3⟩ := rebuild_spec S hH phiv hphi _ htab S.D 0 (by simp) 0 u v
      (by simp) hu hv' hfin'
    refine ⟨R, h1, ?_, ?_⟩
    · simpa [hcell] using h2
    · rw [h3, hroot]; simp [hcell]

end Pendencias.DenseDP

/-!
# III.9.1 — parte 15: orçamento de folhas com o custo de folha separado do resto

O custo de folha é lido apenas nas posições `n = 1`: o termo `cL` aparece `S_D M²` vezes.
-/

namespace Pendencias.DenseDP

open Artigo Classical Tm LTree

variable (S : Setup)

lemma sum_ite_eq_mul_countP {α : Type} (l : List α) (p : α → Prop) [DecidablePred p] (c : ℕ) :
    (l.map fun x => if p x then c else 0).sum = c * l.countP (fun x => decide (p x)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      by_cases h : p a
      · simp [List.countP_cons, h, ih]; ring
      · simp [List.countP_cons, h, ih]

lemma countP_n1 (N r : ℕ) (hN : 1 ≤ N) (hr : r ≤ S.D) :
    (levelKeysB S N r).countP (fun k => decide (k.2.2.2.2 = 1)) = 2 ^ r * S.V.card ^ 2 := by
  unfold levelKeysB
  simp only [hr, if_true, List.countP_flatMap, List.countP_map, Function.comp_def, Vl_length]
  have h1 : (List.range' 1 N).countP (fun n => decide (n = 1)) = 1 := by
    rw [List.countP_eq_length_filter]
    have : (List.range' 1 N).filter (fun n => decide (n = 1)) = [1] := by
      obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
      rw [List.range'_succ, List.filter_cons_of_pos (by simp)]
      have : (List.range' (1 + 1) N').filter (fun n => decide (n = 1)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro a ha
        have := (List.mem_range'_1.mp ha).1
        simp; omega
      rw [this]
    simp [this]
  simp only [h1]
  simp [List.map_const', sq, mul_assoc, Vl_length]


/-- **Tempo com orçamento, custo de folha separado**: `≤ S_D (cL M² + M² N (4NM+2))`;
o custo de folha `cL` é pago apenas `S_D M²` vezes (posições com `n = 1`). -/
theorem denseRunB_ticks_le' (N : ℕ) (leaf : LeafProg) (phiv : ℕ → ℕ → ℚ → ℚ → WithTop ℚ) (cL : ℕ)
    (hv : ∀ r j u v, (leaf r j u v).val = phiv r j u v)
    (ht : ∀ r j u v, (leaf r j u v).ticks = cL) :
    (denseRunB S N leaf).ticks ≤
      (2 ^ (S.D + 1) - 1) * (cL * S.V.card ^ 2 + S.V.card ^ 2 * N * (4 * (N * S.V.card) + 2)) := by
  obtain ⟨-, -, htk⟩ := denseRunB_spec S N leaf phiv cL hv ht
  rw [htk]
  have hlev := sum_range_pow_le (cL * S.V.card ^ 2 + S.V.card ^ 2 * N * (4 * (N * S.V.card) + 2))
    (fun r => ((levelKeysB S N r).map fun k => cB S cL k + 1).sum) (S.D + 1) ?_
  · exact hlev
  · intro r hr
    have hr' : r ≤ S.D := by omega
    by_cases hN : N = 0
    · have : levelKeysB S N r = [] := by
        apply List.length_eq_zero_iff.mp
        rw [levelKeysB_length, if_pos hr', hN]; simp
      simp [this]
    · have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
      have hpt : ∀ k ∈ levelKeysB S N r, cB S cL k + 1 ≤
          (if k.2.2.2.2 = 1 then cL else 0) + (4 * (N * S.V.card) + 2) := by
        intro k hk
        obtain ⟨j, u, v, n, rfl, -, -, -, -, -, hn2⟩ := (mem_levelKeysB S).mp hk
        simp only [cB]
        by_cases h1 : n = 1
        · simp [h1] <;> omega
        · by_cases h2 : r < S.D
          · have : (n - 1) * S.V.card ≤ N * S.V.card := Nat.mul_le_mul_right _ (by omega)
            simp [h1, h2] <;> omega
          · simp [h1, h2]
      have h1 := List.sum_le_sum hpt
      have hsplit : ((levelKeysB S N r).map fun k =>
          (if k.2.2.2.2 = 1 then cL else 0) + (4 * (N * S.V.card) + 2)).sum =
          ((levelKeysB S N r).map fun k => if k.2.2.2.2 = 1 then cL else 0).sum +
            ((levelKeysB S N r).map fun _ => 4 * (N * S.V.card) + 2).sum :=
        List.sum_map_add
      have h2 := sum_ite_eq_mul_countP (levelKeysB S N r) (fun k => k.2.2.2.2 = 1) cL
      have h3 := countP_n1 S N r hN1 hr'
      have h4 : ((levelKeysB S N r).map fun _ => 4 * (N * S.V.card) + 2).sum =
          (levelKeysB S N r).length * (4 * (N * S.V.card) + 2) := by
        simp [List.map_const', List.sum_replicate]
      rw [hsplit, h4, levelKeysB_length, if_pos hr', h2, h3] at h1
      calc _ ≤ _ := h1
        _ = 2 ^ r * (cL * S.V.card ^ 2 + S.V.card ^ 2 * N * (4 * (N * S.V.card) + 2)) := by ring

end Pendencias.DenseDP

/-!
# III.9.1 — parte 16: orçamento com inicialização direta e enunciado final
-/

namespace Pendencias.DenseDP

open Artigo Classical Tm LTree

variable (S : Setup)

/-- **III.9.1, orçamento com inicialização sobre `P` observações**: a mesma tabela (`Cb`,
apontadores, `S_D N M²` entradas) com `≤ S_D M² (4P+3) + S_D M² N (4NM+2)` operações; o termo de
inicialização `S_D M² (4P+3) = O(S_D P M²)` não é multiplicado por `N`. -/
theorem dense_budget_init (hH : 2 ≤ S.H) (N : ℕ) :
    (∀ r j u v n, r ≤ S.D → j < 2 ^ r → u ∈ S.V → v ∈ S.V → 1 ≤ n → n ≤ N →
      ((denseRunB S N (leafInit S)).val.tab (r, j, u, v, n)).1 =
        S.Cb (S.D - r) n (S.k₀ + r) (cellM S r j) u v) ∧
    (denseRunB S N (leafInit S)).val.dom.card = (2 ^ (S.D + 1) - 1) * N * S.V.card ^ 2 ∧
    (denseRunB S N (leafInit S)).ticks ≤
      (2 ^ (S.D + 1) - 1) * ((4 * S.data.length + 3) * S.V.card ^ 2) +
        (2 ^ (S.D + 1) - 1) * (S.V.card ^ 2 * N * (4 * (N * S.V.card) + 2)) ∧
    (∀ u v n, u ∈ S.V → v ∈ S.V → 1 ≤ n → n ≤ N → S.Cb S.D n S.k₀ S.m₀ u v ≠ ⊤ →
      ∃ R, rebuildB S (denseRunB S N (leafInit S)).val.tab S.D 0 0 u v n = some R ∧
        R ∈ S.RsetN S.D n S.k₀ S.m₀ u v ∧ S.costW R = S.Cb S.D n S.k₀ S.m₀ u v) := by
  set phiv : ℕ → ℕ → ℚ → ℚ → WithTop ℚ := fun r j u v => S.Phi (S.k₀ + r) (cellM S r j) u v
    with hphiv
  have hv : ∀ r j u v, (leafInit S r j u v).val = phiv r j u v := fun r j u v => leafInit_val S r j u v
  have ht : ∀ r j u v, (leafInit S r j u v).ticks = 4 * S.data.length + 3 :=
    fun r j u v => leafInit_ticks S r j u v
  have hphi : ∀ r j u v, phiv r j u v = S.Phi (S.k₀ + r) (cellM S r j) u v := fun _ _ _ _ => rfl
  obtain ⟨hspec, -, -⟩ := denseRunB_spec S N (leafInit S) phiv _ hv ht
  have htab : ∀ r j u v n, r ≤ S.D → j < 2 ^ r → u ∈ S.V → v ∈ S.V → 1 ≤ n → n ≤ N →
      (denseRunB S N (leafInit S)).val.tab (r, j, u, v, n) = specB S phiv (r, j, u, v, n) := by
    intro r j u v n hr hj hu hv' hn1 hn2
    exact hspec r hr _ ((mem_levelKeysB S).mpr ⟨j, u, v, n, rfl, hr, hj, hu, hv', hn1, hn2⟩)
  have hcost : ∀ r j u v n, (specB S phiv (r, j, u, v, n)).1 =
      S.Cb (S.D - r) n (S.k₀ + r) (cellM S r j) u v := by
    intro r j u v n
    exact specEB_cost S phiv hphi (S.D - r) r rfl j u v n
  refine ⟨?_, denseRunB_dom_card S N (leafInit S) phiv _ hv ht, ?_, ?_⟩
  · intro r j u v n hr hj hu hv' hn1 hn2
    rw [htab r j u v n hr hj hu hv' hn1 hn2, hcost]
  · have := denseRunB_ticks_le' S N (leafInit S) phiv _ hv ht
    refine this.trans (le_of_eq ?_)
    ring
  · intro u v n hu hv' hn1 hn2 hfin
    have hroot := hcost 0 0 u v n
    have hcell : cellM S 0 0 = S.m₀ := by simp [cellM]
    have hfin' : (specB S phiv (0, 0, u, v, n)).1 ≠ ⊤ := by
      rw [hroot]; simpa [hcell] using hfin
    obtain ⟨R, h1, h2, h3⟩ := rebuildB_spec S hH phiv hphi N _ htab S.D 0 (by simp) 0 u v n
      (by simp) hu hv' hn1 hn2 hfin'
    refine ⟨R, h1, ?_, ?_⟩
    · simpa [hcell] using h2
    · rw [h3, hroot]; simp [hcell]

/-- **Teorema III.9.1 (complexidade em número de estados)** — enunciado formal reunido.
`M = |𝒱_{D,H}(K)|`, `S_D = 2^{D+1} - 1`, `P = |dados|`. Para a implementação densa
(programação dinâmica ascendente com memoização e apontadores de reconstrução):
1. (custos de folha pré-computados) a tabela usa `S_D M²` entradas e `≤ 8 S_D M³` operações;
2. (orçamento até `N` folhas) usa `S_D N M²` entradas e `≤ 7 S_D N² M³` operações;
3. (custos locais sobre `P` observações) a inicialização acrescenta `O(S_D P M²)` operações
   (`4 S_D P M²` na árvore variável e `S_D M² (4P+3)` com orçamento);
4. as tabelas guardam `Cvar` / `Cb`, e os apontadores reconstroem uma representação ótima. -/
theorem state_complexity_dense (hH : 2 ≤ S.H) (N : ℕ) :
    ((denseRun S (leafPre S)).val.dom.card = (2 ^ (S.D + 1) - 1) * S.V.card ^ 2 ∧
      (denseRun S (leafPre S)).ticks ≤ 8 * (2 ^ (S.D + 1) - 1) * S.V.card ^ 3) ∧
    ((denseRunB S N (leafPre S)).val.dom.card = (2 ^ (S.D + 1) - 1) * N * S.V.card ^ 2 ∧
      (denseRunB S N (leafPre S)).ticks ≤ 7 * (2 ^ (S.D + 1) - 1) * N ^ 2 * S.V.card ^ 3) ∧
    ((denseRun S (leafInit S)).val.dom.card = (2 ^ (S.D + 1) - 1) * S.V.card ^ 2 ∧
      (denseRun S (leafInit S)).ticks ≤
        (2 ^ (S.D + 1) - 1) * S.V.card ^ 2 * (4 * S.V.card + 6) +
          4 * ((2 ^ (S.D + 1) - 1) * S.data.length * S.V.card ^ 2)) ∧
    ((denseRunB S N (leafInit S)).val.dom.card = (2 ^ (S.D + 1) - 1) * N * S.V.card ^ 2 ∧
      (denseRunB S N (leafInit S)).ticks ≤
        (2 ^ (S.D + 1) - 1) * ((4 * S.data.length + 3) * S.V.card ^ 2) +
          (2 ^ (S.D + 1) - 1) * (S.V.card ^ 2 * N * (4 * (N * S.V.card) + 2))) := by
  obtain ⟨-, a2, -, a4, -⟩ := dense_variable_complexity S hH
  obtain ⟨-, b2, -, b4, -⟩ := dense_budget_complexity S hH N
  obtain ⟨-, c2, c3, -⟩ := dense_variable_init S hH
  obtain ⟨-, d2, d3, -⟩ := dense_budget_init S hH N
  exact ⟨⟨a2, a4⟩, ⟨b2, b4⟩, ⟨c2, c3⟩, ⟨d2, d3⟩⟩

end Pendencias.DenseDP

