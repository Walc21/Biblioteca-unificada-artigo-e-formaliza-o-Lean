import RequestProject.Catalog

/-!
# III.3.25 — enumeração exata do catálogo (programa certificado)

* `gen H D k m` (computável): gera recursivamente as representações de profundidade relativa
  `≤ D` em `J_{k,m}`, listando nas folhas só os átomos de `𝓛_H` com o suporte exigido e
  descartando, ao unir duas subárvores, os pares cujos valores na fronteira diferem;
  `gen_eq_RepCat`: o resultado é exatamente o catálogo `𝔑_{D,H}(K)` (`RepCat`).
* `select Jq s` (computável): percorre o catálogo guardando o melhor elemento para a chave
  lexicográfica `(Jq R, canKey R)` — o objetivo avaliado em aritmética racional exata e, em caso
  de empate, o menor fluxo `ser♯` em shortlex (`canKey`).
* `enumSelect_eq_canon`: se `Jq` avalia exatamente `𝒥 ∘ Eval` nas representações, o programa
  devolve o minimizador canônico `canon` de `finite_catalog_minimizer` (III.3.19).
-/

namespace Pendencias

open Artigo LTree

/-! ## Geração -/

/-- gerador recursivo do catálogo (computável) -/
def gen (H : ℕ) : ℕ → ℕ → ℤ → Finset LTree
  | 0, k, m => ((LH H).filter (fun a => a.k = k ∧ a.m = m)).image LTree.leaf
  | D + 1, k, m => ((LH H).filter (fun a => a.k = k ∧ a.m = m)).image LTree.leaf ∪
      (((gen H D (k + 1) (2 * m)) ×ˢ (gen H D (k + 1) (2 * m + 1))).filter
        (fun p => p.1.rval = p.2.lval)).image (fun p => LTree.node p.1 p.2)

lemma mem_gen {H : ℕ} : ∀ (D k : ℕ) (m : ℤ) (T : LTree),
    T ∈ gen H D k m ↔ WF k m T ∧ T.depth ≤ D ∧ ∀ a ∈ T.leaves, a.height ≤ H := by
  intro D
  induction D with
  | zero =>
      intro k m T
      cases T with
      | leaf a => simp [gen, WF, LTree.depth, LTree.leaves, mem_LH]; tauto
      | node l r => simp [gen, LTree.depth]
  | succ D ih =>
      intro k m T
      cases T with
      | leaf a => simp [gen, WF, LTree.depth, LTree.leaves, mem_LH]; tauto
      | node l r =>
          simp only [gen, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_product,
            Prod.exists, reduceCtorEq, and_false, exists_false, false_or, LTree.node.injEq, WF,
            LTree.depth, LTree.leaves, List.mem_append]
          constructor
          · rintro ⟨l', r', ⟨⟨hl, hr⟩, hc⟩, rfl, rfl⟩
            rw [ih] at hl hr
            exact ⟨⟨hl.1, hr.1, hc⟩, by omega, fun a ha => ha.elim (hl.2.2 a) (hr.2.2 a)⟩
          · rintro ⟨⟨hwl, hwr, hc⟩, hd, hh⟩
            exact ⟨l, r, ⟨⟨(ih _ _ _).mpr ⟨hwl, by omega, fun a ha => hh a (Or.inl ha)⟩,
              (ih _ _ _).mpr ⟨hwr, by omega, fun a ha => hh a (Or.inr ha)⟩⟩, hc⟩, rfl, rfl⟩

/-- o gerador produz exatamente o catálogo representado -/
theorem gen_eq_RepCat (H D k : ℕ) (m : ℤ) : gen H D k m = RepCat H D k m := by
  ext T
  rw [mem_gen, mem_RepCat, maxHeight_le_iff]

/-! ## Seleção -/

section select

variable (Jq : LTree → ℚ)

/-- chave lexicográfica `(𝒥, ser♯)` -/
def key (R : LTree) : ℚ ×ₗ ℕ := toLex (Jq R, canKey R)

lemma key_injective : Function.Injective (key Jq) := by
  intro a b h
  have := congrArg (fun x => (ofLex x).2) h
  exact canKey_injective this

/-- o melhor de dois -/
def best (a b : LTree) : LTree := if key Jq a ≤ key Jq b then a else b

lemma key_best (a b : LTree) : key Jq (best Jq a b) = min (key Jq a) (key Jq b) := by
  unfold best
  split_ifs with h
  · exact (min_eq_left h).symm
  · exact (min_eq_right (le_of_not_ge h)).symm

lemma best_mem (a b : LTree) : best Jq a b = a ∨ best Jq a b = b := by
  unfold best; split_ifs <;> simp

/-- passo do percurso -/
def obest : Option LTree → Option LTree → Option LTree
  | none, x => x
  | x, none => x
  | some a, some b => some (best Jq a b)

instance : Std.Commutative (obest Jq) where
  comm x y := by
    rcases x with _ | a <;> rcases y with _ | b <;> simp only [obest]
    exact congrArg some (key_injective Jq (by rw [key_best, key_best, min_comm]))

instance : Std.Associative (obest Jq) where
  assoc x y z := by
    rcases x with _ | a <;> rcases y with _ | b <;> rcases z with _ | c <;> simp only [obest]
    exact congrArg some (key_injective Jq (by simp only [key_best, min_assoc]))

/-- percurso do catálogo (computável) -/
def select (s : Finset LTree) : Option LTree := s.fold (obest Jq) none some

lemma select_spec : ∀ s : Finset LTree, s.Nonempty →
    ∃ R, select Jq s = some R ∧ R ∈ s ∧ ∀ R' ∈ s, key Jq R ≤ key Jq R' := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro h; exact absurd h Finset.not_nonempty_empty
  | insert a s ha ih =>
      intro _
      unfold select
      rw [Finset.fold_insert ha]
      rcases s.eq_empty_or_nonempty with rfl | hs
      · refine ⟨a, by simp [obest], Finset.mem_insert_self a ∅, fun R' hR' => ?_⟩
        simp at hR'; rw [hR']
      · obtain ⟨R0, h0, hR0, hmin⟩ := ih hs
        unfold select at h0
        rw [h0]
        refine ⟨best Jq a R0, rfl, ?_, fun R' hR' => ?_⟩
        · rcases best_mem Jq a R0 with h | h <;> rw [h]
          · exact Finset.mem_insert_self a s
          · exact Finset.mem_insert_of_mem hR0
        · rw [key_best]
          rcases Finset.mem_insert.mp hR' with rfl | hR'
          · exact min_le_left _ _
          · exact (min_le_right _ _).trans (hmin R' hR')

end select

/-- **Algoritmo III.3.25**: enumeração exata e seleção canônica -/
def enumSelect (H D k : ℕ) (m : ℤ) (Jq : LTree → ℚ) : Option LTree := select Jq (gen H D k m)

/-- **Correção do algoritmo III.3.25**: se `Jq` avalia `𝒥 ∘ Eval` exatamente em ℚ nas
representações do catálogo e `H ≥ H_K`, o programa devolve o minimizador canônico. -/
theorem enumSelect_eq_canon {H D k : ℕ} {m : ℤ} (hH : HK k m ≤ H)
    (J : (cellIcc k m → ℝ) → ℝ) (Jq : LTree → ℚ)
    (hJ : ∀ R ∈ RepCat H D k m, (Jq R : ℝ) = J (evalK k m R)) :
    enumSelect H D k m Jq = some (canon H D k m J) := by
  have hne : (gen H D k m).Nonempty := ⟨_, (gen_eq_RepCat H D k m) ▸ rootLeaf_mem hH⟩
  obtain ⟨R, hsel, hmem, hmin⟩ := select_spec Jq _ hne
  rw [gen_eq_RepCat] at hmem hmin
  unfold enumSelect
  rw [hsel]
  congr 1
  have hle : ∀ R', key Jq R ≤ key Jq R' → Jq R ≤ Jq R' := by
    intro R' h
    rcases (Prod.Lex.le_iff).mp h with h | ⟨h, -⟩
    · exact h.le
    · exact h.le
  apply canon_unique hH J
  · refine mem_minSet.mpr ⟨hmem, fun R' hR' => ?_⟩
    rw [← hJ R hmem, ← hJ R' hR']
    exact_mod_cast hle R' (hmin R' hR')
  · intro R' hR'
    obtain ⟨hR'mem, hR'min⟩ := mem_minSet.mp hR'
    have h1 : (Jq R' : ℝ) ≤ Jq R := by rw [hJ R' hR'mem, hJ R hmem]; exact hR'min R hmem
    have h2 := hle R' (hmin R' hR'mem)
    have heq : Jq R = Jq R' := le_antisymm h2 (by exact_mod_cast h1)
    rcases (Prod.Lex.le_iff).mp (hmin R' hR'mem) with h | ⟨-, h⟩
    · exact absurd heq (ne_of_lt h)
    · exact h

end Pendencias
