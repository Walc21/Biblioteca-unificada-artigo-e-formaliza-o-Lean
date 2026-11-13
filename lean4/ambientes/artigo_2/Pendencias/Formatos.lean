import RequestProject.Formats

/-!
# III.3.12 — comparação rigorosa dos formatos

O Lean existente prova os decodificadores exatos (`coding_formats_decoders`), as ordens
(`coding_format_orders`) e a família extremal como **lista** de átomos (`coding_gap_family`,
`N` par). Aqui se constrói a montagem do texto: a árvore diádica cheia de profundidade `r`
com raiz `K = J_{H-1-r,0}` cujas folhas são `J_{H-1,j}`, `0 ≤ j < 2^r`, com valor central `0` e
inclinação `(-1)^j`; ela é bem-formada (contínua) em `K`, tem altura `H`, e
`L_atom, L_{ReLU,str} = O(N log H)`, `L_{ReLU,rat} = Ω(NH)`. O caso de `N` qualquer usa
`N' = 2^{⌊log₂ N⌋} > N/2`.
-/

namespace Pendencias

open Artigo LTree

/-- árvore cheia de profundidade `r` com folhas `famAtom H (j 2^r + i)`, `0 ≤ i < 2^r` -/
def famTree (H : ℕ) : ℕ → ℕ → LTree
  | 0, j => .leaf (famAtom H j)
  | r + 1, j => .node (famTree H r (2 * j)) (famTree H r (2 * j + 1))

lemma famTree_leaves (H : ℕ) : ∀ r j, (famTree H r j).leaves =
    (List.range' (j * 2 ^ r) (2 ^ r)).map (famAtom H)
  | 0, j => by simp [famTree, LTree.leaves]
  | r + 1, j => by
      rw [famTree, LTree.leaves, famTree_leaves H r (2 * j), famTree_leaves H r (2 * j + 1),
        ← List.map_append, show (2 * j + 1) * 2 ^ r = 2 * j * 2 ^ r + 2 ^ r by ring,
        List.range'_append_1, show 2 * j * 2 ^ r = j * 2 ^ (r + 1) by ring,
        show 2 ^ r + 2 ^ r = 2 ^ (r + 1) by ring]

lemma famTree_lval (H : ℕ) : ∀ r j, (famTree H r j).lval = (famAtom H (j * 2 ^ r)).lval
  | 0, j => by simp [famTree, LTree.lval]
  | r + 1, j => by
      rw [famTree, LTree.lval, famTree_lval H r (2 * j), show 2 * j * 2 ^ r = j * 2 ^ (r + 1) by ring]

lemma famTree_rval (H : ℕ) : ∀ r j, (famTree H r j).rval =
    (famAtom H (j * 2 ^ r + 2 ^ r - 1)).rval
  | 0, j => by simp [famTree, LTree.rval]
  | r + 1, j => by
      rw [famTree, LTree.rval, famTree_rval H r (2 * j + 1),
        show (2 * j + 1) * 2 ^ r + 2 ^ r = j * 2 ^ (r + 1) + 2 ^ (r + 1) by ring]

lemma famTree_WF (H : ℕ) : ∀ (r j : ℕ), r ≤ H - 1 → WF (H - 1 - r) (j : ℤ) (famTree H r j)
  | 0, j, _ => by simp [famTree, WF, famAtom]
  | r + 1, j, hr => by
      refine ⟨?_, ?_, ?_⟩
      · have := famTree_WF H r (2 * j) (by omega)
        rw [show H - 1 - (r + 1) + 1 = H - 1 - r by omega]
        exact_mod_cast this
      · have := famTree_WF H r (2 * j + 1) (by omega)
        rw [show H - 1 - (r + 1) + 1 = H - 1 - r by omega]
        exact_mod_cast this
      · rw [famTree_rval, famTree_lval, show (2 * j + 1) * 2 ^ r = 2 * j * 2 ^ r + 2 ^ r by ring]
        have hP : 1 ≤ 2 ^ r := Nat.one_le_two_pow
        generalize 2 * j * 2 ^ r = Q
        generalize 2 ^ r = P at hP ⊢
        obtain ⟨n, hn⟩ : ∃ n, Q + P = n + 1 := ⟨Q + P - 1, by omega⟩
        rw [hn, show n + 1 - 1 = n by omega]
        exact (famAtom_contig H n).2

lemma famTree_root_leaves (H r : ℕ) : (famTree H r 0).leaves = famList H (2 ^ r) := by
  rw [famTree_leaves, zero_mul, List.range'_eq_map_range, famList]
  simp

/-- **Teorema III.3.12 (comparação rigorosa dos formatos)**: fluxos prefix-free com
decodificadores exatos; ordens `O(N log H)`, `O(N log H)`, `O(NH)`; a ordem `NH` de `L_{ReLU,rat}`
é atingida pela montagem cheia em `J_{H-1-r,0}` (`N = 2^r`, `2 ≤ N ≤ H`), e para `N` qualquer
com `2 ≤ N ≤ H` há uma montagem com no máximo `N` folhas e `NH ≤ 4 L_{ReLU,rat}`. -/
theorem coding_formats_comparison :
    (CatomCodec.RT (fun L => L ≠ []) ∧
      (∀ L : List Atom, ∀ t, strCodec.dec (strCodec.enc (strParams L) ++ t) = some (strParams L, t)) ∧
      (∀ L : List Atom, ∀ t,
        ratReluCodec.dec (ratReluCodec.enc (ratParams L) ++ t) = some (ratParams L, t))) ∧
    (∃ C : ℕ, ∀ H : ℕ, 2 ≤ H → ∀ L : List Atom, L ≠ [] → (∀ a ∈ L, a.height ≤ H) →
      Latom L ≤ C * L.length * Nat.log 2 H ∧ Lstr L ≤ C * L.length * Nat.log 2 H ∧
      Lrat L ≤ C * L.length * H) ∧
    ∃ C : ℕ,
      (∀ H r : ℕ, 2 ≤ H → 1 ≤ r → 2 ^ r ≤ H →
        let T := famTree H r 0
        WF (H - 1 - r) 0 T ∧ T.numLeaves = 2 ^ r ∧
        (∀ a ∈ T.leaves, a.k = H - 1) ∧ T.maxHeight = H ∧
        Latom T.leaves ≤ C * 2 ^ r * Nat.log 2 H ∧ Lstr T.leaves ≤ C * 2 ^ r * Nat.log 2 H ∧
        2 ^ r * H ≤ 2 * Lrat T.leaves) ∧
      (∀ H N : ℕ, 2 ≤ H → 2 ≤ N → N ≤ H →
        ∃ (r : ℕ) (T : LTree), WF (H - 1 - r) 0 T ∧ T.numLeaves ≤ N ∧ N < 2 * T.numLeaves ∧
          T.maxHeight = H ∧
          Latom T.leaves ≤ C * N * Nat.log 2 H ∧ Lstr T.leaves ≤ C * N * Nat.log 2 H ∧
          N * H ≤ 4 * Lrat T.leaves) := by
  refine ⟨coding_formats_decoders, coding_format_orders, ?_⟩
  obtain ⟨C, hC⟩ := coding_gap_family
  have pow2 : ∀ H r : ℕ, 2 ≤ H → 1 ≤ r → 2 ^ r ≤ H →
      WF (H - 1 - r) 0 (famTree H r 0) ∧ (famTree H r 0).numLeaves = 2 ^ r ∧
      (∀ a ∈ (famTree H r 0).leaves, a.k = H - 1) ∧ (famTree H r 0).maxHeight = H ∧
      Latom (famTree H r 0).leaves ≤ C * 2 ^ r * Nat.log 2 H ∧
      Lstr (famTree H r 0).leaves ≤ C * 2 ^ r * Nat.log 2 H ∧
      2 ^ r * H ≤ 2 * Lrat (famTree H r 0).leaves := by
    intro H r hH hr hrH
    have hr' : r < H := lt_of_lt_of_le (Nat.lt_two_pow_self) hrH
    have hev : Even (2 ^ r) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
    have h2 : 2 ≤ 2 ^ r := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr
    obtain ⟨-, hht, hlen, hA, hS, hQ⟩ := hC H (2 ^ r) hH hev h2 hrH
    rw [← famTree_root_leaves] at hht hlen hA hS hQ
    have hw := famTree_WF H r 0 (by omega)
    push_cast at hw
    refine ⟨hw, hlen, ?_, ?_, hA, hS, hQ⟩
    · intro a ha
      rw [famTree_root_leaves] at ha
      simp only [famList, List.mem_map, List.mem_range] at ha
      obtain ⟨j, -, rfl⟩ := ha
      rfl
    · apply le_antisymm (maxHeight_le_iff.mpr fun a ha => (hht a ha).le)
      have hne : (famTree H r 0).leaves ≠ [] := by
        intro h; have := congrArg List.length h
        rw [show (famTree H r 0).leaves.length = 2 ^ r from hlen] at this; simp at this
      obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ hne
      exact (hht a ha).symm.le.trans (le_maxHeight ha)
  refine ⟨C, fun H r hH hr hrH => pow2 H r hH hr hrH, fun H N hH hN hNH => ?_⟩
  set r := Nat.log 2 N
  have hr : 1 ≤ r := Nat.le_log_of_pow_le (by norm_num) (by simpa using hN)
  have h1 : 2 ^ r ≤ N := Nat.pow_log_le_self 2 (by omega)
  have h2 : N < 2 ^ (r + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  obtain ⟨hw, hn, -, hmax, hA, hS, hQ⟩ := pow2 H r hH hr (h1.trans hNH)
  refine ⟨r, famTree H r 0, hw, by rw [hn]; exact h1, by rw [hn, ← pow_succ']; exact h2, hmax,
    hA.trans ?_, hS.trans ?_, ?_⟩
  · exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)
  · exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)
  · have : N * H ≤ 2 * (2 ^ r * H) := by
      rw [← mul_assoc]; exact Nat.mul_le_mul_right _ (by rw [← pow_succ']; exact h2.le)
    omega

end Pendencias
