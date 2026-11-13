import Pendencias.Marcada
import RequestProject.Formats

/-!
# IV.5.4 (parte direta) — forma ancorada de uma montagem marcada

Infraestrutura (adaptada de `RequestProject/Trees.lean` para `MTree`/`MAtom`, em que a
inclinação pode ser nula): folhas contíguas e a forma ReLU
`g(x) = g(t₀) + s₀ (x - t₀) + ∑ (s_j - s_{j-1}) ρ(x - t_j)`.
-/

namespace Pendencias.Marcada

open Artigo Set

namespace MAtom

variable (a : MAtom)

/-- extremo esquerdo `m 2^{-k}` -/
def left : ℚ := (a.m : ℚ) / 2 ^ a.k
/-- extremo direito `(m+1) 2^{-k}` -/
def right : ℚ := ((a.m : ℚ) + 1) / 2 ^ a.k

lemma left_cast : ((a.left : ℚ) : ℝ) = cL a.k a.m := by simp [left, cL]
lemma right_cast : ((a.right : ℚ) : ℝ) = cR a.k a.m := by simp [right, cR]

lemma lval_eq : a.lval = a.y0 + a.s * (a.left - a.x0) := rfl
lemma rval_eq : a.rval = a.y0 + a.s * (a.right - a.x0) := rfl

lemma eval_left : a.eval (cL a.k a.m) = (a.lval : ℝ) := by
  rw [lval_eq]; push_cast; rw [a.left_cast]; rfl

lemma eval_right : a.eval (cR a.k a.m) = (a.rval : ℝ) := by
  rw [rval_eq]; push_cast; rw [a.right_cast]; rfl

lemma x0_eq : a.x0 = ((2 * a.m + 1 : ℤ) : ℚ) / 2 ^ (a.k + 1) := by
  simp only [MAtom.x0, pow_succ]; push_cast; field_simp

lemma two_le_height : 2 ≤ a.height := by unfold height; omega
lemma k_lt_height : a.k + 1 ≤ a.height := by unfold height; omega
lemma m_lt_height : a.m.natAbs + 1 ≤ a.height := by unfold height; omega
lemma ht_y0_le_height : ht a.y0 ≤ a.height := by unfold height; omega
lemma ht_s_le_height : ht a.s ≤ a.height := by unfold height; omega

end MAtom

namespace MTree

/-! ### Basic properties of well-formed trees -/

lemma leaves_cell_sub : ∀ {k : ℕ} {m : ℤ} {T : MTree}, MWF k m T → ∀ a ∈ T.leaves,
    cellIcc a.k a.m ⊆ cellIcc k m := by
  intro k m T
  induction T generalizing k m with
  | leaf a =>
    intro h b hb
    simp [leaves] at hb; subst hb; rw [h.1, h.2]
  | node l r ihl ihr =>
    intro h b hb
    simp only [leaves, List.mem_append] at hb
    rcases hb with hb | hb
    · refine (ihl h.1 b hb).trans ?_
      rw [cellIcc_eq, cellIcc_eq, cL_child_left, cR_child_left]
      exact Icc_subset_Icc le_rfl (le_trans (le_of_lt (cL_lt_cR _ _)) (by rw [cR_child_right]))
    · refine (ihr h.2.1 b hb).trans ?_
      rw [cellIcc_eq, cellIcc_eq, cR_child_right, ← cR_child_left]
      exact Icc_subset_Icc (by rw [← cL_child_left]; exact (cL_lt_cR _ _).le) le_rfl

lemma eval_at_left : ∀ {k : ℕ} {m : ℤ} {T : MTree}, MWF k m T → T.eval k m (cL k m) = T.lval := by
  intro k m T
  induction T generalizing k m with
  | leaf a => intro h; simp only [eval, lval]; rw [← h.1, ← h.2]; exact a.eval_left
  | node l r ihl _ =>
    intro h
    simp only [eval, lval]
    have : cL k m < cL (k + 1) (2 * m + 1) := by
      rw [← cR_child_left, ← cL_child_left]; exact cL_lt_cR _ _
    rw [if_pos this, ← cL_child_left]; exact ihl h.1

lemma eval_at_right : ∀ {k : ℕ} {m : ℤ} {T : MTree}, MWF k m T → T.eval k m (cR k m) = T.rval := by
  intro k m T
  induction T generalizing k m with
  | leaf a => intro h; simp only [eval, rval]; rw [← h.1, ← h.2]; exact a.eval_right
  | node l r _ ihr =>
    intro h
    simp only [eval, rval]
    have : ¬ cR k m < cL (k + 1) (2 * m + 1) := by
      rw [← cR_child_right]; exact not_lt.mpr (cL_lt_cR _ _).le
    rw [if_neg this, ← cR_child_right]; exact ihr h.2.1

/-- On every leaf cell (closed), the assembly coincides with the leaf atom. -/
lemma eval_leaf : ∀ {k : ℕ} {m : ℤ} {T : MTree}, MWF k m T → ∀ a ∈ T.leaves,
    ∀ x ∈ cellIcc a.k a.m, T.eval k m x = a.eval x := by
  intro k m T
  induction T generalizing k m with
  | leaf a =>
    intro _ b hb x _
    simp [leaves] at hb; subst hb; rfl
  | node l r ihl ihr =>
    intro h b hb x hx
    simp only [leaves, List.mem_append] at hb
    simp only [eval]
    rcases hb with hb | hb
    · have hxl := leaves_cell_sub h.1 b hb hx
      rw [cellIcc_eq, cR_child_left] at hxl
      split_ifs with hlt
      · exact ihl h.1 b hb x hx
      · have hxe : x = cL (k + 1) (2 * m + 1) := le_antisymm hxl.2 (not_lt.mp hlt)
        rw [← ihl h.1 b hb x hx, hxe, eval_at_left h.2.1]
        have := eval_at_right h.1
        rw [cR_child_left] at this
        rw [this, h.2.2]
    · have hxr := leaves_cell_sub h.2.1 b hb hx
      rw [cellIcc_eq] at hxr
      rw [if_neg (not_lt.mpr hxr.1)]
      exact ihr h.2.1 b hb x hx

/-- Every point of the root cell lies in some leaf cell. -/
lemma exists_leaf_mem : ∀ {k : ℕ} {m : ℤ} {T : MTree}, MWF k m T → ∀ x ∈ cellIcc k m,
    ∃ a ∈ T.leaves, x ∈ cellIcc a.k a.m := by
  intro k m T
  induction T generalizing k m with
  | leaf a => intro h x hx; exact ⟨a, by simp [leaves], by rw [h.1, h.2]; exact hx⟩
  | node l r ihl ihr =>
    intro h x hx
    rw [cellIcc_eq] at hx
    by_cases hlt : x < cL (k + 1) (2 * m + 1)
    · obtain ⟨a, ha, hxa⟩ := ihl h.1 x (by
        rw [cellIcc_eq, cL_child_left, cR_child_left]; exact ⟨hx.1, hlt.le⟩)
      exact ⟨a, by simp [leaves, ha], hxa⟩
    · obtain ⟨a, ha, hxa⟩ := ihr h.2.1 x (by
        rw [cellIcc_eq, cR_child_right]; exact ⟨not_lt.mp hlt, hx.2⟩)
      exact ⟨a, by simp [leaves, ha], hxa⟩

/-- first leaf of a tree -/
def firstLeaf : MTree → MAtom
  | leaf a => a
  | node l _ => l.firstLeaf

/-- last leaf of a tree -/
def lastLeaf : MTree → MAtom
  | leaf a => a
  | node _ r => r.lastLeaf

lemma leaves_eq_cons (T : MTree) : ∃ L, T.leaves = T.firstLeaf :: L := by
  induction T with
  | leaf a => exact ⟨[], rfl⟩
  | node l r ihl _ =>
    obtain ⟨L, hL⟩ := ihl
    exact ⟨L ++ r.leaves, by simp [leaves, firstLeaf, hL]⟩

lemma leaves_getLast (T : MTree) : T.leaves.getLast? = some T.lastLeaf := by
  induction T with
  | leaf a => rfl
  | node l r _ ihr =>
    simp only [leaves, lastLeaf]
    rw [List.getLast?_append, ihr]; rfl

lemma firstLeaf_left : ∀ {k : ℕ} {m : ℤ} {T : MTree}, MWF k m T →
    cL T.firstLeaf.k T.firstLeaf.m = cL k m ∧ T.firstLeaf.lval = T.lval := by
  intro k m T
  induction T generalizing k m with
  | leaf a => intro h; simp [firstLeaf, lval, h.1, h.2]
  | node l r ihl _ =>
    intro h
    obtain ⟨h1, h2⟩ := ihl h.1
    simp only [firstLeaf, lval]; rw [h1, cL_child_left]; exact ⟨rfl, h2⟩

lemma lastLeaf_right : ∀ {k : ℕ} {m : ℤ} {T : MTree}, MWF k m T →
    cR T.lastLeaf.k T.lastLeaf.m = cR k m ∧ T.lastLeaf.rval = T.rval := by
  intro k m T
  induction T generalizing k m with
  | leaf a => intro h; simp [lastLeaf, rval, h.1, h.2]
  | node l r _ ihr =>
    intro h
    obtain ⟨h1, h2⟩ := ihr h.2.1
    simp only [lastLeaf, rval]; rw [h1, cR_child_right]; exact ⟨rfl, h2⟩

/-! ### MContiguity of the leaves and the ReLU form -/

/-- two atoms are contiguous: the first ends where the second begins, with equal values. -/
def MContig (a b : MAtom) : Prop := cR a.k a.m = cL b.k b.m ∧ a.rval = b.lval

lemma leaves_isChain : ∀ {k : ℕ} {m : ℤ} {T : MTree}, MWF k m T → List.IsChain MContig T.leaves := by
  intro k m T
  induction T generalizing k m with
  | leaf a => intro _; simp [leaves]
  | node l r ihl ihr =>
    intro h
    simp only [leaves]
    rw [List.isChain_append]
    refine ⟨ihl h.1, ihr h.2.1, ?_⟩
    intro x hx y hy
    rw [leaves_getLast] at hx
    obtain ⟨L, hL⟩ := leaves_eq_cons r
    rw [hL] at hy
    simp at hx hy; subst hx; subst hy
    obtain ⟨e1, e2⟩ := lastLeaf_right h.1
    obtain ⟨f1, f2⟩ := firstLeaf_left h.2.1
    refine ⟨?_, ?_⟩
    · rw [e1, f1, cR_child_left]
    · rw [e2, f2, h.2.2]

/-- `ρ(z) = max{0, z}` -/
noncomputable def relu (z : ℝ) : ℝ := max 0 z

/-- the hinge sum `∑_{j ≥ 1} (s_j - s_{j-1}) ρ(x - t_j)` over consecutive leaves -/
noncomputable def mhingeSum (L : List MAtom) (x : ℝ) : ℝ :=
  ((L.zip L.tail).map (fun p => ((p.2.s : ℝ) - p.1.s) * relu (x - cL p.2.k p.2.m))).sum

lemma mhingeSum_cons_cons (a b : MAtom) (L : List MAtom) (x : ℝ) :
    mhingeSum (a :: b :: L) x = ((b.s : ℝ) - a.s) * relu (x - cL b.k b.m) + mhingeSum (b :: L) x := by
  simp [mhingeSum, List.zip_cons_cons]

lemma mhingeSum_zero_of_le : ∀ (L : List MAtom) (x : ℝ), List.IsChain MContig L →
    ∀ b ∈ L.head?, x ≤ cR b.k b.m → mhingeSum L x = 0 := by
  intro L
  induction L with
  | nil => intros; simp [mhingeSum]
  | cons a L ih =>
    intro x hc b hb hx
    have hb' : a = b := by simpa using hb
    subst hb'
    cases L with
    | nil => simp [mhingeSum]
    | cons c L' =>
      rw [mhingeSum_cons_cons]
      have hac : MContig a c := (List.isChain_cons_cons.mp hc).1
      have hrest : List.IsChain MContig (c :: L') := (List.isChain_cons_cons.mp hc).2
      have h1 : relu (x - cL c.k c.m) = 0 := by
        unfold relu; rw [max_eq_left]; rw [← hac.1]; linarith
      rw [h1, mul_zero, zero_add]
      exact ih x hrest c (by simp) (le_trans hx (by rw [hac.1]; exact (cL_lt_cR _ _).le))

/-- In a contiguous chain, `a₀(x) + ∑ (s_j - s_{j-1}) ρ(x - t_j)` agrees with the atom whose
cell contains `x`. -/
lemma chain_relu : ∀ (L : List MAtom), List.IsChain MContig L → ∀ a₀ ∈ L.head?,
    ∀ a ∈ L, ∀ x ∈ cellIcc a.k a.m, a₀.eval x + mhingeSum L x = a.eval x := by
  intro L
  induction L with
  | nil => intros; simp_all
  | cons b L ih =>
    intro hc a₀ ha₀ a ha x hx
    have ha₀' : b = a₀ := by simpa using ha₀
    subst ha₀'
    cases L with
    | nil =>
      simp at ha; subst ha; simp [mhingeSum]
    | cons c L' =>
      have hbc : MContig b c := (List.isChain_cons_cons.mp hc).1
      have hrest : List.IsChain MContig (c :: L') := (List.isChain_cons_cons.mp hc).2
      rw [mhingeSum_cons_cons]
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · -- `x` in the first cell: all hinges vanish
        rw [cellIcc_eq] at hx
        have h1 : relu (x - cL c.k c.m) = 0 := by
          unfold relu; rw [max_eq_left]; rw [← hbc.1]; linarith [hx.2]
        rw [h1, mul_zero, zero_add, mhingeSum_zero_of_le (c :: L') x hrest c (by simp)
          (le_trans hx.2 (by rw [hbc.1]; exact (cL_lt_cR _ _).le)), add_zero]
      · -- `x` beyond the first knot
        have hge : cL c.k c.m ≤ x := by
          have key : ∀ (L : List MAtom), List.IsChain MContig L → ∀ c ∈ L.head?, ∀ d ∈ L,
              cL c.k c.m ≤ cL d.k d.m := by
            intro L
            induction L with
            | nil => intros; simp_all
            | cons e L ih2 =>
              intro hc' c' hc'' d hd
              have hc3 : e = c' := by simpa using hc''
              subst hc3
              simp only [List.mem_cons] at hd
              rcases hd with rfl | hd
              · exact le_rfl
              · cases L with
                | nil => simp at hd
                | cons f L'' =>
                  have hef : MContig e f := (List.isChain_cons_cons.mp hc').1
                  have := ih2 (List.isChain_cons_cons.mp hc').2 f (by simp) d hd
                  refine le_trans ?_ this
                  rw [← hef.1]; exact (cL_lt_cR _ _).le
          have := key (c :: L') hrest c (by simp) a (List.mem_cons.mpr ha)
          rw [cellIcc_eq] at hx
          linarith [hx.1]
        have h1 : relu (x - cL c.k c.m) = x - cL c.k c.m := by
          unfold relu; rw [max_eq_right]; linarith
        rw [h1, ← ih hrest c (by simp) a (List.mem_cons.mpr ha) x hx]
        -- a₀(x) + (s_c - s_{a₀}) (x - t) = c(x)
        have e1 : b.eval x = b.rval + b.s * (x - cR b.k b.m) := by
          rw [← b.eval_right]; simp only [MAtom.eval]; ring
        have e2 : c.eval x = c.lval + c.s * (x - cL c.k c.m) := by
          rw [← c.eval_left]; simp only [MAtom.eval]; ring
        rw [e1, e2, hbc.1, hbc.2]; ring

/-- **Proposition 2.3 (ReLU form)**: an assembly with knots `t₀ < ⋯ < t_N` and slopes `s_j`
satisfies, on its root cell,
`g(x) = g(t₀) + s₀ (x - t₀) + ∑_{j=1}^{N-1} (s_j - s_{j-1}) ρ(x - t_j)`. -/
theorem eval_relu_form {k : ℕ} {m : ℤ} {T : MTree} (h : MWF k m T) :
    ∀ x ∈ cellIcc k m, T.eval k m x =
      T.eval k m (cL k m) + (T.firstLeaf.s : ℝ) * (x - cL k m) + mhingeSum T.leaves x := by
  intro x hx
  obtain ⟨a, ha, hxa⟩ := exists_leaf_mem h x hx
  rw [eval_leaf h a ha x hxa]
  obtain ⟨L, hL⟩ := leaves_eq_cons T
  have hchain := leaves_isChain h
  have := chain_relu T.leaves hchain T.firstLeaf (by rw [hL]; simp) a ha x hxa
  rw [← this, eval_at_left h]
  obtain ⟨f1, f2⟩ := firstLeaf_left h
  have : T.firstLeaf.eval x = T.firstLeaf.lval + T.firstLeaf.s * (x - cL T.firstLeaf.k T.firstLeaf.m) := by
    rw [← T.firstLeaf.eval_left]; simp only [MAtom.eval]; ring
  rw [this, f1, f2]


end MTree

/-! ## Forma reduzida: hinges de salto não nulo -/

namespace Ancorada

open MTree

/-- pares reduzidos `(t_j, s_j - s_{j-1})` das folhas consecutivas cuja inclinação muda -/
def redPairs (L : List MAtom) : List (ℚ × ℚ) :=
  ((L.zip L.tail).filter (fun p => decide (p.1.s ≠ p.2.s))).map
    (fun p => (p.2.left, p.2.s - p.1.s))

/-- soma `∑ a_j ρ(x - t_j)` sobre uma lista de pares `(t_j, a_j)` -/
noncomputable def redSum (P : List (ℚ × ℚ)) (x : ℝ) : ℝ :=
  (P.map fun q => (q.2 : ℝ) * relu (x - q.1)).sum

lemma redPairs_single (a : MAtom) : redPairs [a] = [] := by simp [redPairs]

lemma redPairs_cons_cons (a b : MAtom) (L : List MAtom) :
    redPairs (a :: b :: L) =
      (if a.s ≠ b.s then [(b.left, b.s - a.s)] else []) ++ redPairs (b :: L) := by
  by_cases h : a.s = b.s <;> simp [redPairs, List.zip_cons_cons, h]

lemma mhingeSum_eq_redSum : ∀ (L : List MAtom) (a : MAtom) (x : ℝ),
    mhingeSum (a :: L) x = redSum (redPairs (a :: L)) x
  | [], a, x => by simp [mhingeSum, redSum, redPairs]
  | b :: L, a, x => by
      rw [mhingeSum_cons_cons, redPairs_cons_cons, mhingeSum_eq_redSum L b x]
      by_cases h : a.s = b.s
      · have h' : (b.s : ℝ) = a.s := by rw [h]
        simp [h, h', redSum]
      · have hne : a.s ≠ b.s := h
        rw [if_pos hne]
        simp only [redSum, List.singleton_append, List.map_cons, List.sum_cons]
        rw [b.left_cast]
        push_cast
        ring

lemma redPairs_length : ∀ (L : List MAtom) (a : MAtom), (redPairs (a :: L)).length ≤ L.length
  | [], a => by simp [redPairs]
  | b :: L, a => by
      rw [redPairs_cons_cons]
      have := redPairs_length L b
      split_ifs <;> simp <;> omega

lemma redPairs_mem {L : List MAtom} {q : ℚ × ℚ} (hq : q ∈ redPairs L) :
    ∃ c ∈ L, ∃ d ∈ L, c.s ≠ d.s ∧ q = (d.left, d.s - c.s) := by
  simp only [redPairs, List.mem_map, List.mem_filter, decide_eq_true_eq] at hq
  obtain ⟨p, ⟨hp, hne⟩, rfl⟩ := hq
  exact ⟨p.1, (List.of_mem_zip hp).1, p.2, List.mem_of_mem_tail (List.of_mem_zip hp).2, hne, rfl⟩

/-- os `t_j` dos hinges são estritamente crescentes e ficam à direita do extremo direito
da primeira folha -/
lemma redPairs_chain : ∀ (L : List MAtom) (a : MAtom), List.IsChain MContig (a :: L) →
    ((redPairs (a :: L)).map Prod.fst).Pairwise (fun u v : ℚ => (u : ℝ) < v) ∧
    ∀ q ∈ redPairs (a :: L), cR a.k a.m ≤ (q.1 : ℝ)
  | [], a, _ => by simp [redPairs]
  | b :: L, a, hc => by
      have hab : MContig a b := (List.isChain_cons_cons.mp hc).1
      have hrest := (List.isChain_cons_cons.mp hc).2
      obtain ⟨ih1, ih2⟩ := redPairs_chain L b hrest
      have hlt : cL b.k b.m < cR b.k b.m := cL_lt_cR _ _
      rw [redPairs_cons_cons]
      by_cases h : a.s = b.s
      · rw [if_neg (fun hne => hne h), List.nil_append]
        refine ⟨ih1, fun q hq => ?_⟩
        have := ih2 q hq
        rw [hab.1]
        linarith
      · have hne : a.s ≠ b.s := h
        rw [if_pos hne]
        refine ⟨?_, ?_⟩
        · simp only [List.singleton_append, List.map_cons, List.pairwise_cons]
          refine ⟨fun v hv => ?_, ih1⟩
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hv
          have := ih2 q hq
          rw [b.left_cast]
          linarith
        · intro q hq
          simp only [List.singleton_append, List.mem_cons] at hq
          rcases hq with rfl | hq
          · simp only
            rw [b.left_cast, hab.1]
          · have := ih2 q hq
            rw [hab.1]
            linarith

/-- as inclinações locais `σ_i = σ_0 + ∑_{j ≤ i} a_j` são inclinações de folhas -/
lemma slope_partial : ∀ (L : List MAtom) (a : MAtom) (i : ℕ), i ≤ (redPairs (a :: L)).length →
    ∃ b ∈ a :: L, a.s + (((redPairs (a :: L)).take i).map Prod.snd).sum = b.s
  | [], a, i, hi => by
      have : i = 0 := by simpa [redPairs] using hi
      subst this
      exact ⟨a, by simp, by simp [redPairs]⟩
  | b :: L, a, i, hi => by
      rw [redPairs_cons_cons] at hi ⊢
      by_cases h : a.s = b.s
      · rw [if_neg (fun hne => hne h), List.nil_append] at hi ⊢
        obtain ⟨c, hc, hce⟩ := slope_partial L b i hi
        refine ⟨c, ?_, ?_⟩
        · simp only [List.mem_cons] at hc ⊢; tauto
        · rw [h]; exact hce
      · have hne : a.s ≠ b.s := h
        rw [if_pos hne] at hi ⊢
        cases i with
        | zero => exact ⟨a, by simp, by simp⟩
        | succ i =>
            simp only [List.singleton_append, List.length_cons] at hi
            obtain ⟨c, hc, hce⟩ := slope_partial L b i (by omega)
            refine ⟨c, ?_, ?_⟩
            · simp only [List.mem_cons] at hc ⊢; tauto
            · simp only [List.singleton_append, List.take_succ_cons, List.map_cons, List.sum_cons]
              rw [← hce]; ring

/-! ## A forma ancorada e o teorema direto -/

/-- forma ancorada `g(x) = ys + s0 (x - xs) + ∑ a_j ρ(x - t_j)`, com `hinges = [(t_j, a_j)]` -/
structure Anchored where
  xs : ℚ
  ys : ℚ
  s0 : ℚ
  hinges : List (ℚ × ℚ)

/-- avaliação da forma ancorada -/
noncomputable def Anchored.eval (A : Anchored) (x : ℝ) : ℝ :=
  (A.ys : ℝ) + (A.s0 : ℝ) * (x - A.xs) + redSum A.hinges x

/-- Propriedades da forma ancorada de `g ∈ 𝒜^□_{N,H}([0,1])` (IV.5.4, parte direta). -/
def AnchoredSpec (N H : ℕ) (g : ℝ → ℝ) (A : Anchored) : Prop :=
  (∀ x ∈ Icc (0 : ℝ) 1, g x = A.eval x) ∧
  (∃ k : ℕ, k + 1 ≤ H ∧ A.xs = 1 / 2 ^ (k + 1)) ∧
  g A.xs = A.ys ∧
  A.hinges.length + 1 ≤ N ∧
  (A.hinges.map Prod.fst).Pairwise (· < ·) ∧
  (∀ q ∈ A.hinges, 0 < q.1 ∧ q.1 < 1 ∧ q.2 ≠ 0) ∧
  ht A.ys ≤ H ∧ ht A.s0 ≤ H ∧
  (∀ i ≤ A.hinges.length, ht (A.s0 + ((A.hinges.take i).map Prod.snd).sum) ≤ H) ∧
  (∀ q ∈ A.hinges, ht q.2 ≤ 2 * H ^ 2) ∧
  (∀ q ∈ A.hinges, ∃ (k : ℕ) (m : ℤ), q.1 = (m : ℚ) / 2 ^ k ∧ k + 1 ≤ H ∧ m.natAbs + 1 ≤ H)

lemma x0_mem_cell (a : MAtom) : ((a.x0 : ℚ) : ℝ) ∈ cellIcc a.k a.m := by
  have hx0c : ((a.x0 : ℚ) : ℝ) = ((a.m : ℝ) + 1 / 2) / 2 ^ a.k := by simp [MAtom.x0]
  have hp : (0 : ℝ) < 2 ^ a.k := by positivity
  rw [cellIcc_eq, hx0c]
  simp only [cL, cR, Set.mem_Icc]
  constructor
  · exact div_le_div_of_nonneg_right (by linarith) hp.le
  · exact div_le_div_of_nonneg_right (by linarith) hp.le

theorem anchored_form {N H : ℕ} {g : ℝ → ℝ} (hg : g ∈ MAsmNH N H) :
    ∃ A : Anchored, AnchoredSpec N H g A := by
  obtain ⟨T, hT, hN, hH, rfl⟩ := hg
  obtain ⟨L, hL⟩ := leaves_eq_cons T
  have hall := (MTree.maxHeight_le_iff).mp hH
  have ha_mem : T.firstLeaf ∈ T.leaves := by rw [hL]; simp
  have hLmem : ∀ b ∈ L, b ∈ T.leaves := fun b hb => by rw [hL]; simp [hb]
  have hchain := leaves_isChain hT
  rw [hL] at hchain
  obtain ⟨hpw, hge⟩ := redPairs_chain L T.firstLeaf hchain
  obtain ⟨hcl, hlv⟩ := firstLeaf_left hT
  have hc00 : cL 0 0 = 0 := by simp [cL]
  have hcl0 : cL T.firstLeaf.k T.firstLeaf.m = 0 := by rw [hcl, hc00]
  have hm0 : T.firstLeaf.m = 0 := by
    have h1 : (T.firstLeaf.m : ℝ) / 2 ^ T.firstLeaf.k = 0 := by simpa [cL] using hcl0
    have h2 : (T.firstLeaf.m : ℝ) = 0 := by
      rcases div_eq_zero_iff.mp h1 with h | h
      · exact h
      · exact absurd h (by positivity)
    exact_mod_cast h2
  have hleft0 : T.firstLeaf.left = 0 := by simp [MAtom.left, hm0]
  have hx0q : T.firstLeaf.x0 = 1 / 2 ^ (T.firstLeaf.k + 1) := by
    unfold MAtom.x0; rw [hm0]; push_cast; rw [pow_succ]; field_simp; norm_num
  have hRpos : (0 : ℝ) < cR T.firstLeaf.k T.firstLeaf.m := by
    unfold cR; rw [hm0]; push_cast; positivity
  have hroot : ∀ b ∈ T.leaves, cR b.k b.m ≤ 1 := by
    intro b hb
    have hsub := leaves_cell_sub hT b hb
    have hmem : cR b.k b.m ∈ cellIcc b.k b.m := by
      rw [cellIcc_eq]; exact ⟨(cL_lt_cR _ _).le, le_rfl⟩
    have h2 := hsub hmem
    rw [cellIcc_eq] at h2
    simpa [cR] using h2.2
  have hHa : T.firstLeaf.height ≤ H := hall _ ha_mem
  refine ⟨⟨T.firstLeaf.x0, T.firstLeaf.y0, T.firstLeaf.s, redPairs (T.firstLeaf :: L)⟩, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hx' : x ∈ cellIcc 0 0 := by
      rw [cellIcc_eq]; simpa [cL, cR] using hx
    rw [eval_relu_form hT x hx', eval_at_left hT, ← hlv, hL, mhingeSum_eq_redSum]
    simp only [Anchored.eval]
    rw [MAtom.lval_eq, hleft0, hc00]
    push_cast
    ring
  · exact ⟨T.firstLeaf.k, le_trans T.firstLeaf.k_lt_height hHa, hx0q⟩
  · have h := eval_leaf hT T.firstLeaf ha_mem _ (x0_mem_cell T.firstLeaf)
    simp only
    rw [h]
    simp [MAtom.eval]
  · have h1 : T.numLeaves = L.length + 1 := by simp [MTree.numLeaves, hL]
    have h2 := redPairs_length L T.firstLeaf
    show (redPairs (T.firstLeaf :: L)).length + 1 ≤ N
    omega
  · exact hpw.imp (fun h => by exact_mod_cast h)
  · intro q hq
    have hq1 := hge q hq
    obtain ⟨c, hc, d, hd, hne, rfl⟩ := redPairs_mem hq
    have hdL : d ∈ T.leaves := by rw [hL]; exact hd
    refine ⟨?_, ?_, sub_ne_zero.mpr (Ne.symm hne)⟩
    · have h0 : (0 : ℝ) < ((d.left : ℚ) : ℝ) := lt_of_lt_of_le hRpos hq1
      exact_mod_cast h0
    · have h1 : ((d.left : ℚ) : ℝ) < 1 := by
        rw [d.left_cast]; exact lt_of_lt_of_le (cL_lt_cR _ _) (hroot d hdL)
      exact_mod_cast h1
  · exact le_trans T.firstLeaf.ht_y0_le_height hHa
  · exact le_trans T.firstLeaf.ht_s_le_height hHa
  · intro i hi
    obtain ⟨b, hb, hbe⟩ := slope_partial L T.firstLeaf i hi
    have hbL : b ∈ T.leaves := by rw [hL]; exact hb
    show ht (T.firstLeaf.s + (((redPairs (T.firstLeaf :: L)).take i).map Prod.snd).sum) ≤ H
    rw [hbe]
    exact le_trans b.ht_s_le_height (hall b hbL)
  · intro q hq
    obtain ⟨c, hc, d, hd, hne, rfl⟩ := redPairs_mem hq
    have hcH : ht c.s ≤ H := le_trans c.ht_s_le_height (hall c (by rw [hL]; exact hc))
    have hdH : ht d.s ≤ H := le_trans d.ht_s_le_height (hall d (by rw [hL]; exact hd))
    show ht (d.s - c.s) ≤ 2 * H ^ 2
    calc ht (d.s - c.s) ≤ 2 * ht d.s * ht c.s := ht_sub_le _ _
      _ ≤ 2 * H * H := by gcongr
      _ = 2 * H ^ 2 := by ring
  · intro q hq
    obtain ⟨c, hc, d, hd, hne, rfl⟩ := redPairs_mem hq
    have hdL : d ∈ T.leaves := by rw [hL]; exact hd
    exact ⟨d.k, d.m, rfl, le_trans d.k_lt_height (hall d hdL),
      le_trans d.m_lt_height (hall d hdL)⟩

end Ancorada

end Pendencias.Marcada
