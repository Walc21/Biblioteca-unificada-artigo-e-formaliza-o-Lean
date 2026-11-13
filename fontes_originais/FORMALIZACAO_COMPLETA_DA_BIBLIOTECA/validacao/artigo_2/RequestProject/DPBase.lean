import RequestProject.Functional

/-!
# Infrastructure for the dynamic programmes of Sections 6–8

Representation sets with prescribed boundary states, their decomposition at the root, the
value alphabet containing all states, and arithmetic of minima in `WithTop ℚ`.
-/

namespace Artigo

open Set LTree

/-! ## Minima in `WithTop ℚ` -/

lemma inf_add_const {ι : Type*} (s : Finset ι) (f : ι → WithTop ℚ) (c : WithTop ℚ) :
    s.inf f + c = s.inf fun x => f x + c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s _ ih =>
    rw [Finset.inf_insert, Finset.inf_insert, ← ih]
    exact (min_add_add_right _ _ _).symm

lemma const_add_inf {ι : Type*} (s : Finset ι) (f : ι → WithTop ℚ) (c : WithTop ℚ) :
    c + s.inf f = s.inf fun x => c + f x := by
  rw [add_comm, inf_add_const]; simp only [add_comm]

lemma inf_prod_add {ι κ : Type*} (s : Finset ι) (t : Finset κ) (f : ι → WithTop ℚ) (g : κ → WithTop ℚ) :
    (s ×ˢ t).inf (fun p => f p.1 + g p.2) = s.inf f + t.inf g := by
  rw [Finset.inf_product_left, inf_add_const]
  congr 1; ext x
  rw [const_add_inf]

/-! ## Leaves and boundary values -/

lemma exists_leaf_lval (T : LTree) : ∃ a ∈ T.leaves, a.lval = T.lval := by
  induction T with
  | leaf a => exact ⟨a, by simp [leaves], rfl⟩
  | node l r ihl _ =>
    obtain ⟨a, ha, h⟩ := ihl
    exact ⟨a, by simp [leaves, ha], h⟩

lemma exists_leaf_rval (T : LTree) : ∃ a ∈ T.leaves, a.rval = T.rval := by
  induction T with
  | leaf a => exact ⟨a, by simp [leaves], rfl⟩
  | node l r _ ihr =>
    obtain ⟨a, ha, h⟩ := ihr
    exact ⟨a, by simp [leaves, ha], h⟩

/-- `J_{k,m}` is a descendant of `K = J_{k₀,m₀}` at relative depth `r` -/
def IsDesc (k₀ : ℕ) (m₀ : ℤ) (k : ℕ) (m : ℤ) (r : ℕ) : Prop := k = k₀ + r ∧ m / 2 ^ r = m₀

lemma IsDesc.root (k₀ : ℕ) (m₀ : ℤ) : IsDesc k₀ m₀ k₀ m₀ 0 := ⟨rfl, by simp⟩

lemma IsDesc.left {k₀ k r : ℕ} {m₀ m : ℤ} (h : IsDesc k₀ m₀ k m r) :
    IsDesc k₀ m₀ (k + 1) (2 * m) (r + 1) := by
  refine ⟨by rw [h.1]; ring, ?_⟩
  rw [pow_succ, mul_comm (2 ^ r : ℤ) 2, ← Int.ediv_ediv_of_nonneg (by norm_num)]
  simp [h.2]

lemma IsDesc.right {k₀ k r : ℕ} {m₀ m : ℤ} (h : IsDesc k₀ m₀ k m r) :
    IsDesc k₀ m₀ (k + 1) (2 * m + 1) (r + 1) := by
  refine ⟨by rw [h.1]; ring, ?_⟩
  rw [pow_succ, mul_comm (2 ^ r : ℤ) 2, ← Int.ediv_ediv_of_nonneg (by norm_num)]
  have : (2 * m + 1) / 2 = m := by omega
  rw [this, h.2]

/-- endpoint values of admissible atoms descending from `K` lie in the alphabet -/
lemma atom_vals_mem {H D k₀ : ℕ} {m₀ : ℤ} (hH : 2 ≤ H) {a : Atom} (ha : a.height ≤ H)
    (hk : k₀ ≤ a.k) (hkD : a.k ≤ k₀ + D) (hm : a.m / 2 ^ (a.k - k₀) = m₀) :
    a.lval ∈ Valphabet H D k₀ m₀ ∧ a.rval ∈ Valphabet H D k₀ m₀ := by
  classical
  set r := a.k - k₀
  have hpos : (0 : ℤ) < 2 ^ r := by positivity
  have hj0 : 0 ≤ a.m % 2 ^ r := Int.emod_nonneg _ hpos.ne'
  have hj1 : a.m % 2 ^ r < 2 ^ r := Int.emod_lt_of_pos _ hpos
  have hdec : a.m = 2 ^ r * m₀ + (a.m % 2 ^ r) := by rw [← hm]; exact (Int.mul_ediv_add_emod _ _).symm
  have hmemP : (a.lval, a.rval) ∈ PH H (k₀ + r) (2 ^ r * m₀ + ((a.m % 2 ^ r).toNat : ℤ)) := by
    have := (endpoint_dictionary (k := a.k) (m := a.m) hH).1.1 ⟨ha, rfl, rfl⟩
    rw [Finset.mem_coe] at this
    convert this using 2
    · omega
    · rw [Int.toNat_of_nonneg hj0]; exact hdec.symm
  have hjr : (a.m % 2 ^ r).toNat < 2 ^ r := by
    have h' : ((a.m % 2 ^ r).toNat : ℤ) < ((2 ^ r : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg hj0]; push_cast; exact hj1
    exact_mod_cast h'
  unfold Valphabet
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
  exact ⟨⟨r, by omega, _, hjr, _, hmemP, Or.inl rfl⟩, ⟨r, by omega, _, hjr, _, hmemP, Or.inr rfl⟩⟩

/-- all leaf values of a representation rooted at a descendant cell lie in the alphabet -/
lemma leaf_vals_mem {H D k₀ : ℕ} {m₀ : ℤ} (hH : 2 ≤ H) {k r : ℕ} {m : ℤ}
    (hd : IsDesc k₀ m₀ k m r) {T : LTree} (hT : WF k m T) (hdep : r + T.depth ≤ D)
    (hh : T.maxHeight ≤ H) :
    ∀ a ∈ T.leaves, a.lval ∈ Valphabet H D k₀ m₀ ∧ a.rval ∈ Valphabet H D k₀ m₀ := by
  intro a ha
  obtain ⟨hk, hm⟩ := WF_leaf_anc hT a ha
  have hkd := WF_leaf_depth hT a ha
  obtain ⟨rfl, hdm⟩ := hd
  refine atom_vals_mem hH (le_trans (le_maxHeight ha) hh) (by omega) (by omega) ?_
  have e : a.k - k₀ = (a.k - (k₀ + r)) + r := by omega
  rw [e, pow_add, ← Int.ediv_ediv_of_nonneg (by positivity), hm, hdm]

lemma rootvals_mem {H D k₀ : ℕ} {m₀ : ℤ} (hH : 2 ≤ H) {k r : ℕ} {m : ℤ}
    (hd : IsDesc k₀ m₀ k m r) {T : LTree} (hT : WF k m T) (hdep : r + T.depth ≤ D)
    (hh : T.maxHeight ≤ H) : T.lval ∈ Valphabet H D k₀ m₀ ∧ T.rval ∈ Valphabet H D k₀ m₀ := by
  obtain ⟨a, ha, hal⟩ := exists_leaf_lval T
  obtain ⟨b, hb, hbr⟩ := exists_leaf_rval T
  exact ⟨hal ▸ (leaf_vals_mem hH hd hT hdep hh a ha).1, hbr ▸ (leaf_vals_mem hH hd hT hdep hh b hb).2⟩

lemma maxHeight_node (l r : LTree) {H : ℕ} :
    (node l r).maxHeight ≤ H ↔ l.maxHeight ≤ H ∧ r.maxHeight ≤ H := by
  simp only [maxHeight_le_iff, leaves, List.mem_append]
  constructor
  · intro h; exact ⟨fun a ha => h a (Or.inl ha), fun a ha => h a (Or.inr ha)⟩
  · rintro ⟨h1, h2⟩ a (ha | ha); exacts [h1 a ha, h2 a ha]

/-! ## Representation sets -/

namespace Setup

variable (S : Setup)

/-- the value alphabet `𝒱_{D,H}(K)` of the problem -/
noncomputable def V : Finset ℚ := Valphabet S.H S.D S.k₀ S.m₀

open Classical in
/-- `𝔑_{d,H}(J;u,v)`: representations rooted at `J_{k,m}` with relative depth `≤ d`, atoms in
`𝓛_H` and boundary values `u, v` -/
noncomputable def Rset (d k : ℕ) (m : ℤ) (u v : ℚ) : Finset LTree :=
  (allTrees S.H d).filter fun R => WF k m R ∧ R.lval = u ∧ R.rval = v

lemma mem_Rset {d k : ℕ} {m : ℤ} {u v : ℚ} {R : LTree} :
    R ∈ S.Rset d k m u v ↔ R.depth ≤ d ∧ R.maxHeight ≤ S.H ∧ WF k m R ∧ R.lval = u ∧ R.rval = v := by
  classical
  unfold Rset
  rw [Finset.mem_filter, mem_allTrees, maxHeight_le_iff]
  tauto

/-- the cost as an extended rational -/
def costW (R : LTree) : WithTop ℚ := (S.costT R : WithTop ℚ)

lemma costW_node (l r : LTree) : S.costW (node l r) = S.costW l + S.costW r + ((S.lb + S.ls : ℚ) : WithTop ℚ) := by
  simp only [costW, S.costT_node]; push_cast; rfl

/-- the leaf representations with boundary values `(u,v)` realize `Φ_H(J;u,v)` -/
lemma Rset_zero_inf (hH : 2 ≤ S.H) (k : ℕ) (m : ℤ) (u v : ℚ) :
    (S.Rset 0 k m u v).inf S.costW = S.Phi k m u v := by
  classical
  by_cases hp : (u, v) ∈ PH S.H k m
  · obtain ⟨b, ⟨hb, hbk, hbm⟩, hbuv⟩ := (endpoint_dictionary hH).1.2.2 (Finset.mem_coe.mpr hp)
    simp only [Prod.mk.injEq] at hbuv
    obtain ⟨rfl, rfl⟩ := hbuv
    subst hbk hbm
    have hRs : S.Rset 0 b.k b.m b.lval b.rval = {leaf b} := by
      ext R
      rw [mem_Rset, Finset.mem_singleton]
      constructor
      · rintro ⟨hd, hh, hW, hu, hv⟩
        cases R with
        | node l r => simp [depth] at hd
        | leaf c =>
          obtain ⟨hk, hm⟩ := hW
          simp only [LTree.lval, LTree.rval] at hu hv
          have hc : c.height ≤ S.H := by
            rw [maxHeight_le_iff] at hh; exact hh c (by simp [leaves])
          rw [(endpoint_dictionary hH).1.2.1 (show c ∈ {a : Atom | a.height ≤ S.H ∧ a.k = b.k ∧ a.m = b.m}
            from ⟨hc, hk, hm⟩) (show b ∈ {a : Atom | a.height ≤ S.H ∧ a.k = b.k ∧ a.m = b.m}
            from ⟨hb, rfl, rfl⟩) (by simp only [hu, hv])]
      · rintro rfl
        refine ⟨by simp [depth], ?_, ⟨rfl, rfl⟩, rfl, rfl⟩
        rw [maxHeight_le_iff]
        intro c hc
        simp only [leaves, List.mem_singleton] at hc
        rw [hc]; exact hb
    rw [hRs, Finset.inf_singleton]
    exact (S.Phi_atom hb).symm
  · have hRs : S.Rset 0 k m u v = ∅ := by
      ext R
      simp only [Finset.notMem_empty, iff_false]
      intro hR
      rw [mem_Rset] at hR
      obtain ⟨hd, hh, hW, hu, hv⟩ := hR
      cases R with
      | node l r => simp [depth] at hd
      | leaf b =>
        obtain ⟨hk, hm⟩ := hW
        apply hp
        have := (endpoint_dictionary (k := k) (m := m) hH).1.1
          (show b ∈ {a : Atom | a.height ≤ S.H ∧ a.k = k ∧ a.m = m} from
            ⟨by rw [maxHeight_le_iff] at hh; exact hh b (by simp [leaves]), hk, hm⟩)
        simp only [LTree.lval, LTree.rval] at hu hv
        simp only [Finset.mem_coe] at this
        rwa [hu, hv] at this
    rw [hRs, Finset.inf_empty]
    unfold Phi
    rw [dif_neg hp]

/-- **root decomposition**: a representation of depth `≤ d+1` is either a leaf, or a node whose
two subtrees share a boundary value `w ∈ 𝒱` -/
lemma Rset_succ (hH : 2 ≤ S.H) {d k r : ℕ} {m : ℤ} (hd : IsDesc S.k₀ S.m₀ k m r)
    (hdD : r + (d + 1) ≤ S.D) (u v : ℚ) :
    S.Rset (d + 1) k m u v = S.Rset 0 k m u v ∪ S.V.biUnion fun w =>
      (S.Rset d (k + 1) (2 * m) u w ×ˢ S.Rset d (k + 1) (2 * m + 1) w v).image
        fun p => node p.1 p.2 := by
  classical
  ext R
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product,
    Prod.exists, mem_Rset]
  cases R with
  | leaf a =>
    simp only [depth, zero_le, true_and, reduceCtorEq, and_false, exists_false, or_false]
  | node l r' =>
    simp only [depth, node.injEq, maxHeight_node, WF, LTree.lval, LTree.rval]
    constructor
    · rintro ⟨hdp, ⟨hl, hr⟩, ⟨hWl, hWr, hlr⟩, hu, hv⟩
      right
      refine ⟨l.rval, ?_, l, r', ⟨⟨by omega, hl, hWl, hu, rfl⟩, by omega, hr, hWr, hlr.symm, hv⟩, rfl, rfl⟩
      exact (rootvals_mem hH hd.left hWl (by omega) hl).2
    · rintro (⟨hd0, -⟩ | ⟨w, -, l', r'', ⟨⟨hd1, hl, hWl, hu, hw⟩, hd2, hr, hWr, hw', hv⟩, rfl, rfl⟩)
      · omega
      · exact ⟨by omega, ⟨hl, hr⟩, ⟨hWl, hWr, hw.trans hw'.symm⟩, hu, hv⟩

/-- all representations in the catalogue have root values in the alphabet -/
lemma RepCat_eq_biUnion (hH : 2 ≤ S.H) :
    RepCat S.H S.D S.k₀ S.m₀ = (S.V ×ˢ S.V).biUnion fun p => S.Rset S.D S.k₀ S.m₀ p.1 p.2 := by
  classical
  ext R
  simp only [Finset.mem_biUnion, Finset.mem_product, Prod.exists, mem_Rset, mem_RepCat]
  constructor
  · rintro ⟨hW, hd, hh⟩
    have := rootvals_mem (D := S.D) hH (IsDesc.root S.k₀ S.m₀) hW (by omega) hh
    exact ⟨R.lval, R.rval, ⟨this.1, this.2⟩, hd, hh, hW, rfl, rfl⟩
  · rintro ⟨u, v, -, hd, hh, hW, -, -⟩
    exact ⟨hW, hd, hh⟩

end Setup

end Artigo
