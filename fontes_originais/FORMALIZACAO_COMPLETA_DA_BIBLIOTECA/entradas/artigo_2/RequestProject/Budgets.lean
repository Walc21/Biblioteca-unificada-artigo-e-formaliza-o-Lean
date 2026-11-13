import RequestProject.DP
import RequestProject.Uniform

/-!
# Section 8 — Hard budgets and uniform error

* Theorem 8.1 (correctness under a leaf budget, and the optimum with at most `N` leaves),
* Theorem 8.2 (exact computation of the best truncated uniform error by a bottleneck recursion;
  inactivity of the depth constraint),
* Corollary 8.3 (convergence for continuous functions).
-/

namespace Artigo

open Set LTree Filter Topology

/-! ## Leaf-representation sets -/

namespace Setup

variable (S : Setup)

/-- a depth-`0` representation set is either a single admissible leaf or empty -/
lemma Rset_zero_cases (hH : 2 ≤ S.H) (k : ℕ) (m : ℤ) (u v : ℚ) :
    (∃ b : Atom, b.height ≤ S.H ∧ b.k = k ∧ b.m = m ∧ b.lval = u ∧ b.rval = v ∧
      S.Rset 0 k m u v = {leaf b}) ∨ ((u, v) ∉ PH S.H k m ∧ S.Rset 0 k m u v = ∅) := by
  classical
  by_cases hp : (u, v) ∈ PH S.H k m
  · left
    obtain ⟨b, ⟨hb, hbk, hbm⟩, hbuv⟩ := (endpoint_dictionary hH).1.2.2 (Finset.mem_coe.mpr hp)
    simp only [Prod.mk.injEq] at hbuv
    obtain ⟨rfl, rfl⟩ := hbuv
    subst hbk hbm
    refine ⟨b, hb, rfl, rfl, rfl, rfl, ?_⟩
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
  · right
    refine ⟨hp, ?_⟩
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

open Classical in
/-- `𝔑_{d,H}(J;u,v)` restricted to representations with exactly `n` leaves -/
noncomputable def RsetN (d n k : ℕ) (m : ℤ) (u v : ℚ) : Finset LTree :=
  (S.Rset d k m u v).filter fun R => R.numLeaves = n

lemma mem_RsetN {d n k : ℕ} {m : ℤ} {u v : ℚ} {R : LTree} :
    R ∈ S.RsetN d n k m u v ↔ R ∈ S.Rset d k m u v ∧ R.numLeaves = n := by
  classical
  unfold RsetN; rw [Finset.mem_filter]

lemma RsetN_zero (n k : ℕ) (m : ℤ) (u v : ℚ) :
    S.RsetN 0 n k m u v = if n = 1 then S.Rset 0 k m u v else ∅ := by
  classical
  ext R
  rw [mem_RsetN]
  constructor
  · rintro ⟨hR, hn⟩
    have hR' := (S.mem_Rset).mp hR
    cases R with
    | node l r => simp [depth] at hR'
    | leaf a =>
      simp only [numLeaves, leaves, List.length_singleton] at hn
      rw [if_pos hn.symm]; exact hR
  · intro h
    split_ifs at h with hn
    · refine ⟨h, ?_⟩
      have hR' := (S.mem_Rset).mp h
      cases R with
      | node l r => simp [depth] at hR'
      | leaf a => simp [numLeaves, leaves, hn]
    · simp at h

lemma RsetN_succ_one {d k : ℕ} {m : ℤ} (u v : ℚ) : S.RsetN (d + 1) 1 k m u v = S.Rset 0 k m u v := by
  classical
  ext R
  rw [mem_RsetN, mem_Rset, mem_Rset]
  cases R with
  | leaf a => simp [depth, numLeaves, leaves]
  | node l r =>
    simp only [depth, numLeaves_node]
    constructor
    · rintro ⟨-, h⟩; have := numLeaves_pos l; have := numLeaves_pos r; omega
    · rintro ⟨h, -⟩; omega

/-- **root decomposition with a leaf count**: for `n ≠ 1`, a representation with exactly `n`
leaves is a node whose children have `n_L + n_R = n` leaves, `n_L, n_R ≥ 1` -/
lemma RsetN_succ (hH : 2 ≤ S.H) {d k r n : ℕ} {m : ℤ} (hd : IsDesc S.k₀ S.m₀ k m r)
    (hdD : r + (d + 1) ≤ S.D) (hn : n ≠ 1) (u v : ℚ) :
    S.RsetN (d + 1) n k m u v = (Finset.Ico 1 n).biUnion fun nL => S.V.biUnion fun w =>
      (S.RsetN d nL (k + 1) (2 * m) u w ×ˢ S.RsetN d (n - nL) (k + 1) (2 * m + 1) w v).image
        fun p => node p.1 p.2 := by
  classical
  ext R
  simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_product, Prod.exists, mem_RsetN,
    mem_Rset, Finset.mem_Ico]
  cases R with
  | leaf a =>
    simp only [numLeaves, leaves, List.length_singleton, reduceCtorEq, and_false, exists_false,
      iff_false, not_and]
    intro _ h; exact hn h.symm
  | node l r' =>
    simp only [depth, node.injEq, maxHeight_node, WF, LTree.lval, LTree.rval, numLeaves_node]
    constructor
    · rintro ⟨⟨hdp, ⟨hl, hr⟩, ⟨hWl, hWr, hlr⟩, hu, hv⟩, hnn⟩
      have := numLeaves_pos l; have := numLeaves_pos r'
      refine ⟨l.numLeaves, ⟨by omega, by omega⟩, l.rval, ?_, l, r', ⟨⟨⟨by omega, hl, hWl, hu, rfl⟩,
        rfl⟩, ⟨by omega, hr, hWr, hlr.symm, hv⟩, by omega⟩, rfl, rfl⟩
      exact (rootvals_mem hH hd.left hWl (by omega) hl).2
    · rintro ⟨nL, ⟨h1, h2⟩, w, -, l', r'', ⟨⟨⟨hd1, hl, hWl, hu, hw⟩, hnl⟩, ⟨hd2, hr, hWr, hw', hv⟩,
        hnr⟩, rfl, rfl⟩
      exact ⟨⟨by omega, ⟨hl, hr⟩, ⟨hWl, hWr, hw.trans hw'.symm⟩, hu, hv⟩, by omega⟩

/-- the catalogue with at most `N` leaves, split by leaf count and boundary values -/
lemma catalogN_eq_biUnion (hH : 2 ≤ S.H) (N : ℕ) :
    ((RepCat S.H S.D S.k₀ S.m₀).filter fun R => R.numLeaves ≤ N) =
      (Finset.Icc 1 (min N (2 ^ S.D)) ×ˢ (S.V ×ˢ S.V)).biUnion
        fun q => S.RsetN S.D q.1 S.k₀ S.m₀ q.2.1 q.2.2 := by
  classical
  ext R
  simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_product, Finset.mem_Icc, Prod.exists,
    mem_RsetN, mem_Rset, mem_RepCat]
  constructor
  · rintro ⟨⟨hW, hd, hh⟩, hN⟩
    have := rootvals_mem (D := S.D) hH (IsDesc.root S.k₀ S.m₀) hW (by omega) hh
    have h1 := numLeaves_pos R
    have h2 : R.numLeaves ≤ 2 ^ S.D :=
      (numLeaves_le_pow_depth R).trans (Nat.pow_le_pow_right (by norm_num) hd)
    exact ⟨R.numLeaves, R.lval, R.rval, ⟨⟨h1, le_min hN h2⟩, this.1, this.2⟩,
      ⟨hd, hh, hW, rfl, rfl⟩, rfl⟩
  · rintro ⟨n, u, v, ⟨⟨-, hn⟩, -⟩, ⟨hd, hh, hW, -, -⟩, rfl⟩
    exact ⟨⟨hW, hd, hh⟩, le_trans hn (min_le_left _ _)⟩

/-! ## Theorem 8.1 -/

/-- the leaf-budget recursion `C_{d,n}(J;u,v)`:
`C_{0,1} = Φ_H`, `C_{0,n} = +∞` (`n ≠ 1`), `C_{d,1} = Φ_H`, and for `n ≥ 2`
`C_{d,n} = λ_bits + λ_split + min_{n_L+n_R=n, n_L,n_R ≥ 1} min_{w ∈ 𝒱} {C_{d-1,n_L}(J_L;u,w) + C_{d-1,n_R}(J_R;w,v)}`
(for `n = 0` the minimum is empty and the value is `+∞`) -/
noncomputable def Cb : ℕ → ℕ → ℕ → ℤ → ℚ → ℚ → WithTop ℚ
  | 0, n, k, m, u, v => if n = 1 then S.Phi k m u v else ⊤
  | d + 1, n, k, m, u, v => if n = 1 then S.Phi k m u v else
      ((S.lb + S.ls : ℚ) : WithTop ℚ) + (Finset.Ico 1 n).inf fun nL => S.V.inf fun w =>
        Cb d nL (k + 1) (2 * m) u w + Cb d (n - nL) (k + 1) (2 * m + 1) w v

/-- **Theorem 8.1 (correção sob orçamento de folhas)**: `C_{d,n}(J;u,v)` is exactly the least
cost among representations of depth `≤ d`, height `≤ H`, boundary values `(u,v)` and exactly `n`
leaves (`+∞` if there is none). -/
theorem leaf_budget (hH : 2 ≤ S.H) : ∀ (d n k r : ℕ) (m : ℤ) (u v : ℚ),
    IsDesc S.k₀ S.m₀ k m r → r + d ≤ S.D →
      S.Cb d n k m u v = (S.RsetN d n k m u v).inf S.costW := by
  classical
  intro d
  induction d with
  | zero =>
    intro n k r m u v _ _
    rw [Cb, S.RsetN_zero]
    split_ifs
    · rw [S.Rset_zero_inf hH]
    · rfl
  | succ d ih =>
    intro n k r m u v hd hdD
    rw [Cb]
    split_ifs with hn
    · subst hn; rw [S.RsetN_succ_one, S.Rset_zero_inf hH]
    · rw [S.RsetN_succ hH hd hdD hn, Finset.inf_biUnion, const_add_inf]
      refine Finset.inf_congr rfl (fun nL _ => ?_)
      rw [Finset.inf_biUnion, const_add_inf]
      refine Finset.inf_congr rfl (fun w _ => ?_)
      rw [S.inf_glue', ih nL (k + 1) (r + 1) (2 * m) u w hd.left (by omega),
        ih (n - nL) (k + 1) (r + 1) (2 * m + 1) w v hd.right (by omega)]

/-- **Theorem 8.1 (optimum with at most `N` leaves)**:
`min_{1 ≤ n ≤ min{N, 2^D}, u,v ∈ 𝒱} C_{D,n}(K;u,v)` is the least cost over the representations of
the catalogue `𝔑_{D,H}(K)` with at most `N` leaves. -/
theorem leaf_budget_atMost (hH : 2 ≤ S.H) (N : ℕ) :
    (Finset.Icc 1 (min N (2 ^ S.D)) ×ˢ (S.V ×ˢ S.V)).inf
        (fun q => S.Cb S.D q.1 S.k₀ S.m₀ q.2.1 q.2.2) =
      ((RepCat S.H S.D S.k₀ S.m₀).filter fun R => R.numLeaves ≤ N).inf S.costW := by
  classical
  rw [S.catalogN_eq_biUnion hH, Finset.inf_biUnion]
  refine Finset.inf_congr rfl (fun q _ => ?_)
  exact S.leaf_budget hH S.D q.1 S.k₀ 0 S.m₀ q.2.1 q.2.2 (IsDesc.root _ _) (by omega)

end Setup

/-! ## Uniform error -/

/-- the line `ℓ_{J;u,v}` on `J_{k,m}` with end values `u, v` -/
noncomputable def lineR (k : ℕ) (m : ℤ) (u v : ℚ) (x : ℝ) : ℝ :=
  (u : ℝ) + ((v : ℝ) - u) * 2 ^ k * (x - cL k m)

/-- the local uniform-error oracle `e_f(J;u,v) = ‖f - ℓ_{J;u,v}‖_{∞,J}` for admissible pairs, and
`+∞` for inadmissible ones -/
noncomputable def errU (f : ℝ → ℝ) (H k : ℕ) (m : ℤ) (u v : ℚ) : ENNReal :=
  if (u, v) ∈ PH H k m then ⨆ x ∈ cellIcc k m, ENNReal.ofReal |f x - lineR k m u v x| else ⊤

/-- the uniform error of `f` against an atom on its own cell -/
noncomputable def errAtom (f : ℝ → ℝ) (a : Atom) : ENNReal :=
  ⨆ x ∈ cellIcc a.k a.m, ENNReal.ofReal |f x - a.eval x|

/-- the bottleneck (maximum of the leaf errors) of a representation -/
noncomputable def bott (f : ℝ → ℝ) : LTree → ENNReal
  | leaf a => errAtom f a
  | node l r => max (bott f l) (bott f r)

/-- the global uniform error `‖f - Eval(R)‖_{∞,J_{k,m}}` -/
noncomputable def globErr (f : ℝ → ℝ) (k : ℕ) (m : ℤ) (R : LTree) : ENNReal :=
  ⨆ x ∈ cellIcc k m, ENNReal.ofReal |f x - R.eval k m x|

open Classical in
/-- `E^tree_{N,H,D}(f)_∞ = min {‖f - Eval(R)‖_{∞,K} : R ∈ 𝔑_{D,H}(K), |Λ(R)| ≤ N}` -/
noncomputable def Etree (f : ℝ → ℝ) (k₀ : ℕ) (m₀ : ℤ) (N H D : ℕ) : ENNReal :=
  ((RepCat H D k₀ m₀).filter fun R => R.numLeaves ≤ N).inf (globErr f k₀ m₀)

lemma max_inf_const {ι : Type*} (s : Finset ι) (f : ι → ENNReal) (c : ENNReal) :
    max c (s.inf f) = s.inf fun x => max c (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s _ ih =>
    rw [Finset.inf_insert, Finset.inf_insert, ← ih]
    exact max_min_distrib_left _ _ _

lemma inf_prod_max {ι κ : Type*} (s : Finset ι) (t : Finset κ) (f : ι → ENNReal) (g : κ → ENNReal) :
    (s ×ˢ t).inf (fun p => max (f p.1) (g p.2)) = max (s.inf f) (t.inf g) := by
  rw [Finset.inf_product_left, max_comm, max_inf_const]
  refine Finset.inf_congr rfl (fun x _ => ?_)
  rw [max_comm (t.inf g) (f x), max_inf_const]

lemma inf_glue_bott (f : ℝ → ℝ) (s t : Finset LTree) :
    ((s ×ˢ t).image fun p => node p.1 p.2).inf (bott f) = max (s.inf (bott f)) (t.inf (bott f)) := by
  classical
  rw [Finset.inf_image]
  exact inf_prod_max s t _ _

/-- the oracle value of an admissible atom is its own uniform error -/
lemma errU_atom (f : ℝ → ℝ) {H : ℕ} {a : Atom} (ha : a.height ≤ H) :
    errU f H a.k a.m a.lval a.rval = errAtom f a := by
  have h2 : 2 ≤ H := le_trans a.two_le_height ha
  have hmem : (a.lval, a.rval) ∈ PH H a.k a.m := (endpoint_dictionary h2).1.1 ⟨ha, rfl, rfl⟩
  unfold errU errAtom
  rw [if_pos hmem]
  simp only [lineR, ← Atom.eval_interp]

/-- for a continuous assembly, the global uniform error is the maximum of the leaf errors -/
lemma globErr_eq_bott (f : ℝ → ℝ) {k : ℕ} {m : ℤ} {R : LTree} (hR : WF k m R) :
    globErr f k m R = bott f R := by
  have hb : ∀ T : LTree, bott f T = ⨆ a ∈ T.leaves, errAtom f a := by
    intro T
    induction T with
    | leaf a => simp [bott, leaves]
    | node l r ihl ihr =>
      simp only [bott, leaves, List.mem_append, iSup_or, iSup_sup_eq, ihl, ihr]
  rw [hb]
  apply le_antisymm
  · refine iSup₂_le fun x hx => ?_
    obtain ⟨a, ha, hxa⟩ := exists_leaf_mem hR x hx
    rw [eval_leaf hR a ha x hxa]
    exact le_trans (le_iSup₂ (f := fun x (_ : x ∈ cellIcc a.k a.m) =>
      ENNReal.ofReal |f x - a.eval x|) x hxa) (le_iSup₂ (f := fun a (_ : a ∈ R.leaves) =>
        errAtom f a) a ha)
  · refine iSup₂_le fun a ha => iSup₂_le fun x hxa => ?_
    have hx := leaves_cell_sub hR a ha hxa
    rw [← eval_leaf hR a ha x hxa]
    exact le_iSup₂ (f := fun x (_ : x ∈ cellIcc k m) => ENNReal.ofReal |f x - R.eval k m x|) x hx

namespace Setup

variable (S : Setup)

/-- some leaf of a well-formed tree lies at the full depth -/
lemma _root_.Artigo.exists_leaf_deep : ∀ {k : ℕ} {m : ℤ} {T : LTree}, WF k m T →
    ∃ a ∈ T.leaves, a.k = k + T.depth := by
  intro k m T
  induction T generalizing k m with
  | leaf a => intro h; exact ⟨a, by simp [leaves], by simp [depth, h.1]⟩
  | node l r ihl ihr =>
    intro h
    obtain ⟨a, ha, hak⟩ := ihl h.1
    obtain ⟨b, hb, hbk⟩ := ihr h.2.1
    by_cases hlr : r.depth ≤ l.depth
    · exact ⟨a, by simp [leaves, ha], by simp only [depth]; omega⟩
    · exact ⟨b, by simp [leaves, hb], by simp only [depth]; omega⟩

/-- the bottleneck recursion `B_{d,n}(J;u,v)`: as `C_{d,n}`, with the leaf cost replaced by
`e_f` and the sum replaced by the maximum -/
noncomputable def Bb (f : ℝ → ℝ) : ℕ → ℕ → ℕ → ℤ → ℚ → ℚ → ENNReal
  | 0, n, k, m, u, v => if n = 1 then errU f S.H k m u v else ⊤
  | d + 1, n, k, m, u, v => if n = 1 then errU f S.H k m u v else
      (Finset.Ico 1 n).inf fun nL => S.V.inf fun w =>
        max (Bb f d nL (k + 1) (2 * m) u w) (Bb f d (n - nL) (k + 1) (2 * m + 1) w v)

/-- `B_{d,n}(J;u,v)` is the best bottleneck with fixed state and leaf count -/
theorem bottleneck_correctness (hH : 2 ≤ S.H) (f : ℝ → ℝ) : ∀ (d n k r : ℕ) (m : ℤ) (u v : ℚ),
    IsDesc S.k₀ S.m₀ k m r → r + d ≤ S.D →
      S.Bb f d n k m u v = (S.RsetN d n k m u v).inf (bott f) := by
  classical
  have hzero : ∀ (k : ℕ) (m : ℤ) (u v : ℚ), (S.Rset 0 k m u v).inf (bott f) = errU f S.H k m u v := by
    intro k m u v
    rcases S.Rset_zero_cases hH k m u v with ⟨b, hb, rfl, rfl, rfl, rfl, he⟩ | ⟨hp, he⟩
    · rw [he, Finset.inf_singleton, errU_atom f hb]; rfl
    · rw [he, Finset.inf_empty, errU, if_neg hp]
  intro d
  induction d with
  | zero =>
    intro n k r m u v _ _
    rw [Bb, S.RsetN_zero]
    split_ifs
    · rw [hzero]
    · rfl
  | succ d ih =>
    intro n k r m u v hd hdD
    rw [Bb]
    split_ifs with hn
    · subst hn; rw [S.RsetN_succ_one, hzero]
    · rw [S.RsetN_succ hH hd hdD hn, Finset.inf_biUnion]
      refine Finset.inf_congr rfl (fun nL _ => ?_)
      rw [Finset.inf_biUnion]
      refine Finset.inf_congr rfl (fun w _ => ?_)
      rw [inf_glue_bott, ih nL (k + 1) (r + 1) (2 * m) u w hd.left (by omega),
        ih (n - nL) (k + 1) (r + 1) (2 * m + 1) w v hd.right (by omega)]

/-- **Theorem 8.2 (cálculo exato do melhor erro truncado)**: under the oracle `e_f`,
`E^tree_{N,H,D}(f)_∞ = min_{1 ≤ n ≤ min{N,2^D}, u,v ∈ 𝒱} B_{D,n}(K;u,v)`; and if
`D ≥ max{0, H - k₀ - 1}` the depth constraint is inactive: no atom of `𝓛_H` supported on a
descendant of `K` lies below relative depth `D`, so every continuous assembly on `K` with atoms in
`𝓛_H` already has depth `≤ D`. -/
theorem bottleneck (hH : 2 ≤ S.H) (f : ℝ → ℝ) (N : ℕ) :
    Etree f S.k₀ S.m₀ N S.H S.D =
      (Finset.Icc 1 (min N (2 ^ S.D)) ×ˢ (S.V ×ˢ S.V)).inf
        (fun q => S.Bb f S.D q.1 S.k₀ S.m₀ q.2.1 q.2.2) ∧
    (S.H - S.k₀ - 1 ≤ S.D →
      (∀ a : Atom, a.height ≤ S.H → S.k₀ ≤ a.k → a.k - S.k₀ ≤ S.D) ∧
      ∀ R : LTree, WF S.k₀ S.m₀ R → R.maxHeight ≤ S.H → R.depth ≤ S.D) := by
  classical
  refine ⟨?_, fun hD => ⟨fun a ha hk => ?_, fun R hR hh => ?_⟩⟩
  · unfold Etree
    rw [S.catalogN_eq_biUnion hH, Finset.inf_biUnion]
    refine Finset.inf_congr rfl (fun q _ => ?_)
    rw [S.bottleneck_correctness hH f S.D q.1 S.k₀ 0 S.m₀ q.2.1 q.2.2 (IsDesc.root _ _) (by omega)]
    refine Finset.inf_congr rfl (fun R hR => ?_)
    exact globErr_eq_bott f ((S.mem_Rset.mp (S.mem_RsetN.mp hR).1).2.2.1)
  · have := a.k_lt_height; omega
  · obtain ⟨a, ha, hak⟩ := exists_leaf_deep hR
    have := a.k_lt_height
    have := le_trans (le_maxHeight ha) hh
    omega

end Setup

/-- **Corollary 8.3 (convergência para funções contínuas)**: for every `f ∈ C(K)`,
`inf_{N,H,D} E^tree_{N,H,D}(f)_∞ = 0`; more precisely the errors tend to zero along any cofinal
sequence of triples `(N_j, H_j, D_j)` (monotonicity of the sequence is not needed). -/
theorem uniform_convergence {k₀ : ℕ} {m₀ : ℤ} {f : ℝ → ℝ} (hf : ContinuousOn f (cellIcc k₀ m₀)) :
    (⨅ (N : ℕ) (H : ℕ) (D : ℕ), Etree f k₀ m₀ N H D) = 0 ∧
    ∀ (N H D : ℕ → ℕ), Tendsto N atTop atTop → Tendsto H atTop atTop → Tendsto D atTop atTop →
      Tendsto (fun j => Etree f k₀ m₀ (N j) (H j) (D j)) atTop (𝓝 0) := by
  classical
  -- a single tree with small error
  have hsmall : ∀ ε : ENNReal, 0 < ε → ∃ T : LTree, WF k₀ m₀ T ∧ globErr f k₀ m₀ T ≤ ε := by
    intro ε hε
    obtain ⟨r, hr0, hr, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
    obtain ⟨T, hT, herr⟩ := assemblies_dense hf (ENNReal.ofReal_pos.mp hr)
    refine ⟨T, hT, le_trans (iSup₂_le fun x hx => ?_) hrε.le⟩
    exact ENNReal.ofReal_le_ofReal (herr x hx).le
  have hle : ∀ (T : LTree) (N H D : ℕ), WF k₀ m₀ T → T.numLeaves ≤ N → T.maxHeight ≤ H →
      T.depth ≤ D → Etree f k₀ m₀ N H D ≤ globErr f k₀ m₀ T := by
    intro T N H D hT hN hH hD
    exact Finset.inf_le (Finset.mem_filter.mpr ⟨mem_RepCat.mpr ⟨hT, hD, hH⟩, hN⟩)
  have htend : ∀ (N H D : ℕ → ℕ), Tendsto N atTop atTop → Tendsto H atTop atTop →
      Tendsto D atTop atTop → Tendsto (fun j => Etree f k₀ m₀ (N j) (H j) (D j)) atTop (𝓝 0) := by
    intro N H D hN hH hD
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    obtain ⟨T, hT, hTε⟩ := hsmall ε hε
    filter_upwards [tendsto_atTop.mp hN T.numLeaves, tendsto_atTop.mp hH T.maxHeight,
      tendsto_atTop.mp hD T.depth] with j h1 h2 h3
    exact le_trans (hle T _ _ _ hT h1 h2 h3) hTε
  refine ⟨le_antisymm ?_ bot_le, htend⟩
  have := htend id id id tendsto_id tendsto_id tendsto_id
  refine ge_of_tendsto this (Eventually.of_forall fun j => ?_)
  exact le_trans (iInf_le _ j) (le_trans (iInf_le _ j) (iInf_le _ j))

end Artigo
