import RequestProject.Budgets

/-!
# Section 9 — Complexity, truncation and stability

* the stream-length bound `L ≤ S_D (2⌊log₂|𝓛_H|⌋ + 2)`,
* Theorem 9.1 (complexity in number of states, in the unit-cost model: the dynamic programme
  examines one candidate per (internal node, state, intermediate value) and stores one entry per
  (node, state)),
* Proposition 9.3 (convergence of the penalized minima under truncation; stabilization of the
  canonical selector),
* Proposition 9.4 (an exact selector may be discontinuous).
-/

namespace Artigo

open Set LTree Filter Topology

/-! ## Operation counts -/

/-- the cells of the dense table: descendants `(r, j)` of `K` at relative depth `r ≤ D` -/
def cellsD (D : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (D + 1)).biUnion fun r => (Finset.range (2 ^ r)).image fun j => (r, j)

/-- the internal cells (relative depth `r < D`), at which the recursion minimizes over `w` -/
def internalCells (D : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range D).biUnion fun r => (Finset.range (2 ^ r)).image fun j => (r, j)

lemma card_levels (D : ℕ) :
    ((Finset.range D).biUnion fun r => (Finset.range (2 ^ r)).image fun j => (r, j)).card =
      2 ^ D - 1 := by
  rw [Finset.card_biUnion]
  · have : ∀ r ∈ Finset.range D, ((Finset.range (2 ^ r)).image fun j => (r, j)).card = 2 ^ r := by
      intro r _
      rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h), Finset.card_range]
    rw [Finset.sum_congr rfl this]
    clear this
    induction D with
    | zero => simp
    | succ D ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      have := Nat.one_le_two_pow (n := D)
      omega
  · intro r _ r' _ hrr'
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hp hp'
    simp only [Finset.mem_image] at hp hp'
    obtain ⟨j, -, rfl⟩ := hp
    obtain ⟨j', -, h⟩ := hp'
    exact hrr' (congrArg Prod.fst h).symm

/-- `|cells| = S_D = 2^{D+1} - 1` -/
lemma card_cellsD (D : ℕ) : (cellsD D).card = 2 ^ (D + 1) - 1 := card_levels (D + 1)

lemma card_internalCells_le (D : ℕ) : (internalCells D).card ≤ 2 ^ (D + 1) - 1 := by
  unfold internalCells; rw [card_levels]
  have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (Nat.le_succ D)
  omega

/-- the pairs of budgets `(n, n_L)` with `1 ≤ n ≤ N`, `1 ≤ n_L < n` -/
def budgetPairs (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 N).biUnion fun n => (Finset.Ico 1 n).image fun nL => (n, nL)

lemma card_budgetPairs_le (N : ℕ) : (budgetPairs N).card ≤ N ^ 2 := by
  have h : budgetPairs N ⊆ Finset.Icc 1 N ×ˢ Finset.Icc 1 N := by
    intro p hp
    simp only [budgetPairs, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_image,
      Finset.mem_Ico] at hp
    obtain ⟨n, ⟨h1, h2⟩, nL, ⟨h3, h4⟩, rfl⟩ := hp
    simp only [Finset.mem_product, Finset.mem_Icc]; omega
  calc _ ≤ _ := Finset.card_le_card h
    _ = N ^ 2 := by simp [sq]

namespace Setup

variable (S : Setup)

/-- **Theorem 9.1 (complexidade em número de estados)**. Write `M = |𝒱_{D,H}(K)|` and
`S_D = 2^{D+1} - 1`. In the dense implementation of the variable-tree recursion,
(i) the table has `S_D M²` entries (one cost and one pointer per node and state);
(ii) the transitions — one candidate `w` per internal node and state `(u,v)` — number at most
`S_D M³`;
(iii) with a budget of up to `N` leaves, the table has `S_D N M²` entries and the transitions
(one per internal node, triple `(u,w,v)` and budget pair `n_L + n_R = n ≤ N`) number at most
`S_D N² M³`;
(iv) computing every local loss directly over the `P` observations costs `S_D P M²` operations;
(v) with `M ≤ 36 H⁶` (Lemma 4.4), the transitions number at most `36³ S_D H¹⁸`. -/
theorem state_complexity (hH : 2 ≤ S.H) (N : ℕ) :
    (cellsD S.D ×ˢ (S.V ×ˢ S.V)).card = (2 ^ (S.D + 1) - 1) * S.V.card ^ 2 ∧
    (internalCells S.D ×ˢ (S.V ×ˢ S.V ×ˢ S.V)).card ≤ (2 ^ (S.D + 1) - 1) * S.V.card ^ 3 ∧
    (cellsD S.D ×ˢ (S.V ×ˢ S.V) ×ˢ Finset.Icc 1 N).card = (2 ^ (S.D + 1) - 1) * N * S.V.card ^ 2 ∧
    (internalCells S.D ×ˢ (S.V ×ˢ S.V ×ˢ S.V) ×ˢ budgetPairs N).card ≤
      (2 ^ (S.D + 1) - 1) * N ^ 2 * S.V.card ^ 3 ∧
    (cellsD S.D ×ˢ (S.V ×ˢ S.V) ×ˢ Finset.range S.data.length).card =
      (2 ^ (S.D + 1) - 1) * S.data.length * S.V.card ^ 2 ∧
    (internalCells S.D ×ˢ (S.V ×ˢ S.V ×ˢ S.V)).card ≤ (2 ^ (S.D + 1) - 1) * (36 ^ 3 * S.H ^ 18) := by
  have hM : S.V.card ≤ 36 * S.H ^ 6 := (value_alphabet (D := S.D) (k₀ := S.k₀) (m₀ := S.m₀) hH).2.2.2.2
  have hI := card_internalCells_le S.D
  simp only [Finset.card_product, card_cellsD, Nat.card_Icc, Finset.card_range, Nat.add_sub_cancel]
  refine ⟨by ring, ?_, by ring, ?_, by ring, ?_⟩
  · calc _ ≤ (2 ^ (S.D + 1) - 1) * (S.V.card * (S.V.card * S.V.card)) := Nat.mul_le_mul_right _ hI
      _ = _ := by ring
  · calc _ ≤ (2 ^ (S.D + 1) - 1) * (S.V.card * (S.V.card * S.V.card) * N ^ 2) :=
          Nat.mul_le_mul hI (Nat.mul_le_mul_left _ (card_budgetPairs_le N))
      _ = _ := by ring
  · calc _ ≤ (2 ^ (S.D + 1) - 1) * ((36 * S.H ^ 6) * ((36 * S.H ^ 6) * (36 * S.H ^ 6))) :=
          Nat.mul_le_mul hI (Nat.mul_le_mul hM (Nat.mul_le_mul hM hM))
      _ = _ := by ring

end Setup

/-- the number of nodes of a tree is at most `S_D` when its depth is at most `D` -/
lemma numNodes_le {T : LTree} {D : ℕ} (hD : T.depth ≤ D) :
    T.numLeaves + T.numInternal ≤ 2 ^ (D + 1) - 1 := by
  have h1 := numInternal_eq T
  have h2 := (numLeaves_le_pow_depth T).trans (Nat.pow_le_pow_right (by norm_num) hD)
  rw [pow_succ]; omega

lemma serRec_length_le {H : ℕ} : ∀ T : LTree, T.maxHeight ≤ H →
    (serRec T).length ≤ (T.numLeaves + T.numInternal) * (2 * Nat.log 2 (LH H).card + 2) := by
  intro T
  induction T with
  | leaf a =>
    intro h
    have ha : a.height ≤ H := by rw [maxHeight_le_iff] at h; exact h a (by simp [leaves])
    have hn := nSharp_lt ha
    have : Nat.log 2 (nSharp a + 1) ≤ Nat.log 2 (LH H).card := Nat.log_mono_right (by omega)
    simp only [serRec, List.length_cons, gamma_length, numLeaves, leaves, List.length_nil,
      numInternal, Nat.zero_add, add_zero, one_mul]
    omega
  | node l r ihl ihr =>
    intro h
    rw [maxHeight_node] at h
    have := ihl h.1; have := ihr h.2
    simp only [serRec, List.length_cons, List.length_append, numLeaves_node, numInternal]
    nlinarith

/-- **the stream-length bound**: `L = max_R |ser_rec(R)| ≤ S_D (2⌊log₂|𝓛_H|⌋ + 2)` over the
catalogue `𝔑_{D,H}(K)` -/
theorem stream_length {H D k₀ : ℕ} {m₀ : ℤ} : ∀ R ∈ RepCat H D k₀ m₀,
    (serRec R).length ≤ (2 ^ (D + 1) - 1) * (2 * Nat.log 2 (LH H).card + 2) := by
  intro R hR
  obtain ⟨-, hd, hh⟩ := mem_RepCat.mp hR
  exact (serRec_length_le R hh).trans (Nat.mul_le_mul_right _ (numNodes_le hd))

/-! ## Proposition 9.3 -/

/-- extended rationals as extended reals -/
noncomputable def toE : WithTop ℚ → EReal
  | ⊤ => ⊤
  | (q : ℚ) => ((q : ℝ) : EReal)

lemma toE_mono : Monotone toE := by
  intro a b h
  cases b with
  | top => cases a <;> simp [toE]
  | coe b =>
    cases a with
    | top => simp at h
    | coe a =>
      simp only [toE, EReal.coe_le_coe_iff, Rat.cast_le]
      exact_mod_cast h

lemma toE_inf {ι : Type*} (s : Finset ι) (g : ι → WithTop ℚ) :
    toE (s.inf g) = ⨅ x ∈ s, toE (g x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [toE]
  | insert a s _ ih =>
    rw [Finset.inf_insert, Finset.iInf_insert, ← ih]
    exact toE_mono.map_min

namespace Setup

variable (S : Setup)

/-- the same problem with truncation levels `(D, H)` -/
def withDH (D H : ℕ) : Setup := { S with D := D, H := H }

/-- the cost of a representation as an extended real -/
noncomputable def costE (R : LTree) : EReal := ((S.costT R : ℝ) : EReal)

/-- the value `C⋆_{D,H}(K)` as an extended real -/
noncomputable def CstarE (D H : ℕ) : EReal := toE (S.withDH D H).Cstar

lemma CstarE_eq {D H : ℕ} (hH : 2 ≤ H) :
    S.CstarE D H = ⨅ R ∈ RepCat H D S.k₀ S.m₀, S.costE R := by
  unfold CstarE
  rw [((S.withDH D H).variable_global hH).1, toE_inf]
  rfl

/-- **Proposition 9.3 (convergência dos mínimos penalizados)**: (i) `C⋆_{D,H}(K)` is
non-increasing separately in `D` and in `H`; (ii) `inf_{D,H} C⋆_{D,H}(K) = inf_{R ∈ 𝔑_∞(K)} cost(R)`;
(iii) along every componentwise non-decreasing and cofinal sequence `(D_j, H_j)` the values
converge to this infimum; (iv) if the infimum is attained, the global minimizer of least key `κ`
lies in a finite catalogue, and from every truncation containing it on, the canonical selector
(the `κ`-least representation of the catalogue) is this minimizer. (Heights `H ≥ 2` are used,
since no atom has height below `2`.) -/
theorem truncation_convergence :
    (∀ {D D' H : ℕ}, 2 ≤ H → D ≤ D' → S.CstarE D' H ≤ S.CstarE D H) ∧
    (∀ {D H H' : ℕ}, 2 ≤ H → H ≤ H' → S.CstarE D H' ≤ S.CstarE D H) ∧
    (⨅ (D : ℕ) (H : ℕ) (_ : 2 ≤ H), S.CstarE D H) = ⨅ (R : LTree) (_ : WF S.k₀ S.m₀ R), S.costE R ∧
    (∀ (Dj Hj : ℕ → ℕ), Monotone Dj → Monotone Hj → Tendsto Dj atTop atTop →
      Tendsto Hj atTop atTop → (∀ j, 2 ≤ Hj j) →
      Tendsto (fun j => S.CstarE (Dj j) (Hj j)) atTop
        (𝓝 (⨅ (R : LTree) (_ : WF S.k₀ S.m₀ R), S.costE R))) ∧
    ((∃ R₀, WF S.k₀ S.m₀ R₀ ∧ ∀ R, WF S.k₀ S.m₀ R → S.costT R₀ ≤ S.costT R) →
      ∃ Rs : LTree, WF S.k₀ S.m₀ Rs ∧ (∀ R, WF S.k₀ S.m₀ R → S.costT Rs ≤ S.costT R) ∧
        (∀ R, WF S.k₀ S.m₀ R → (∀ R', WF S.k₀ S.m₀ R' → S.costT R ≤ S.costT R') →
          S.kappa Rs ≤ S.kappa R) ∧
        ∃ D₀ H₀ : ℕ, ∀ D H, D₀ ≤ D → H₀ ≤ H → Rs ∈ RepCat H D S.k₀ S.m₀ ∧
          ∀ R' ∈ RepCat H D S.k₀ S.m₀, S.kappa Rs ≤ S.kappa R') := by
  classical
  have hmonoD : ∀ {D D' H : ℕ}, 2 ≤ H → D ≤ D' → S.CstarE D' H ≤ S.CstarE D H := by
    intro D D' H hH hD
    rw [S.CstarE_eq hH, S.CstarE_eq hH]
    exact biInf_mono fun R hR => RepCat_mono hD le_rfl hR
  have hmonoH : ∀ {D H H' : ℕ}, 2 ≤ H → H ≤ H' → S.CstarE D H' ≤ S.CstarE D H := by
    intro D H H' hH hHH
    rw [S.CstarE_eq hH, S.CstarE_eq (hH.trans hHH)]
    exact biInf_mono fun R hR => RepCat_mono le_rfl hHH hR
  -- every finite representation enters a catalogue
  have hle_of : ∀ R, WF S.k₀ S.m₀ R → ∀ D H, 2 ≤ H → R.depth ≤ D → R.maxHeight ≤ H →
      S.CstarE D H ≤ S.costE R := by
    intro R hR D H hH hD hh
    rw [S.CstarE_eq hH]
    exact biInf_le _ (mem_RepCat.mpr ⟨hR, hD, hh⟩)
  have hge : ∀ D H, 2 ≤ H → (⨅ (R : LTree) (_ : WF S.k₀ S.m₀ R), S.costE R) ≤ S.CstarE D H := by
    intro D H hH
    rw [S.CstarE_eq hH]
    exact le_iInf₂ fun R hR => biInf_le _ (mem_RepCat.mp hR).1
  have hinf : (⨅ (D : ℕ) (H : ℕ) (_ : 2 ≤ H), S.CstarE D H) =
      ⨅ (R : LTree) (_ : WF S.k₀ S.m₀ R), S.costE R := by
    apply le_antisymm
    · refine le_iInf₂ fun R hR => ?_
      exact (iInf_le _ R.depth).trans ((iInf_le _ (max 2 R.maxHeight)).trans
        ((iInf_le _ (le_max_left _ _)).trans (hle_of R hR _ _ (le_max_left _ _) le_rfl
          (le_max_right _ _))))
    · exact le_iInf fun D => le_iInf fun H => le_iInf fun hH => hge D H hH
  refine ⟨hmonoD, hmonoH, hinf, ?_, ?_⟩
  · intro Dj Hj hDm hHm hDt hHt h2
    have hanti : Antitone fun j => S.CstarE (Dj j) (Hj j) := by
      intro i j hij
      exact (hmonoD (h2 j) (hDm hij)).trans (hmonoH (h2 i) (hHm hij))
    convert tendsto_atTop_iInf hanti using 2
    apply le_antisymm
    · exact le_iInf fun j => hge _ _ (h2 j)
    · refine le_iInf₂ fun R hR => ?_
      obtain ⟨j1, hj1⟩ := (tendsto_atTop.mp hDt R.depth).exists_forall_of_atTop
      obtain ⟨j2, hj2⟩ := (tendsto_atTop.mp hHt R.maxHeight).exists_forall_of_atTop
      exact (iInf_le _ (max j1 j2)).trans (hle_of R hR _ _ (h2 _) (hj1 _ (le_max_left _ _))
        (hj2 _ (le_max_right _ _)))
  · rintro ⟨R₀, hR₀, hmin₀⟩
    let G : LTree → Prop := fun R => WF S.k₀ S.m₀ R ∧ ∀ R', WF S.k₀ S.m₀ R' → S.costT R ≤ S.costT R'
    have hG : ∃ n, ∃ R, G R ∧ slRank (serRec R) = n := ⟨_, R₀, ⟨hR₀, hmin₀⟩, rfl⟩
    obtain ⟨Rs, hRs, hkey⟩ := Nat.find_spec hG
    have hleast : ∀ R, G R → slRank (serRec Rs) ≤ slRank (serRec R) := fun R hR => by
      rw [hkey]; exact Nat.find_min' hG ⟨R, hR, rfl⟩
    have hkap : ∀ R, WF S.k₀ S.m₀ R → S.kappa Rs ≤ S.kappa R := by
      intro R hR
      rcases (hRs.2 R hR).lt_or_eq with hlt | heq
      · exact Prod.Lex.toLex_le_toLex.mpr (Or.inl hlt)
      · have hGR : G R := ⟨hR, fun R' hR' => heq ▸ hRs.2 R' hR'⟩
        exact Prod.Lex.toLex_le_toLex.mpr (Or.inr ⟨heq, hleast R hGR⟩)
    refine ⟨Rs, hRs.1, hRs.2, fun R hR _ => hkap R hR, Rs.depth, Rs.maxHeight,
      fun D H hD hH => ⟨mem_RepCat.mpr ⟨hRs.1, hD, hH⟩, fun R' hR' => hkap R' (mem_RepCat.mp hR').1⟩⟩

end Setup

/-! ## Proposition 9.4 -/

/-- `g₊(x) = x` on `K = [0,1]` -/
def gPlus : Atom := ⟨0, 0, 1 / 2, 1, by norm_num⟩

/-- `g₋(x) = -x` on `K = [0,1]` -/
def gMinus : Atom := ⟨0, 0, -1 / 2, -1, by norm_num⟩

/-- the cost of an atom for the single observation `(1, z)` (quadratic loss) -/
noncomputable def costObs (z : ℝ) (a : Atom) : ℝ := (z - a.eval 1) ^ 2

/-- **Proposition 9.4 (um seletor exato pode ser descontínuo)**: `g₊(x) = x` and `g₋(x) = -x` are
atoms of height `2` on `K = [0,1]`, with `‖g₊ - g₋‖_{∞,[0,1]} = 2`; for the single observation
`(1,z)` the costs are `(z-1)²` and `(z+1)²`; and every selector `z ↦ sel(z) ∈ {g₊, g₋}` returning
a minimizer of the cost (with any deterministic tie-break) is discontinuous at `z = 0` in the
uniform norm: there are data `z` arbitrarily close to `0` with
`sup_{x ∈ [0,1]} |sel(z)(x) - sel(0)(x)| = 2`. -/
theorem instability :
    gPlus.height = 2 ∧ gMinus.height = 2 ∧
    (∀ x : ℝ, gPlus.eval x = x) ∧ (∀ x : ℝ, gMinus.eval x = -x) ∧
    (⨆ x ∈ Icc (0 : ℝ) 1, |gPlus.eval x - gMinus.eval x|) = 2 ∧
    (∀ z : ℝ, costObs z gPlus = (z - 1) ^ 2 ∧ costObs z gMinus = (z + 1) ^ 2) ∧
    ∀ sel : ℝ → Atom, (∀ z, (sel z = gPlus ∨ sel z = gMinus) ∧
        costObs z (sel z) ≤ costObs z gPlus ∧ costObs z (sel z) ≤ costObs z gMinus) →
      ∀ δ > 0, ∃ z, |z| < δ ∧ (⨆ x ∈ Icc (0 : ℝ) 1, |(sel z).eval x - (sel 0).eval x|) = 2 := by
  have hp : ∀ x : ℝ, gPlus.eval x = x := by
    intro x; simp [gPlus, Atom.eval, Atom.x0]
  have hm : ∀ x : ℝ, gMinus.eval x = -x := by
    intro x; simp [gMinus, Atom.eval, Atom.x0]; ring
  have hsup : ∀ (a b : Atom), (∀ x : ℝ, a.eval x - b.eval x = 2 * x ∨ a.eval x - b.eval x = -2 * x) →
      (⨆ x ∈ Icc (0 : ℝ) 1, |a.eval x - b.eval x|) = 2 := by
    intro a b hab
    have hpt : ∀ x : ℝ, (⨆ (_ : x ∈ Icc (0 : ℝ) 1), |a.eval x - b.eval x|) ≤ 2 := by
      intro x
      by_cases hx : x ∈ Icc (0 : ℝ) 1
      · rw [ciSup_pos hx]
        rcases hab x with h | h <;> rw [h] <;> rw [abs_le] <;> constructor <;> linarith [hx.1, hx.2]
      · simp [hx]
    apply le_antisymm (ciSup_le hpt)
    have hb : BddAbove (Set.range fun x : ℝ => ⨆ (_ : x ∈ Icc (0 : ℝ) 1), |a.eval x - b.eval x|) :=
      ⟨2, by rintro _ ⟨x, rfl⟩; exact hpt x⟩
    refine le_trans ?_ (le_ciSup hb 1)
    rw [ciSup_pos (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1)]
    rcases hab 1 with h | h <;> rw [h] <;> norm_num
  have hcost : ∀ z : ℝ, costObs z gPlus = (z - 1) ^ 2 ∧ costObs z gMinus = (z + 1) ^ 2 := by
    intro z
    constructor
    · simp only [costObs, hp]
    · simp only [costObs, hm, sub_neg_eq_add]
  refine ⟨by decide +kernel, by decide +kernel, hp, hm, hsup _ _ (fun x => Or.inl (by rw [hp, hm]; ring)), hcost, ?_⟩
  intro sel hsel δ hδ
  -- the selections at `±δ/2` are forced
  have hpos : sel (δ / 2) = gPlus := by
    rcases (hsel (δ / 2)).1 with h | h
    · exact h
    · have := (hsel (δ / 2)).2.1
      rw [h, (hcost _).1, (hcost _).2] at this
      nlinarith
  have hneg : sel (-(δ / 2)) = gMinus := by
    rcases (hsel (-(δ / 2))).1 with h | h
    · have := (hsel (-(δ / 2))).2.2
      rw [h, (hcost _).1, (hcost _).2] at this
      nlinarith
    · exact h
  have habs : |δ / 2| < δ := by rw [abs_of_pos (by linarith)]; linarith
  rcases (hsel 0).1 with h0 | h0
  · refine ⟨-(δ / 2), by rwa [abs_neg], ?_⟩
    rw [hneg, h0]
    exact hsup _ _ (fun x => Or.inr (by rw [hp, hm]; ring))
  · refine ⟨δ / 2, habs, ?_⟩
    rw [hpos, h0]
    exact hsup _ _ (fun x => Or.inl (by rw [hp, hm]; ring))

end Artigo
