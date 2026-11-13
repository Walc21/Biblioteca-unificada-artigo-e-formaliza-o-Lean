module
public import RequestProject.Normalization

/-!
# Seção 7: ordenação finita e cadeia normalizada

Formalização da Seção 7 (`sec:chain`).
-/

@[expose] public section

open scoped Classical

noncomputable section

namespace Montagens

open Atom

variable {α β : ℝ}

/-! ## Ordem auxiliar total dos átomos (Definição `def:sort`) -/

/-- A chave `ζ(a) = (L_ℚ(C(a)), a.k, a.m, a.y, a.s)` na ordem lexicográfica. -/
def zeta (a : Atom) : Lex (ℚ × Lex (ℕ × Lex (ℤ × Lex (ℚ × ℚ)))) :=
  toLex (LQ a.C, toLex (a.k, toLex (a.m, toLex (a.y, a.s))))

theorem zeta_injective : Function.Injective zeta := by
  intro a b h
  simp only [zeta, toLex_inj, Prod.mk.injEq] at h
  exact Atom.ext h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

/-- A ordem linear `◁` em `Atom` induzida por `ζ`. -/
instance atomLinearOrder : LinearOrder Atom := LinearOrder.lift' zeta zeta_injective

theorem atom_lt_iff (a b : Atom) : a < b ↔ zeta a < zeta b := Iff.rfl

/-- `sort : Finset Atom → List Atom`, por recursão bem fundada na cardinalidade:
`sort(∅) = []`, `sort(F) = a :: sort(F \ {a})` com `a = min_◁ F`. -/
def sortAtoms (F : Finset Atom) : List Atom :=
  if h : F.Nonempty then
    F.min' h :: sortAtoms (F.erase (F.min' h))
  else []
termination_by F.card
decreasing_by exact Finset.card_erase_lt_of_mem (Finset.min'_mem F h)

theorem sortAtoms_ne {F : Finset Atom} (h : F.Nonempty) :
    sortAtoms F = F.min' h :: sortAtoms (F.erase (F.min' h)) := by
  rw [sortAtoms, dif_pos h]

theorem sortAtoms_empty : sortAtoms ∅ = [] := by
  rw [sortAtoms, dif_neg (by simp)]

/-- Lema `lem:sort` (propriedades da lista ordenada). -/
theorem sortAtoms_props (F : Finset Atom) :
    (sortAtoms F).length = F.card ∧ (sortAtoms F).Nodup ∧
    (∀ a, a ∈ sortAtoms F ↔ a ∈ F) ∧ (sortAtoms F).Pairwise (· < ·) := by
  induction hn : F.card generalizing F with
  | zero =>
    rw [Finset.card_eq_zero] at hn; subst hn
    simp [sortAtoms_empty]
  | succ n ih =>
    have hne : F.Nonempty := by rw [← Finset.card_pos]; omega
    obtain ⟨h1, h2, h3, h4⟩ := ih (F.erase (F.min' hne))
      (by rw [Finset.card_erase_of_mem (Finset.min'_mem F hne)]; omega)
    rw [sortAtoms_ne hne]
    refine ⟨by simp [h1], ?_, ?_, ?_⟩
    · rw [List.nodup_cons]; refine ⟨?_, h2⟩
      rw [h3]; simp
    · intro a
      rw [List.mem_cons, h3, Finset.mem_erase]
      constructor
      · rintro (rfl | ⟨_, ha⟩); exact Finset.min'_mem F hne; exact ha
      · intro ha
        by_cases hm : a = F.min' hne
        · exact Or.inl hm
        · exact Or.inr ⟨hm, ha⟩
    · rw [List.pairwise_cons]; refine ⟨fun b hb => ?_, h4⟩
      rw [h3, Finset.mem_erase] at hb
      exact lt_of_le_of_ne (Finset.min'_le F b hb.2) (Ne.symm hb.1)

theorem LQ_le_of_lt {a b : Atom} (h : a < b) : LQ a.C ≤ LQ b.C := by
  rw [atom_lt_iff, zeta, zeta, Prod.Lex.toLex_lt_toLex] at h
  rcases h with h | ⟨h, -⟩
  · exact h.le
  · exact h.le

/-- Sob `Sep`, dois átomos distintos não têm o mesmo extremo esquerdo. -/
theorem LQ_ne_of_sep {F : Finset Atom} (hS : Sep F) {a b : Atom} (ha : a ∈ F) (hb : b ∈ F)
    (hab : a ≠ b) : LQ a.C ≠ LQ b.C := by
  intro hL
  have h := hS a ha b hb hab
  have h1 := (geometry a.C).2.2.2.2.1
  have h2 := (geometry b.C).2.2.2.2.1
  have hL' : L a.C = L b.C := by simp only [L, hL]
  have hne : (a.Oa ∩ b.Oa).Nonempty := by
    refine ⟨(L a.C + min (R a.C) (R b.C)) / 2, ⟨?_, ?_⟩, ?_, ?_⟩
    all_goals simp only [min_def]; split_ifs <;> linarith
  rw [h] at hne; exact Set.not_nonempty_empty hne

theorem sortAtoms_left_strict {F : Finset Atom} (hS : Sep F) :
    (sortAtoms F).Pairwise (fun a b => LQ a.C < LQ b.C) := by
  obtain ⟨-, -, hmem, hpw⟩ := sortAtoms_props F
  exact hpw.imp_of_mem (fun ha hb hab => lt_of_le_of_ne (LQ_le_of_lt hab)
    (LQ_ne_of_sep hS ((hmem _).1 ha) ((hmem _).1 hb) hab.ne))

/-! ## Tipo dos dados de cadeia (Definição `def:chain`) -/

/-- A estrutura `NormChain_K(Λ)`. -/
structure NormChain (α β : ℝ) (Λ : Finset Atom) where
  M : ℕ
  hM : 1 ≤ M
  a : Fin M → Atom
  t : Fin (M + 1) → ℚ
  a_inj : Function.Injective a
  a_image : Finset.univ.image a = NormK α β Λ
  t_lt : ∀ j : Fin M, t j.castSucc < t j.succ
  a_left : ∀ j : Fin M, LQ (a j).C = t j.castSucc
  a_right : ∀ j : Fin M, RQ (a j).C = t j.succ
  t_first : ((t 0 : ℚ) : ℝ) ≤ α
  t_last : β ≤ ((t (Fin.last M) : ℚ) : ℝ)
  t_inner : ∀ j : Fin (M + 1), 1 ≤ j.val → j.val < M →
    α < ((t j : ℚ) : ℝ) ∧ ((t j : ℚ) : ℝ) < β

theorem NormChain.Ja_eq {Λ : Finset Atom} (q : NormChain α β Λ) (j : Fin q.M) :
    (q.a j).Ja = Set.Icc ((q.t j.castSucc : ℚ) : ℝ) ((q.t j.succ : ℚ) : ℝ) := by
  simp only [Atom.Ja, J, L, R, q.a_left, q.a_right]

/-! ## Construção determinada da cadeia (Teorema `thm:chain`) -/

theorem normK_nonempty_of_localRep (hK : α < β) {g : CK α β} {Λ : Finset Atom}
    (h : LocalRep α β g Λ) : 1 ≤ (NormK α β Λ).card :=
  Finset.card_pos.2 (normalization hK h).2.1.2

/-- Os átomos `a_j = (sort(F))_j` da cadeia construída. -/
def chainAtoms (α β : ℝ) (Λ : Finset Atom) (j : Fin (NormK α β Λ).card) : Atom :=
  (sortAtoms (NormK α β Λ)).get ⟨j.val, by rw [(sortAtoms_props _).1]; exact j.isLt⟩

/-- Os nós `t_0 = L_ℚ(C(a_0))`, `t_{j+1} = R_ℚ(C(a_j))` da cadeia construída. -/
def chainNodes (α β : ℝ) (Λ : Finset Atom) (h0 : 1 ≤ (NormK α β Λ).card) :
    Fin ((NormK α β Λ).card + 1) → ℚ :=
  Fin.cases (LQ (chainAtoms α β Λ ⟨0, h0⟩).C) (fun j => RQ (chainAtoms α β Λ j).C)

theorem chainAtoms_inj (Λ : Finset Atom) : Function.Injective (chainAtoms α β Λ) := by
  intro i j h
  have hnd := (sortAtoms_props (NormK α β Λ)).2.1
  unfold chainAtoms at h
  have := (List.Nodup.get_inj_iff hnd).1 h
  ext; simpa using congrArg Fin.val this

theorem chainAtoms_mem (Λ : Finset Atom) (j : Fin (NormK α β Λ).card) :
    chainAtoms α β Λ j ∈ NormK α β Λ := by
  rw [← (sortAtoms_props _).2.2.1]; unfold chainAtoms; exact List.get_mem _ _

theorem chainAtoms_image (Λ : Finset Atom) :
    Finset.univ.image (chainAtoms α β Λ) = NormK α β Λ := by
  ext b
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩; exact chainAtoms_mem Λ j
  · intro hb
    rw [← (sortAtoms_props _).2.2.1, List.mem_iff_get] at hb
    obtain ⟨n, hn⟩ := hb
    refine ⟨⟨n.val, by rw [← (sortAtoms_props (NormK α β Λ)).1]; exact n.isLt⟩, ?_⟩
    rw [← hn]; rfl

theorem chainAtoms_left_lt {Λ : Finset Atom} (hS : Sep (NormK α β Λ))
    {i j : Fin (NormK α β Λ).card} (hij : i < j) :
    LQ (chainAtoms α β Λ i).C < LQ (chainAtoms α β Λ j).C := by
  have h := List.pairwise_iff_get.1 (sortAtoms_left_strict hS)
  exact h ⟨i.val, by rw [(sortAtoms_props _).1]; exact i.isLt⟩
    ⟨j.val, by rw [(sortAtoms_props _).1]; exact j.isLt⟩ (Fin.mk_lt_mk.2 hij)

theorem LQ_lt_RQ (c : Cell) : LQ c < RQ c := by
  have := (geometry c).2.1; linarith

theorem chainAtoms_R_le_L {Λ : Finset Atom} (hS : Sep (NormK α β Λ))
    {i j : Fin (NormK α β Λ).card} (hij : i < j) :
    RQ (chainAtoms α β Λ i).C ≤ LQ (chainAtoms α β Λ j).C := by
  have hne : chainAtoms α β Λ i ≠ chainAtoms α β Λ j :=
    fun h => (ne_of_lt hij) (chainAtoms_inj Λ h)
  have hO := hS _ (chainAtoms_mem Λ i) _ (chainAtoms_mem Λ j) hne
  have hLL := chainAtoms_left_lt hS hij
  have h1 := LQ_lt_RQ (chainAtoms α β Λ i).C
  have h2 := LQ_lt_RQ (chainAtoms α β Λ j).C
  simp only [Atom.Oa, O, L, R] at hO
  rcases separated_of_disjoint (by exact_mod_cast h1) (by exact_mod_cast h2) hO with h | h
  · exact_mod_cast h
  · have : RQ (chainAtoms α β Λ j).C ≤ LQ (chainAtoms α β Λ i).C := by exact_mod_cast h
    linarith

/-- Adjacência sem lacunas: `R(a_j) = L(a_{j+1})`. -/
theorem chainAtoms_adj (hK : α < β) {g : CK α β} {Λ : Finset Atom} (h : LocalRep α β g Λ)
    (j : ℕ) (hj : j + 1 < (NormK α β Λ).card) :
    RQ (chainAtoms α β Λ ⟨j, by omega⟩).C = LQ (chainAtoms α β Λ ⟨j + 1, hj⟩).C := by
  obtain ⟨-, ⟨hCov, -⟩, -, ⟨⟨hS, -, -⟩, -⟩, -⟩ := normalization hK h
  have hj0 : j < (NormK α β Λ).card := by omega
  set a := chainAtoms α β Λ
  have hle := chainAtoms_R_le_L hS (i := ⟨j, hj0⟩) (j := ⟨j + 1, hj⟩)
    (Fin.mk_lt_mk.2 (by omega))
  by_contra hne
  have hlt : RQ (a ⟨j, hj0⟩).C < LQ (a ⟨j + 1, hj⟩).C := lt_of_le_of_ne hle hne
  set z : ℚ := (RQ (a ⟨j, hj0⟩).C + LQ (a ⟨j + 1, hj⟩).C) / 2 with hz
  have hz1 : RQ (a ⟨j, hj0⟩).C < z := by rw [hz]; linarith
  have hz2 : z < LQ (a ⟨j + 1, hj⟩).C := by rw [hz]; linarith
  have hact1 := (mem_NormK.1 (chainAtoms_mem (α := α) (β := β) Λ ⟨j, hj0⟩)).2
  have hact2 := (mem_NormK.1 (chainAtoms_mem (α := α) (β := β) Λ ⟨j + 1, hj⟩)).2
  obtain ⟨u, ⟨-, hu2⟩, hu3, -⟩ := Set.nonempty_iff_ne_empty.2 hact1
  obtain ⟨v, ⟨hv1, -⟩, -, hv4⟩ := Set.nonempty_iff_ne_empty.2 hact2
  simp only [L, R] at hu2 hv1
  have hzα : α < (z : ℝ) := by
    have : ((RQ (a ⟨j, hj0⟩).C : ℚ) : ℝ) < z := by exact_mod_cast hz1
    linarith
  have hzβ : (z : ℝ) < β := by
    have : (z : ℝ) < ((LQ (a ⟨j + 1, hj⟩).C : ℚ) : ℝ) := by exact_mod_cast hz2
    linarith
  obtain ⟨b, hb, hzb⟩ := hCov z ⟨hzα.le, hzβ.le⟩
  rw [← chainAtoms_image Λ, Finset.mem_image] at hb
  obtain ⟨i, -, rfl⟩ := hb
  simp only [Atom.Ja, J, L, R, Set.mem_Icc] at hzb
  have hzb1 : LQ (a i).C ≤ z := by exact_mod_cast hzb.1
  have hzb2 : z ≤ RQ (a i).C := by exact_mod_cast hzb.2
  rcases lt_trichotomy i.val j with hij | hij | hij
  · have h1 := chainAtoms_R_le_L hS (i := i) (j := ⟨j, hj0⟩) (Fin.mk_lt_mk.2 hij)
    have h2 := LQ_lt_RQ (a ⟨j, hj0⟩).C
    linarith
  · have : i = ⟨j, hj0⟩ := Fin.ext hij
    rw [this] at hzb2; linarith
  · rcases eq_or_lt_of_le (show j + 1 ≤ i.val by omega) with hij' | hij'
    · have : i = ⟨j + 1, hj⟩ := Fin.ext hij'.symm
      rw [this] at hzb1; linarith
    · have h1 := chainAtoms_left_lt hS (i := ⟨j + 1, hj⟩) (j := i) (Fin.mk_lt_mk.2 hij')
      linarith

theorem chainNodes_succ {Λ : Finset Atom} (h0 : 1 ≤ (NormK α β Λ).card)
    (j : Fin (NormK α β Λ).card) :
    chainNodes α β Λ h0 j.succ = RQ (chainAtoms α β Λ j).C := by
  simp [chainNodes]

theorem chainNodes_zero {Λ : Finset Atom} (h0 : 1 ≤ (NormK α β Λ).card) :
    chainNodes α β Λ h0 0 = LQ (chainAtoms α β Λ ⟨0, h0⟩).C := by
  simp [chainNodes]

theorem chainNodes_castSucc (hK : α < β) {g : CK α β} {Λ : Finset Atom}
    (h : LocalRep α β g Λ) (j : Fin (NormK α β Λ).card) :
    chainNodes α β Λ (normK_nonempty_of_localRep hK h) j.castSucc =
      LQ (chainAtoms α β Λ j).C := by
  obtain ⟨jv, hjv⟩ := j
  cases jv with
  | zero => exact chainNodes_zero _
  | succ k =>
    have e : (Fin.castSucc ⟨k + 1, hjv⟩ : Fin ((NormK α β Λ).card + 1)) =
        (⟨k, by omega⟩ : Fin (NormK α β Λ).card).succ := Fin.ext rfl
    rw [e, chainNodes_succ, chainAtoms_adj hK h k hjv]

theorem chainNodes_lt (hK : α < β) {g : CK α β} {Λ : Finset Atom} (h : LocalRep α β g Λ)
    (j : Fin (NormK α β Λ).card) :
    chainNodes α β Λ (normK_nonempty_of_localRep hK h) j.castSucc <
      chainNodes α β Λ (normK_nonempty_of_localRep hK h) j.succ := by
  rw [chainNodes_castSucc hK h, chainNodes_succ]
  exact LQ_lt_RQ _

theorem chainNodes_left (hK : α < β) {g : CK α β} {Λ : Finset Atom} (h : LocalRep α β g Λ)
    (j : Fin (NormK α β Λ).card) :
    LQ (chainAtoms α β Λ j).C =
      chainNodes α β Λ (normK_nonempty_of_localRep hK h) j.castSucc :=
  (chainNodes_castSucc hK h j).symm

theorem chainNodes_right (hK : α < β) {g : CK α β} {Λ : Finset Atom} (h : LocalRep α β g Λ)
    (j : Fin (NormK α β Λ).card) :
    RQ (chainAtoms α β Λ j).C = chainNodes α β Λ (normK_nonempty_of_localRep hK h) j.succ :=
  (chainNodes_succ _ j).symm

theorem chainNodes_first (hK : α < β) {g : CK α β} {Λ : Finset Atom} (h : LocalRep α β g Λ) :
    ((chainNodes α β Λ (normK_nonempty_of_localRep hK h) 0 : ℚ) : ℝ) ≤ α := by
  obtain ⟨-, ⟨hCov, -⟩, -, ⟨⟨hS, -, -⟩, -⟩, -⟩ := normalization hK h
  rw [chainNodes_zero]
  obtain ⟨b, hb, hαb⟩ := hCov α ⟨le_rfl, hK.le⟩
  rw [← chainAtoms_image Λ, Finset.mem_image] at hb
  obtain ⟨i, -, rfl⟩ := hb
  have h1 : L (chainAtoms α β Λ i).C ≤ α := hαb.1
  rcases Nat.eq_zero_or_pos i.val with hi | hi
  · have : i = ⟨0, normK_nonempty_of_localRep hK h⟩ := Fin.ext hi
    rw [this] at h1; exact h1
  · have := chainAtoms_left_lt hS (i := ⟨0, normK_nonempty_of_localRep hK h⟩) (j := i)
      (Fin.mk_lt_mk.2 hi)
    have : L (chainAtoms α β Λ ⟨0, normK_nonempty_of_localRep hK h⟩).C <
        L (chainAtoms α β Λ i).C := by simp only [L]; exact_mod_cast this
    simp only [L] at *; linarith

theorem chainNodes_last (hK : α < β) {g : CK α β} {Λ : Finset Atom} (h : LocalRep α β g Λ) :
    β ≤ ((chainNodes α β Λ (normK_nonempty_of_localRep hK h)
      (Fin.last (NormK α β Λ).card) : ℚ) : ℝ) := by
  obtain ⟨-, ⟨hCov, -⟩, -, ⟨⟨hS, -, -⟩, -⟩, -⟩ := normalization hK h
  have h0 := normK_nonempty_of_localRep hK h
  have e : Fin.last (NormK α β Λ).card =
      (⟨(NormK α β Λ).card - 1, by omega⟩ : Fin (NormK α β Λ).card).succ :=
    Fin.ext (by simp; omega)
  rw [e, chainNodes_succ]
  obtain ⟨b, hb, hβb⟩ := hCov β ⟨hK.le, le_rfl⟩
  rw [← chainAtoms_image Λ, Finset.mem_image] at hb
  obtain ⟨i, -, rfl⟩ := hb
  have h1 : β ≤ R (chainAtoms α β Λ i).C := hβb.2
  rcases eq_or_lt_of_le (show i.val ≤ (NormK α β Λ).card - 1 by omega) with hi | hi
  · have : i = ⟨(NormK α β Λ).card - 1, by omega⟩ := Fin.ext hi
    rw [this] at h1; exact h1
  · have h2 := chainAtoms_R_le_L hS (i := i) (j := ⟨(NormK α β Λ).card - 1, by omega⟩)
      (Fin.mk_lt_mk.2 hi)
    have h3 := LQ_lt_RQ (chainAtoms α β Λ ⟨(NormK α β Λ).card - 1, by omega⟩).C
    have : R (chainAtoms α β Λ i).C ≤
        R (chainAtoms α β Λ ⟨(NormK α β Λ).card - 1, by omega⟩).C := by
      simp only [R]; exact_mod_cast (by linarith)
    simp only [R] at *; linarith

theorem chainNodes_inner (hK : α < β) {g : CK α β} {Λ : Finset Atom} (h : LocalRep α β g Λ)
    (j : Fin ((NormK α β Λ).card + 1)) (hj1 : 1 ≤ j.val) (hj2 : j.val < (NormK α β Λ).card) :
    α < ((chainNodes α β Λ (normK_nonempty_of_localRep hK h) j : ℚ) : ℝ) ∧
      ((chainNodes α β Λ (normK_nonempty_of_localRep hK h) j : ℚ) : ℝ) < β := by
  obtain ⟨-, -, hin, -, -⟩ := normalization hK h
  have e1 : j = (⟨j.val - 1, by omega⟩ : Fin (NormK α β Λ).card).succ :=
    Fin.ext (by simp; omega)
  have e2 : j = (⟨j.val, hj2⟩ : Fin (NormK α β Λ).card).castSucc := Fin.ext rfl
  have hR := chainNodes_succ (normK_nonempty_of_localRep hK h) ⟨j.val - 1, by omega⟩
  have hL := chainNodes_castSucc hK h ⟨j.val, hj2⟩
  rw [← e1] at hR
  rw [← e2] at hL
  have hne : chainAtoms α β Λ ⟨j.val - 1, by omega⟩ ≠ chainAtoms α β Λ ⟨j.val, hj2⟩ := by
    intro hc; have := chainAtoms_inj Λ hc; simp [Fin.ext_iff] at this; omega
  have hmem := hin _ (chainAtoms_mem Λ _) _ (chainAtoms_mem Λ _) hne
  have hx : ((chainNodes α β Λ (normK_nonempty_of_localRep hK h) j : ℚ) : ℝ) ∈
      (chainAtoms α β Λ ⟨j.val - 1, by omega⟩).Ja ∩ (chainAtoms α β Λ ⟨j.val, hj2⟩).Ja := by
    have g1 := LQ_lt_RQ (chainAtoms α β Λ ⟨j.val - 1, by omega⟩).C
    have g2 := LQ_lt_RQ (chainAtoms α β Λ ⟨j.val, hj2⟩).C
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only [L, R] <;> rw [Rat.cast_le]
    · rw [hR]; exact g1.le
    · rw [hR]
    · rw [hL]
    · rw [hL]; exact g2.le
  exact hmem hx

/-- Teorema `thm:chain`: de `LocalRep_K(g, Λ)` obtemos `NormChain_K(Λ)` pela
construção `F = Norm_K(Λ)`, `M = |F|`, `a_j = sort(F)_j`, `t_0 = L_ℚ(C(a_0))`,
`t_{j+1} = R_ℚ(C(a_j))`. Não há escolhas de enumeração adicionais. -/
def chainOf (hK : α < β) {g : CK α β} {Λ : Finset Atom} (h : LocalRep α β g Λ) :
    NormChain α β Λ where
  M := (NormK α β Λ).card
  hM := normK_nonempty_of_localRep hK h
  a := chainAtoms α β Λ
  t := chainNodes α β Λ (normK_nonempty_of_localRep hK h)
  a_inj := chainAtoms_inj Λ
  a_image := chainAtoms_image Λ
  t_lt := chainNodes_lt hK h
  a_left := chainNodes_left hK h
  a_right := chainNodes_right hK h
  t_first := chainNodes_first hK h
  t_last := chainNodes_last hK h
  t_inner := chainNodes_inner hK h

/-- Os nós internos da cadeia construída são diádicos. -/
theorem chainOf_nodes_dyadic (hK : α < β) {g : CK α β} {Λ : Finset Atom}
    (h : LocalRep α β g Λ) (j : Fin ((chainOf hK h).M + 1)) :
    (((chainOf hK h).t j : ℚ) : ℝ) ∈ Dy := by
  change ((chainNodes α β Λ (normK_nonempty_of_localRep hK h) j : ℚ) : ℝ) ∈ Dy
  cases j using Fin.cases with
  | zero => rw [chainNodes_zero]; exact (geometry _).2.2.2.2.2.2.2.2.1
  | succ i => rw [chainNodes_succ]; exact (geometry _).2.2.2.2.2.2.2.2.2.1

end Montagens

end
