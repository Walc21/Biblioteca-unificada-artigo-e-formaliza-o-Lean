module
public import RequestProject.Basic

/-!
# Seção 3: predicados de representação e normalização

Formalização da Seção 3 (`sec:normalization`).
-/

@[expose] public section

open scoped Classical

noncomputable section

namespace Montagens

open Atom

variable {α β : ℝ}

/-! ## Campos dos contratos (Definição `def:contracts`) -/

/-- `Sep(Λ)`: interiores de átomos distintos são disjuntos. -/
def Sep (Λ : Finset Atom) : Prop :=
  ∀ a ∈ Λ, ∀ b ∈ Λ, a ≠ b → a.Oa ∩ b.Oa = ∅

/-- `Cover(K, Λ)`: todo ponto de `K` está em algum suporte `J_a`. -/
def Cover (Kset : Set ℝ) (Λ : Finset Atom) : Prop :=
  ∀ x ∈ Kset, ∃ a ∈ Λ, x ∈ a.Ja

/-- `Match_K(g, Λ)` para `g : C_K`. -/
def MatchK (α β : ℝ) (g : CK α β) (Λ : Finset Atom) : Prop :=
  ∀ a ∈ Λ, ∀ z : Set.Icc α β, (z : ℝ) ∈ a.Ja → g z = a.line z

/-- `Match^G_K(G, Λ)` para `G : ℝ → ℝ`. -/
def MatchG (α β : ℝ) (G : ℝ → ℝ) (Λ : Finset Atom) : Prop :=
  ∀ a ∈ Λ, ∀ x ∈ a.Ja ∩ K α β, G x = a.line x

/-- `Agree(Λ)`: as retas coincidem em todos os encontros dos suportes. -/
def Agree (Λ : Finset Atom) : Prop :=
  ∀ a ∈ Λ, ∀ b ∈ Λ, ∀ x ∈ a.Ja ∩ b.Ja, a.line x = b.line x

/-- `LocalRep_K(g, Λ) := Sep(Λ) ∧ Cover(K, Λ) ∧ Match_K(g, Λ)`. -/
def LocalRep (α β : ℝ) (g : CK α β) (Λ : Finset Atom) : Prop :=
  Sep Λ ∧ Cover (K α β) Λ ∧ MatchK α β g Λ

/-- `StrongRep_K(g, Λ) := LocalRep_K(g, Λ) ∧ Agree(Λ)`. -/
def StrongRep (α β : ℝ) (g : CK α β) (Λ : Finset Atom) : Prop :=
  LocalRep α β g Λ ∧ Agree Λ

/-- `LocalRep^G_K(G, Λ)`. -/
def LocalRepG (α β : ℝ) (G : ℝ → ℝ) (Λ : Finset Atom) : Prop :=
  Sep Λ ∧ Cover (K α β) Λ ∧ MatchG α β G Λ

/-- `StrongRep^G_K(G, Λ)`. -/
def StrongRepG (α β : ℝ) (G : ℝ → ℝ) (Λ : Finset Atom) : Prop :=
  LocalRepG α β G Λ ∧ Agree Λ

/-- A classe local `𝒜^loc(K) ⊆ C_K`. -/
def Aloc (α β : ℝ) : Set (CK α β) := {g | ∃ Λ, LocalRep α β g Λ}

/-- A classe consolidada `𝒜^con(K) ⊆ C_K`. -/
def Astr (α β : ℝ) : Set (CK α β) := {g | ∃ Λ, StrongRep α β g Λ}

/-! ## Atividade e filtro (Definição `def:norm`) -/

/-- `Active_K(a) :⟺ O_a ∩ K° ≠ ∅`. -/
def Active (α β : ℝ) (a : Atom) : Prop := a.Oa ∩ Kint α β ≠ ∅

/-- `Norm_K(Λ) := filter(Active_K, Λ)`. -/
def NormK (α β : ℝ) (Λ : Finset Atom) : Finset Atom := Λ.filter (Active α β)

theorem mem_NormK {Λ : Finset Atom} {a : Atom} :
    a ∈ NormK α β Λ ↔ a ∈ Λ ∧ Active α β a := Finset.mem_filter

/-- Lema `lem:active` (critério exato de atividade). Usa `α < β`. -/
theorem active_iff (hK : α < β) (a : Atom) :
    Active α β a ↔ a.La < β ∧ α < a.Ra := by
  have hLR : a.La < a.Ra := (geometry a.C).2.2.2.2.1
  unfold Active
  rw [← Set.nonempty_iff_ne_empty]
  simp only [Atom.Oa, O, Kint, Atom.La, Atom.Ra] at *
  constructor
  · rintro ⟨x, ⟨h1, h2⟩, h3, h4⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    refine ⟨(max (L a.C) α + min (R a.C) β) / 2, ⟨?_, ?_⟩, ?_, ?_⟩ <;>
    · simp only [max_def, min_def]; split_ifs <;> linarith

/-- Lema `lem:separated` (intervalos separados), primeira parte. -/
theorem separated_of_disjoint {u v p q : ℝ} (huv : u < v) (hpq : p < q)
    (h : Set.Ioo u v ∩ Set.Ioo p q = ∅) : v ≤ p ∨ q ≤ u := by
  by_contra hc
  push_neg at hc
  have : (max u p + min v q) / 2 ∈ Set.Ioo u v ∩ Set.Ioo p q := by
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
    · simp only [max_def, min_def]; split_ifs <;> linarith
  rw [h] at this; exact this

/-- Lema `lem:separated`, segunda parte: uma interseção não vazia dos fechados
é uma única extremidade comum. -/
theorem separated_inter {u v p q : ℝ} (huv : u < v) (hpq : p < q)
    (h : Set.Ioo u v ∩ Set.Ioo p q = ∅) (hne : (Set.Icc u v ∩ Set.Icc p q).Nonempty) :
    (v = p ∧ Set.Icc u v ∩ Set.Icc p q = {v}) ∨
    (q = u ∧ Set.Icc u v ∩ Set.Icc p q = {u}) := by
  obtain ⟨z, ⟨h1, h2⟩, h3, h4⟩ := hne
  rcases separated_of_disjoint huv hpq h with h5 | h5
  · left
    have : v = p := by linarith
    subst this
    refine ⟨rfl, ?_⟩
    ext x; simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨_, _⟩, _, _⟩; linarith
    · rintro rfl; exact ⟨⟨huv.le, le_rfl⟩, le_rfl, hpq.le⟩
  · right
    have : q = u := by linarith
    subst this
    refine ⟨rfl, ?_⟩
    ext x; simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨_, _⟩, _, _⟩; linarith
    · rintro rfl; exact ⟨⟨le_rfl, huv.le⟩, hpq.le, le_rfl⟩

/-- A família filtrada cobre `K` (passo da demonstração de `thm:norm`). -/
theorem norm_cover (hK : α < β) {Λ : Finset Atom} (hC : Cover (K α β) Λ) :
    Cover (K α β) (NormK α β Λ) := by
  intro x hx
  have hU : IsClosed (⋃ a ∈ NormK α β Λ, a.Ja) :=
    isClosed_biUnion_finset (fun a _ => (geometry a.C).2.2.2.1)
  have hsub : Kint α β ⊆ ⋃ a ∈ NormK α β Λ, a.Ja := by
    intro y hy
    obtain ⟨a, ha, hya⟩ := hC y ⟨hy.1.le, hy.2.le⟩
    refine Set.mem_biUnion (mem_NormK.2 ⟨ha, (active_iff hK a).2 ?_⟩) hya
    simp only [Atom.Ja, J, Set.mem_Icc] at hya
    exact ⟨lt_of_le_of_lt hya.1 hy.2, lt_of_lt_of_le hy.1 hya.2⟩
  have hx' : x ∈ closure (Kint α β) := by rw [← (K_props hK).2.2]; exact hx
  have := (closure_minimal hsub hU) hx'
  simpa using this

/-- Interseções entre átomos distintos retidos estão em `K°`. -/
theorem norm_inter_inside {Λ : Finset Atom} (hS : Sep Λ) :
    ∀ a ∈ NormK α β Λ, ∀ b ∈ NormK α β Λ, a ≠ b → a.Ja ∩ b.Ja ⊆ Kint α β := by
  intro a ha b hb hab z hz
  rw [mem_NormK] at ha hb
  have hO := hS a ha.1 b hb.1 hab
  have hLRa : a.La < a.Ra := (geometry a.C).2.2.2.2.1
  have hLRb : b.La < b.Ra := (geometry b.C).2.2.2.2.1
  obtain ⟨u, ⟨hu1, hu2⟩, hu3, hu4⟩ := Set.nonempty_iff_ne_empty.2 ha.2
  obtain ⟨v, ⟨hv1, hv2⟩, hv3, hv4⟩ := Set.nonempty_iff_ne_empty.2 hb.2
  simp only [Atom.Oa, Atom.Ja, O, J, Atom.La, Atom.Ra] at *
  rcases separated_inter hLRa hLRb hO ⟨z, hz⟩ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h2] at hz; rw [Set.mem_singleton_iff] at hz; subst hz
    exact ⟨by linarith, by linarith⟩
  · rw [h2] at hz; rw [Set.mem_singleton_iff] at hz; subst hz
    exact ⟨by linarith, by linarith⟩

theorem agree_of_inside {Λ : Finset Atom}
    (hin : ∀ a ∈ Λ, ∀ b ∈ Λ, a ≠ b → a.Ja ∩ b.Ja ⊆ Kint α β)
    (hinner : ∀ a ∈ Λ, ∀ b ∈ Λ, ∀ x ∈ a.Ja ∩ b.Ja ∩ K α β, a.line x = b.line x) :
    Agree Λ := by
  intro a ha b hb x hx
  by_cases hab : a = b
  · subst hab; rfl
  · have := hin a ha b hb hab hx
    exact hinner a ha b hb x ⟨hx, this.1.le, this.2.le⟩

theorem norm_idem (Λ : Finset Atom) : NormK α β (NormK α β Λ) = NormK α β Λ := by
  unfold NormK; rw [Finset.filter_filter]; simp

theorem sep_subset {Λ Λ' : Finset Atom} (h : Λ' ⊆ Λ) (hS : Sep Λ) : Sep Λ' :=
  fun a ha b hb hab => hS a (h ha) b (h hb) hab

/-- Teorema `thm:norm` (normalização), versão para `g : C_K`. -/
theorem normalization (hK : α < β) {g : CK α β} {Λ : Finset Atom}
    (h : LocalRep α β g Λ) :
    (NormK α β Λ ⊆ Λ ∧ (NormK α β Λ).card ≤ Λ.card) ∧
    (Cover (K α β) (NormK α β Λ) ∧ (NormK α β Λ).Nonempty) ∧
    (∀ a ∈ NormK α β Λ, ∀ b ∈ NormK α β Λ, a ≠ b → a.Ja ∩ b.Ja ⊆ Kint α β) ∧
    StrongRep α β g (NormK α β Λ) ∧
    NormK α β (NormK α β Λ) = NormK α β Λ := by
  obtain ⟨hS, hC, hM⟩ := h
  have hsub : NormK α β Λ ⊆ Λ := Finset.filter_subset _ _
  have hC' := norm_cover hK hC
  have hin := norm_inter_inside (α := α) (β := β) hS
  have hne : (NormK α β Λ).Nonempty := by
    obtain ⟨a, ha, _⟩ := hC' α ⟨le_rfl, hK.le⟩; exact ⟨a, ha⟩
  have hM' : MatchK α β g (NormK α β Λ) := fun a ha => hM a (hsub ha)
  refine ⟨⟨hsub, Finset.card_le_card hsub⟩, ⟨hC', hne⟩, hin,
    ⟨⟨sep_subset hsub hS, hC', hM'⟩, ?_⟩, norm_idem Λ⟩
  apply agree_of_inside hin
  rintro a ha b hb x ⟨⟨hxa, hxb⟩, hxK⟩
  rw [← hM' a ha ⟨x, hxK⟩ hxa, hM' b hb ⟨x, hxK⟩ hxb]

/-- Teorema `thm:norm`, versão global para `G : ℝ → ℝ` (a função `G` inteira
é preservada: o enunciado é sobre a mesma `G`). -/
theorem normalizationG (hK : α < β) {G : ℝ → ℝ} {Λ : Finset Atom}
    (h : LocalRepG α β G Λ) :
    (NormK α β Λ ⊆ Λ ∧ (NormK α β Λ).card ≤ Λ.card) ∧
    (Cover (K α β) (NormK α β Λ) ∧ (NormK α β Λ).Nonempty) ∧
    (∀ a ∈ NormK α β Λ, ∀ b ∈ NormK α β Λ, a ≠ b → a.Ja ∩ b.Ja ⊆ Kint α β) ∧
    StrongRepG α β G (NormK α β Λ) ∧
    NormK α β (NormK α β Λ) = NormK α β Λ := by
  obtain ⟨hS, hC, hM⟩ := h
  have hsub : NormK α β Λ ⊆ Λ := Finset.filter_subset _ _
  have hC' := norm_cover hK hC
  have hin := norm_inter_inside (α := α) (β := β) hS
  have hne : (NormK α β Λ).Nonempty := by
    obtain ⟨a, ha, _⟩ := hC' α ⟨le_rfl, hK.le⟩; exact ⟨a, ha⟩
  have hM' : MatchG α β G (NormK α β Λ) := fun a ha => hM a (hsub ha)
  refine ⟨⟨hsub, Finset.card_le_card hsub⟩, ⟨hC', hne⟩, hin,
    ⟨⟨sep_subset hsub hS, hC', hM'⟩, ?_⟩, norm_idem Λ⟩
  apply agree_of_inside hin
  rintro a ha b hb x ⟨⟨hxa, hxb⟩, hxK⟩
  rw [← hM' a ha x ⟨hxa, hxK⟩, hM' b hb x ⟨hxb, hxK⟩]

/-- Corolário `cor:classes`: `𝒜^loc(K) = 𝒜^con(K)`. -/
theorem Aloc_eq_Astr (hK : α < β) : Aloc α β = Astr α β := by
  ext g
  constructor
  · rintro ⟨Λ, h⟩; exact ⟨_, (normalization hK h).2.2.2.1⟩
  · rintro ⟨Λ, h⟩; exact ⟨Λ, h.1⟩

end Montagens

end
