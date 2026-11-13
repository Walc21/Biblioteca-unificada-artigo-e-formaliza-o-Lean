module
public import RequestProject.Normalization
public import RequestProject.Enumeration

/-!
# Seção 5: representações por células e mapas entre os tipos de função

Formalização da Seção 5 (`sec:bridge`).
-/

@[expose] public section

open scoped Classical

noncomputable section

namespace Montagens

open Atom

variable {α β : ℝ}

/-! ## Testemunhas por células endereçadas (Definição `def:cellrep`) -/

/-- `CellRep_{i,K}(g, F, e)` para `g : C_K`. -/
def CellRep (i : Phase) (α β : ℝ) (g : CK α β) (F : Finset Cell) (e : Cell → ℕ) : Prop :=
  (∀ c ∈ F, ∀ d ∈ F, c ≠ d → O c ∩ O d = ∅) ∧
  (∀ x ∈ K α β, ∃ c ∈ F, x ∈ J c) ∧
  (∀ c ∈ F, Ci i (e c) = c) ∧
  (∀ c ∈ F, ∀ z : Set.Icc α β, (z : ℝ) ∈ J c → g z = lam i (e c) z)

/-- `CellRep^G_{i,K}(G, F, e)` para `G : ℝ → ℝ`. -/
def CellRepG (i : Phase) (α β : ℝ) (G : ℝ → ℝ) (F : Finset Cell) (e : Cell → ℕ) : Prop :=
  (∀ c ∈ F, ∀ d ∈ F, c ≠ d → O c ∩ O d = ∅) ∧
  (∀ x ∈ K α β, ∃ c ∈ F, x ∈ J c) ∧
  (∀ c ∈ F, Ci i (e c) = c) ∧
  (∀ c ∈ F, ∀ x ∈ J c ∩ K α β, G x = lam i (e c) x)

/-! ## Continuidade no domínio e restrição (Definição `def:restriction`) -/

/-- `ContOn_K(G)`: continuidade ε-δ de `G` relativa a `K`. -/
def ContOn (α β : ℝ) (G : ℝ → ℝ) : Prop :=
  ∀ x ∈ K α β, ∀ ε > 0, ∃ δ > 0, ∀ y ∈ K α β, |y - x| < δ → |G y - G x| < ε

theorem continuous_restrict_of_contOn {G : ℝ → ℝ} (h : ContOn α β G) :
    Continuous (fun z : Set.Icc α β => G z) := by
  rw [Metric.continuous_iff]
  intro b ε hε
  obtain ⟨δ, hδ, hb⟩ := h b b.2 ε hε
  refine ⟨δ, hδ, fun a ha => ?_⟩
  have := hb a a.2 (by simpa [Subtype.dist_eq, Real.dist_eq] using ha)
  simpa [Real.dist_eq] using this

/-- `Res_K(G, h) : C_K`, a função `z ↦ G(ι_K(z))`. -/
def Res (G : ℝ → ℝ) (h : ContOn α β G) : CK α β :=
  ⟨fun z => G z, continuous_restrict_of_contOn h⟩

/-- `ResImage_K(𝒮) = {g : C_K | ∃ G ∈ 𝒮, ∀ z, g(z) = G(ι_K(z))}`. -/
def ResImage (α β : ℝ) (S : Set (ℝ → ℝ)) : Set (CK α β) :=
  {g | ∃ G ∈ S, ∀ z : Set.Icc α β, g z = G z}

/-! ## As três classes tipadas (Definição `def:threeclasses`) -/

/-- `𝓑₂(K) ⊆ C_K`. -/
def B2 (α β : ℝ) : Set (CK α β) :=
  {g | ∃ (F : Finset Cell) (e : Cell → ℕ), CellRep .two α β g F e}

/-- `𝓑₃(K) ⊆ (ℝ → ℝ)`. -/
def B3 (α β : ℝ) : Set (ℝ → ℝ) :=
  {G | ContOn α β G ∧ ∃ (F : Finset Cell) (e : Cell → ℕ), CellRepG .three α β G F e}

/-- `𝓑_con(K) ⊆ (ℝ → ℝ)`. -/
def Bcon (α β : ℝ) : Set (ℝ → ℝ) :=
  {G | ContOn α β G ∧ ∃ Λ : Finset Atom, StrongRepG α β G Λ}

/-! ## Conversões explícitas das testemunhas (Lema `lem:witnesses`) -/

/-- Células para átomos: `T_i(F, e) = image(c ↦ dec_i(e(c)), F)`. -/
def cellsToAtoms (i : Phase) (F : Finset Cell) (e : Cell → ℕ) : Finset Atom :=
  F.image (fun c => dec i (e c))

/-- Átomos para células: `I(Λ) = image(C, Λ)`. -/
def atomsToCells (Λ : Finset Atom) : Finset Cell := Λ.image Atom.C

/-- `σ_Λ(c)`: o (único) átomo de `Λ` com célula `c`, ou `a†` se `c ∉ I(Λ)`. -/
def sigmaAtom (Λ : Finset Atom) (c : Cell) : Atom :=
  if h : c ∈ atomsToCells Λ then
    Classical.choose (Finset.mem_image.1 h)
  else atomDefault

/-- O endereçamento total `e_{i,Λ}(c) = enc_i(σ_Λ(c))`. -/
def addrOf (i : Phase) (Λ : Finset Atom) (c : Cell) : ℕ := enc i (sigmaAtom Λ c)

theorem dec_C_eq (i : Phase) (n : ℕ) : (dec i n).C = Ci i n := rfl

theorem cellsToAtoms_common (i : Phase) {F : Finset Cell} {e : Cell → ℕ}
    (hS : ∀ c ∈ F, ∀ d ∈ F, c ≠ d → O c ∩ O d = ∅)
    (hCov : ∀ x ∈ K α β, ∃ c ∈ F, x ∈ J c)
    (hci : ∀ c ∈ F, Ci i (e c) = c) :
    Sep (cellsToAtoms i F e) ∧ Cover (K α β) (cellsToAtoms i F e) ∧
    (cellsToAtoms i F e).card = F.card ∧
    atomsToCells (cellsToAtoms i F e) = F ∧
    (∀ c ∈ F, addrOf i (cellsToAtoms i F e) c = e c) := by
  have hinj : Set.InjOn (fun c => dec i (e c)) F := by
    intro c hc d hd hcd
    have := congrArg Atom.C hcd
    simp only [dec_C_eq, hci c hc, hci d hd] at this
    exact this
  have himg : atomsToCells (cellsToAtoms i F e) = F := by
    unfold atomsToCells cellsToAtoms
    rw [Finset.image_image]
    rw [Finset.image_congr (g := id) (fun c hc => by simp [dec_C_eq, hci c hc])]
    simp
  refine ⟨?_, ?_, Finset.card_image_of_injOn hinj, himg, ?_⟩
  · intro a ha b hb hab
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hb
    have hcd : c ≠ d := fun h => hab (by rw [h])
    simpa [Atom.Oa, dec_C_eq, hci c hc, hci d hd] using hS c hc d hd hcd
  · intro x hx
    obtain ⟨c, hc, hxc⟩ := hCov x hx
    exact ⟨_, Finset.mem_image_of_mem _ hc, by simpa [Atom.Ja, dec_C_eq, hci c hc] using hxc⟩
  · intro c hc
    have hcI : c ∈ atomsToCells (cellsToAtoms i F e) := by rw [himg]; exact hc
    unfold addrOf sigmaAtom
    rw [dif_pos hcI]
    obtain ⟨ha, hCa⟩ := Classical.choose_spec (Finset.mem_image.1 hcI)
    obtain ⟨d, hd, hdeq⟩ := Finset.mem_image.1 ha
    have : d = c := by rw [← hCa, ← hdeq, dec_C_eq, hci d hd]
    subst this
    rw [← hdeq, (codec i).2.1]

theorem C_injOn_of_sep {Λ : Finset Atom} (hS : Sep Λ) : Set.InjOn Atom.C Λ := by
  intro a ha b hb hab
  by_contra hne
  have h := hS a ha b hb hne
  have hO : a.Oa = b.Oa := by simp [Atom.Oa, hab]
  rw [hO, Set.inter_self] at h
  exact (Set.nonempty_iff_ne_empty.1 (geometry b.C).2.2.2.2.2.1) h

theorem sigmaAtom_C {Λ : Finset Atom} (hS : Sep Λ) {a : Atom} (ha : a ∈ Λ) :
    sigmaAtom Λ a.C = a := by
  have hcI : a.C ∈ atomsToCells Λ := Finset.mem_image_of_mem _ ha
  unfold sigmaAtom
  rw [dif_pos hcI]
  obtain ⟨ha', hCa⟩ := Classical.choose_spec (Finset.mem_image.1 hcI)
  exact C_injOn_of_sep hS ha' ha hCa

theorem atomsToCells_common (i : Phase) {Λ : Finset Atom} (hS : Sep Λ)
    (hC : Cover (K α β) Λ) :
    (∀ c ∈ atomsToCells Λ, ∀ d ∈ atomsToCells Λ, c ≠ d → O c ∩ O d = ∅) ∧
    (∀ x ∈ K α β, ∃ c ∈ atomsToCells Λ, x ∈ J c) ∧
    (∀ c ∈ atomsToCells Λ, Ci i (addrOf i Λ c) = c) ∧
    (∀ a ∈ Λ, dec i (addrOf i Λ a.C) = a) ∧
    (atomsToCells Λ).card = Λ.card ∧
    cellsToAtoms i (atomsToCells Λ) (addrOf i Λ) = Λ := by
  have hdec : ∀ a ∈ Λ, dec i (addrOf i Λ a.C) = a := by
    intro a ha; unfold addrOf; rw [sigmaAtom_C hS ha, (codec i).1]
  refine ⟨?_, ?_, ?_, hdec, Finset.card_image_of_injOn (C_injOn_of_sep hS), ?_⟩
  · intro c hc d hd hcd
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hd
    exact hS a ha b hb (fun h => hcd (by rw [h]))
  · intro x hx
    obtain ⟨a, ha, hxa⟩ := hC x hx
    exact ⟨a.C, Finset.mem_image_of_mem _ ha, hxa⟩
  · intro c hc
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hc
    rw [← dec_C_eq, hdec a ha]
  · unfold cellsToAtoms atomsToCells
    rw [Finset.image_image]
    rw [Finset.image_congr (g := id) (fun a ha => by simp [hdec a ha])]
    simp

/-- Lema `lem:witnesses`, células para átomos (versão `C_K`). -/
theorem cellsToAtoms_spec (i : Phase) {g : CK α β} {F : Finset Cell} {e : Cell → ℕ}
    (h : CellRep i α β g F e) :
    LocalRep α β g (cellsToAtoms i F e) ∧ (cellsToAtoms i F e).card = F.card ∧
    atomsToCells (cellsToAtoms i F e) = F ∧
    (∀ c ∈ F, addrOf i (cellsToAtoms i F e) c = e c) := by
  obtain ⟨hS, hCov, hci, hM⟩ := h
  obtain ⟨h1, h2, h3, h4, h5⟩ := cellsToAtoms_common (α := α) (β := β) i hS hCov hci
  refine ⟨⟨h1, h2, ?_⟩, h3, h4, h5⟩
  intro a ha z hz
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 ha
  rw [hM c hc z (by simpa [Atom.Ja, dec_C_eq, hci c hc] using hz), (codec i).2.2]

/-- Lema `lem:witnesses`, células para átomos (versão global). -/
theorem cellsToAtoms_specG (i : Phase) {G : ℝ → ℝ} {F : Finset Cell} {e : Cell → ℕ}
    (h : CellRepG i α β G F e) :
    LocalRepG α β G (cellsToAtoms i F e) ∧ (cellsToAtoms i F e).card = F.card ∧
    atomsToCells (cellsToAtoms i F e) = F ∧
    (∀ c ∈ F, addrOf i (cellsToAtoms i F e) c = e c) := by
  obtain ⟨hS, hCov, hci, hM⟩ := h
  obtain ⟨h1, h2, h3, h4, h5⟩ := cellsToAtoms_common (α := α) (β := β) i hS hCov hci
  refine ⟨⟨h1, h2, ?_⟩, h3, h4, h5⟩
  rintro a ha x ⟨hx, hxK⟩
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 ha
  rw [hM c hc x ⟨by simpa [Atom.Ja, dec_C_eq, hci c hc] using hx, hxK⟩, (codec i).2.2]

/-- Lema `lem:witnesses`, átomos para células (versão `C_K`). -/
theorem atomsToCells_spec (i : Phase) {g : CK α β} {Λ : Finset Atom}
    (h : LocalRep α β g Λ) :
    CellRep i α β g (atomsToCells Λ) (addrOf i Λ) ∧
    (atomsToCells Λ).card = Λ.card ∧
    cellsToAtoms i (atomsToCells Λ) (addrOf i Λ) = Λ := by
  obtain ⟨hS, hC, hM⟩ := h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := atomsToCells_common (α := α) (β := β) i hS hC
  refine ⟨⟨h1, h2, h3, ?_⟩, h5, h6⟩
  intro c hc z hz
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hc
  rw [(codec i).2.2, h4 a ha]
  exact hM a ha z hz

/-- Lema `lem:witnesses`, átomos para células (versão global). -/
theorem atomsToCells_specG (i : Phase) {G : ℝ → ℝ} {Λ : Finset Atom}
    (h : LocalRepG α β G Λ) :
    CellRepG i α β G (atomsToCells Λ) (addrOf i Λ) ∧
    (atomsToCells Λ).card = Λ.card ∧
    cellsToAtoms i (atomsToCells Λ) (addrOf i Λ) = Λ := by
  obtain ⟨hS, hC, hM⟩ := h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := atomsToCells_common (α := α) (β := β) i hS hC
  refine ⟨⟨h1, h2, h3, ?_⟩, h5, h6⟩
  intro c hc x hx
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hc
  rw [(codec i).2.2, h4 a ha]
  exact hM a ha x hx

/-! ## Extensão contínua por projeção (Definição `def:clamp`) -/

/-- `p_K(x) = ⟨min {β, max {α, x}}, h_x⟩`. -/
def projK (hK : α ≤ β) (x : ℝ) : Set.Icc α β :=
  ⟨min β (max α x), le_min hK (le_max_left _ _), min_le_left _ _⟩

theorem continuous_projK (hK : α ≤ β) : Continuous (projK hK) := by
  unfold projK; fun_prop

/-- `E₀(g)(x) = g(p_K(x))`. -/
def E0 (hK : α ≤ β) (g : CK α β) : C(ℝ, ℝ) :=
  ⟨fun x => g (projK hK x), g.continuous.comp (continuous_projK hK)⟩

theorem projK_of_mem (hK : α ≤ β) {x : ℝ} (hx : x ∈ K α β) : ((projK hK x : ℝ)) = x := by
  simp only [projK]
  rw [max_eq_right hx.1, min_eq_right hx.2]

theorem contOn_of_continuous {G : ℝ → ℝ} (hG : Continuous G) : ContOn α β G := by
  intro x _ ε hε
  obtain ⟨δ, hδ, h⟩ := Metric.continuous_iff.1 hG x ε hε
  exact ⟨δ, hδ, fun y _ hy => by
    simpa [Real.dist_eq] using h y (by simpa [Real.dist_eq] using hy)⟩

theorem contOn_E0 (hK : α ≤ β) (g : CK α β) : ContOn α β (E0 hK g) :=
  contOn_of_continuous (E0 hK g).continuous

theorem E0_apply_mem (hK : α ≤ β) (g : CK α β) (z : Set.Icc α β) : E0 hK g z = g z := by
  change g (projK hK z) = g z
  congr 1
  exact Subtype.ext (projK_of_mem hK z.2)

theorem Res_E0 (hK : α ≤ β) (g : CK α β) (h : ContOn α β (E0 hK g)) :
    Res (E0 hK g) h = g := by
  ext z
  exact E0_apply_mem hK g z

/-! ## Equivalência extensional tipada (Teorema `thm:bridge`) -/

theorem localRep_iff_localRepG {g : CK α β} {G : ℝ → ℝ} (hgG : ∀ z : Set.Icc α β, g z = G z)
    (Λ : Finset Atom) : LocalRep α β g Λ ↔ LocalRepG α β G Λ := by
  unfold LocalRep LocalRepG MatchK MatchG
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun a ha x hx => ?_⟩
    rw [← hgG ⟨x, hx.2⟩]; exact h3 a ha ⟨x, hx.2⟩ hx.1
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun a ha z hz => ?_⟩
    rw [hgG z]; exact h3 a ha z ⟨hz, z.2⟩

theorem strongRep_iff_strongRepG {g : CK α β} {G : ℝ → ℝ}
    (hgG : ∀ z : Set.Icc α β, g z = G z) (Λ : Finset Atom) :
    StrongRep α β g Λ ↔ StrongRepG α β G Λ := by
  unfold StrongRep StrongRepG
  rw [localRep_iff_localRepG hgG]

theorem B2_eq_Aloc : B2 α β = Aloc α β := by
  ext g
  constructor
  · rintro ⟨F, e, h⟩; exact ⟨_, (cellsToAtoms_spec _ h).1⟩
  · rintro ⟨Λ, h⟩; exact ⟨_, _, (atomsToCells_spec .two h).1⟩

theorem ResImage_B3_eq_Aloc (hK : α < β) : ResImage α β (B3 α β) = Aloc α β := by
  ext g
  constructor
  · rintro ⟨G, ⟨-, F, e, hG⟩, hgG⟩
    exact ⟨_, (localRep_iff_localRepG hgG _).2 (cellsToAtoms_specG _ hG).1⟩
  · rintro ⟨Λ, h⟩
    have hgG : ∀ z : Set.Icc α β, g z = E0 hK.le g z := fun z => (E0_apply_mem hK.le g z).symm
    refine ⟨E0 hK.le g, ⟨contOn_E0 hK.le g, _, _,
      (atomsToCells_specG .three ((localRep_iff_localRepG hgG Λ).1 h)).1⟩, hgG⟩

theorem ResImage_Bcon_eq_Astr (hK : α < β) : ResImage α β (Bcon α β) = Astr α β := by
  ext g
  constructor
  · rintro ⟨G, ⟨-, Λ, hG⟩, hgG⟩
    exact ⟨Λ, (strongRep_iff_strongRepG hgG _).2 hG⟩
  · rintro ⟨Λ, h⟩
    have hgG : ∀ z : Set.Icc α β, g z = E0 hK.le g z := fun z => (E0_apply_mem hK.le g z).symm
    exact ⟨E0 hK.le g, ⟨contOn_E0 hK.le g, Λ, (strongRep_iff_strongRepG hgG Λ).1 h⟩, hgG⟩

theorem B3_eq_Bcon (hK : α < β) : B3 α β = Bcon α β := by
  ext G
  constructor
  · rintro ⟨hc, F, e, hG⟩
    exact ⟨hc, _, (normalizationG hK (cellsToAtoms_specG _ hG).1).2.2.2.1⟩
  · rintro ⟨hc, Λ, hG⟩
    exact ⟨hc, _, _, (atomsToCells_specG .three hG.1).1⟩

/-- Teorema `thm:bridge` (equivalência extensional tipada). -/
theorem bridge (hK : α < β) :
    (B2 α β = Aloc α β ∧ Aloc α β = Astr α β) ∧
    ResImage α β (B3 α β) = Aloc α β ∧
    ResImage α β (Bcon α β) = Astr α β ∧
    B3 α β = Bcon α β :=
  ⟨⟨B2_eq_Aloc, Aloc_eq_Astr hK⟩, ResImage_B3_eq_Aloc hK, ResImage_Bcon_eq_Astr hK,
    B3_eq_Bcon hK⟩

end Montagens

end
