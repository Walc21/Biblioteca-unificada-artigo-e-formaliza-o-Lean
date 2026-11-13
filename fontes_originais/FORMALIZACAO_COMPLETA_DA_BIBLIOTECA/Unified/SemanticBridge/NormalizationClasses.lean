module
public import Unified.SemanticBridge.NormalizationEnumerations
@[expose] public section

/-!
# Classes de montagens nos tipos originais das Fases 2 e 3

Esta ponte usa os endereços concretos já identificados e distingue as funções
contínuas no subtipo fechado das funções globais. Nenhuma extensão altera os
valores prescritos dentro do domínio.
-/

noncomputable section

namespace SemanticBridge

theorem normalization_cell3 (c : Montagens.Cell) : Montagens.J c = Fase3.cC c := by
  simp [Montagens.J, Montagens.L, Montagens.R, Montagens.LQ, Montagens.RQ,
    Fase3.cC, Fase3.cell, Fase3.cellL, Fase3.cellR]

theorem normalization_cell2 (c : Montagens.Cell) :
    Montagens.J c = Dyadic2.cellJ c.1 c.2 := by
  rw [normalization_cell3]
  rfl

theorem normalization_interior3 (c : Montagens.Cell) :
    Montagens.O c = Set.Ioo (Fase3.cL c) (Fase3.cR c) := by
  rw [Montagens.O_eq_interior_J, normalization_cell3]
  simp [Fase3.cC, Fase3.cell]

theorem normalization_interior2 (c : Montagens.Cell) :
    Montagens.O c = interior (Dyadic2.cellJ c.1 c.2) := by
  rw [Montagens.O_eq_interior_J, normalization_cell2]

theorem normalization_C3 (n : ℕ) :
    Montagens.Ci .three n = (Fase3.gK n, Fase3.gM n) := by
  rw [Montagens.Ci, ← normalization_ofFase3]
  rfl

theorem normalization_C2 (n : ℕ) :
    Montagens.Ci .two n = (Dyadic2.scale n, Dyadic2.cellIdx n) := by
  rw [Montagens.Ci, ← normalization_ofFase2]
  rfl

theorem normalization_C3_eq_iff (n : ℕ) (c : Montagens.Cell) :
    Montagens.Ci .three n = c ↔ Fase3.gK n = c.1 ∧ Fase3.gM n = c.2 := by
  rw [normalization_C3, Prod.ext_iff]

theorem normalization_C2_eq_iff (n : ℕ) (c : Montagens.Cell) :
    Montagens.Ci .two n = c ↔ Dyadic2.scale n = c.1 ∧ Dyadic2.cellIdx n = c.2 := by
  rw [normalization_C2, Prod.ext_iff]

theorem normalization_lam3 (n : ℕ) (x : ℝ) :
    Montagens.lam .three n x = Fase3.atomLine n x := by
  rw [(Montagens.codec .three).2.2, ← normalization_ofFase3, normalization_atom_line,
    Fase3.atomLine_eq]
  simp [Dyadic.Lib.Atom.line, Dyadic.Lib.Atom.center, ofFase3, Fase3.x0, Fase3.center]

theorem normalization_lam2 (n : ℕ) (x : ℝ) :
    Montagens.lam .two n x = Dyadic2.line n x := by
  rw [(Montagens.codec .two).2.2, ← normalization_ofFase2, normalization_atom_line]
  simp [Dyadic.Lib.Atom.line, Dyadic.Lib.Atom.center, ofFase2, Dyadic2.line,
    Dyadic2.an, Dyadic2.bn, Dyadic2.x0n, Dyadic2.center_eq]
  ring

theorem normalization_contOn_iff (α β : ℝ) (g : ℝ → ℝ) :
    Montagens.ContOn α β g ↔ ContinuousOn g (Set.Icc α β) := by
  rw [Metric.continuousOn_iff]
  simp only [Montagens.ContOn, Montagens.K, Real.dist_eq]

theorem normalization_cellRep3_iff (α β : ℝ) (g : ℝ → ℝ)
    (F : Finset Montagens.Cell) (addr : Montagens.Cell → ℕ) :
    Montagens.CellRepG .three α β g F addr ↔
      Fase3.DisjointInteriors F ∧ Set.Icc α β ⊆ ⋃ c ∈ F, Fase3.cC c ∧
      ∀ c ∈ F, Fase3.gK (addr c) = c.1 ∧ Fase3.gM (addr c) = c.2 ∧
        ∀ x ∈ Fase3.cC c ∩ Set.Icc α β, g x = Fase3.atomLine (addr c) x := by
  simp only [Montagens.CellRepG, normalization_interior3, normalization_cell3,
    normalization_C3_eq_iff, normalization_lam3, Montagens.K,
    Fase3.DisjointInteriors, Set.disjoint_iff_inter_eq_empty, Set.subset_def,
    Set.mem_iUnion, exists_prop, forall_and]
  tauto

theorem normalization_B3_iff (α β : ℝ) (g : ℝ → ℝ) :
    g ∈ Montagens.B3 α β ↔ Fase3.IsAssembly α β g := by
  constructor
  · rintro ⟨hc, F, addr, h⟩
    obtain ⟨hs, hcov, hm⟩ := (normalization_cellRep3_iff α β g F addr).mp h
    exact ⟨(normalization_contOn_iff α β g).mp hc, F, hs, hcov, addr, hm⟩
  · rintro ⟨hc, F, hs, hcov, addr, hm⟩
    exact ⟨(normalization_contOn_iff α β g).mpr hc, F, addr,
      (normalization_cellRep3_iff α β g F addr).mpr ⟨hs, hcov, hm⟩⟩

theorem normalization_Bcon_iff (α β : ℝ) (g : ℝ → ℝ) :
    g ∈ Montagens.Bcon α β ↔ g ∈ Dyadic.Lib.Asm (Set.Icc α β) := by
  constructor
  · rintro ⟨hc, Λ, hΛ⟩
    refine ⟨(normalization_contOn_iff α β g).mp hc, canonicalAtoms Λ, ?_⟩
    apply (normalization_strong_iff α β g _).mp
    simpa only [normalization_canonical_atoms] using hΛ
  · rintro ⟨hc, Λ, hΛ⟩
    exact ⟨(normalization_contOn_iff α β g).mpr hc, normalizationAtoms Λ,
      (normalization_strong_iff α β g Λ).mpr hΛ⟩

/-- Fechamento da equivalência global nas definições originais da biblioteca. -/
theorem fase3_assembly_iff_consolidated {α β : ℝ} (hK : α < β) (g : ℝ → ℝ) :
    Fase3.IsAssembly α β g ↔ g ∈ Dyadic.Lib.Asm (Set.Icc α β) := by
  rw [← normalization_B3_iff, Montagens.B3_eq_Bcon hK, normalization_Bcon_iff]

theorem normalization_B2_iff (α β : ℝ) (g : Montagens.CK α β) :
    g ∈ Montagens.B2 α β ↔ g ∈ Dyadic2.Asm α β := by
  constructor
  · rintro ⟨F, addr, hs, hcov, hci, hm⟩
    refine ⟨F, addr, ?_, ?_, ?_⟩
    · intro c hc d hd hcd
      apply Set.disjoint_iff_inter_eq_empty.mpr
      simpa only [normalization_interior2] using hs c hc d hd hcd
    · intro x hx
      obtain ⟨c, hc, hxc⟩ := hcov x hx
      exact Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨hc,
        by simpa only [normalization_cell2] using hxc⟩⟩
    · intro c hc
      obtain ⟨hk, hidx⟩ := (normalization_C2_eq_iff (addr c) c).mp (hci c hc)
      refine ⟨hk, hidx, fun z hz => ?_⟩
      rw [← normalization_lam2]
      exact hm c hc z (by simpa only [normalization_cell2] using hz)
  · rintro ⟨F, addr, hs, hcov, hm⟩
    refine ⟨F, addr, ?_, ?_, ?_, ?_⟩
    · intro c hc d hd hcd
      simpa only [normalization_interior2] using
        Set.disjoint_iff_inter_eq_empty.mp (hs c hc d hd hcd)
    · intro x hx
      obtain ⟨c, hxc⟩ := Set.mem_iUnion.mp (hcov hx)
      obtain ⟨hc, hxc⟩ := Set.mem_iUnion.mp hxc
      exact ⟨c, hc, by simpa only [normalization_cell2] using hxc⟩
    · intro c hc
      exact (normalization_C2_eq_iff (addr c) c).mpr ⟨(hm c hc).1, (hm c hc).2.1⟩
    · intro c hc z hz
      rw [normalization_lam2]
      exact (hm c hc).2.2 z (by simpa only [normalization_cell2] using hz)

/-- Imagem por restrição da classe global consolidada no tipo contínuo da Fase 2. -/
theorem fase2_restriction_eq_consolidated {α β : ℝ} (hK : α < β) :
    Montagens.ResImage α β (Dyadic.Lib.Asm (Set.Icc α β)) = Dyadic2.Asm α β := by
  have hcon : Dyadic.Lib.Asm (Set.Icc α β) = Montagens.Bcon α β := by
    ext g
    exact (normalization_Bcon_iff α β g).symm
  have htwo : Dyadic2.Asm α β = Montagens.B2 α β := by
    ext g
    exact (normalization_B2_iff α β g).symm
  rw [hcon, Montagens.ResImage_Bcon_eq_Astr hK, htwo,
    Montagens.B2_eq_Aloc, Montagens.Aloc_eq_Astr hK]

end SemanticBridge
