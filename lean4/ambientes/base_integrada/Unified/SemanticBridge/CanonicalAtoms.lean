module
public import Unified.SemanticBridge.AssemblyEquivalence
@[expose] public section

/-!
# Dicionário canônico de átomos entre as Fases 2 e 3

Os endereços naturais NÃO são identificados. A equivalência é de
parâmetros geométricos e induz endereços canônicos via encode/decode.
-/

namespace SemanticBridge

/-- Todo átomo canônico possui um endereço na enumeração da Fase 2. -/
theorem ofFase2_surjective : Function.Surjective ofFase2 := by
  intro a
  obtain ⟨n, hk, hm, hy, hs⟩ := canonical_params_in_fase2 a
  refine ⟨n, ?_⟩
  apply Dyadic.Lib.Atom.ext
  · exact hk
  · exact hm
  · exact hy
  · exact hs

/-- Todo átomo canônico possui um endereço na enumeração da Fase 3. -/
theorem ofFase3_surjective : Function.Surjective ofFase3 := by
  intro a
  obtain ⟨n, hk, hm, hy, hs⟩ :=
    Fase3.exists_jet a.k a.m a.y0 a.s a.hs
  refine ⟨n, ?_⟩
  apply Dyadic.Lib.Atom.ext
  · exact hk
  · exact hm
  · exact hy
  · exact hs

/-- Qualquer endereço da Fase 2 possui equivalente na Fase 3. -/
theorem fase2_to_fase3_atoms (n : ℕ) :
    ∃ m : ℕ, ofFase3 m = ofFase2 n :=
  ofFase3_surjective (ofFase2 n)

/-- Qualquer endereço da Fase 3 possui equivalente na Fase 2. -/
theorem fase3_to_fase2_atoms (n : ℕ) :
    ∃ m : ℕ, ofFase2 m = ofFase3 n :=
  ofFase2_surjective (ofFase3 n)

/-- As duas enumerações têm a mesma imagem no espaço dos átomos. -/
theorem range_ofFase2_eq_range_ofFase3 :
    Set.range ofFase2 = Set.range ofFase3 := by
  apply Set.Subset.antisymm
  · rintro a ⟨n, rfl⟩
    exact ofFase3_surjective _
  · rintro a ⟨n, rfl⟩
    exact ofFase2_surjective _

/-- A reindexação por endereços canônicos recupera os mesmos parâmetros. -/
theorem canonical_address_transfer_2_to_3 (n : ℕ) :
    ∃ m : ℕ, Dyadic.Lib.decode (readdress3 m) =
      Dyadic.Lib.decode (readdress2 n) := by
  obtain ⟨m, hm⟩ := fase2_to_fase3_atoms n
  exact ⟨m, by simpa only [readdress2_spec, readdress3_spec] using hm⟩

end SemanticBridge
