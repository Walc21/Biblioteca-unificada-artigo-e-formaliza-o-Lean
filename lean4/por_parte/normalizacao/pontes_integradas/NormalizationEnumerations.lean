module
public import Unified.SemanticBridge.NormalizationContracts
@[expose] public section

/-!
# Enumerações concretas das Fases 2 e 3

As identidades são verificadas pelas fórmulas dos postos e pelas inversas
dos pareamentos. Não se infere igualdade de endereços apenas da
sobrejetividade das bibliotecas.
-/

noncomputable section

namespace SemanticBridge

theorem normalization_tri (n : ℕ) : Montagens.T n = Fase3.tri n := by
  have h₁ := Montagens.T_two_mul n
  have h₂ := Fase3.two_mul_tri n
  omega

theorem normalization_pair (u v : ℕ) : Montagens.pair u v = Fase3.cpair u v := by
  simp only [Montagens.pair, Fase3.cpair, normalization_tri]

theorem normalization_unpair (n : ℕ) : Montagens.unpair n = Fase3.cunpair n := by
  apply Fase3.cpair_bijective.1
  calc
    Fase3.cpair (Montagens.unpair n).1 (Montagens.unpair n).2 = n := by
      rw [← normalization_pair]
      exact Montagens.pair_props.2.2.1 n
    _ = Fase3.cpair (Fase3.cunpair n).1 (Fase3.cunpair n).2 :=
      (Fase3.cpair_cunpair n).symm

theorem normalization_unpack3 (n : ℕ) : Montagens.unpack n = Fase3.decode4 n := by
  simp only [Montagens.unpack, normalization_unpair, Fase3.decode4]

theorem normalization_unpack2 (n : ℕ) : Montagens.unpack n = Dyadic2.unpack n := by
  rw [normalization_unpack3]
  rfl

theorem normalization_Z3 (n : ℕ) : Montagens.Zenc n = Fase3.zEnum n := by
  unfold Montagens.Zenc Fase3.zEnum
  split_ifs with h
  · rfl
  · have he : (n + 1) / 2 = n / 2 + 1 := by omega
    rw [he]
    push_cast
    rfl

theorem normalization_Z2 (n : ℕ) : Montagens.Zenc n = Dyadic2.Zenum n := by
  rw [normalization_Z3]
  rfl

theorem normalization_rank3 (r : ℚ) : Montagens.rank .three r = Fase3.rankQ r := by
  have hp : Montagens.Pred .three r = Fase3.predQ r := by
    ext v
    rw [Montagens.mem_Pred_iff, Fase3.mem_predQ]
    rfl
  exact congrArg Finset.card hp

theorem normalization_rankStar3 (r : Montagens.Qstar) :
    Montagens.rankStar .three r = Fase3.rankQstar r := by
  have hp : Montagens.PredStar .three r = Fase3.predQstar r := by
    ext v
    rw [Montagens.mem_PredStar_iff, Fase3.mem_predQstar]
    rfl
  exact congrArg Finset.card hp

theorem normalization_Q3 (n : ℕ) : Montagens.Qenum .three n = Fase3.Qenum n := by
  apply Fase3.rankQ_bijective.1
  have hr : Fase3.rankQ (Fase3.Qenum n) = n :=
    (Equiv.ofBijective Fase3.rankQ Fase3.rankQ_bijective).apply_symm_apply n
  rw [hr, ← normalization_rank3, Montagens.rank_Qenum]

theorem normalization_Qstar3 (n : ℕ) :
    Montagens.QstarEnum .three n = Fase3.QstarEnum n := by
  apply Fase3.rankQstar_bijective.1
  have hr : Fase3.rankQstar (Fase3.QstarEnum n) = n :=
    (Equiv.ofBijective Fase3.rankQstar Fase3.rankQstar_bijective).apply_symm_apply n
  rw [hr, ← normalization_rankStar3, Montagens.rankStar_QstarEnum]

theorem normalization_rank2 (r : ℚ) : Montagens.rank .two r = Dyadic2.Qrank r := by
  change (Montagens.Pred .two r).card =
    ({v : ℚ | Dyadic2.htKey v < Dyadic2.htKey r} : Set ℚ).ncard
  rw [← Set.ncard_coe_finset]
  congr 1
  ext v
  simp only [Finset.mem_coe, Set.mem_setOf_eq, Montagens.mem_Pred_iff]
  rfl

theorem normalization_rankStar2 (r : Montagens.Qstar) :
    Montagens.rankStar .two r = Dyadic2.Qstarrank r := by
  change (Montagens.PredStar .two r).card =
    ({v : Montagens.Qstar | Dyadic2.htKey v.1 < Dyadic2.htKey r.1} : Set Montagens.Qstar).ncard
  rw [← Set.ncard_coe_finset]
  congr 1
  ext v
  simp only [Finset.mem_coe, Set.mem_setOf_eq, Montagens.mem_PredStar_iff]
  rfl

theorem normalization_Q2 (n : ℕ) : Montagens.Qenum .two n = Dyadic2.Qenum n := by
  apply Dyadic2.Qrank_bijective.1
  have hr : Dyadic2.Qrank (Dyadic2.Qenum n) = n :=
    (Equiv.ofBijective Dyadic2.Qrank Dyadic2.Qrank_bijective).apply_symm_apply n
  rw [hr, ← normalization_rank2, Montagens.rank_Qenum]

theorem normalization_Qstar2 (n : ℕ) :
    Montagens.QstarEnum .two n = Dyadic2.Qstar n := by
  apply Dyadic2.Qstarrank_bijective.1
  have hr : Dyadic2.Qstarrank (Dyadic2.Qstar n) = n :=
    (Equiv.ofBijective Dyadic2.Qstarrank Dyadic2.Qstarrank_bijective).apply_symm_apply n
  rw [hr, ← normalization_rankStar2, Montagens.rankStar_QstarEnum]

/-- Identidade literal dos átomos para cada endereço da Fase 3. -/
theorem normalization_ofFase3 (n : ℕ) :
    normalizationAtomEquiv (ofFase3 n) = Montagens.dec .three n := by
  apply Montagens.Atom.ext
  · simp only [normalizationAtomEquiv, ofFase3, Montagens.dec_k, normalization_unpack3,
      Fase3.gK]
    rfl
  · simp [normalizationAtomEquiv, ofFase3, Montagens.dec_m, normalization_unpack3,
      normalization_Z3, Fase3.gM]
  · simp [normalizationAtomEquiv, ofFase3, Montagens.dec_y, normalization_unpack3,
      normalization_Q3, Fase3.y0]
  · simp [normalizationAtomEquiv, ofFase3, Montagens.dec_s, normalization_unpack3,
      normalization_Qstar3, Fase3.slope]

/-- Identidade literal dos átomos para cada endereço da Fase 2. -/
theorem normalization_ofFase2 (n : ℕ) :
    normalizationAtomEquiv (ofFase2 n) = Montagens.dec .two n := by
  apply Montagens.Atom.ext
  · simp [normalizationAtomEquiv, ofFase2, Montagens.dec_k, normalization_unpack2,
      Dyadic2.scale]
  · simp [normalizationAtomEquiv, ofFase2, Montagens.dec_m, normalization_unpack2,
      normalization_Z2, Dyadic2.cellIdx]
  · simp [normalizationAtomEquiv, ofFase2, Montagens.dec_y, normalization_unpack2,
      normalization_Q2, Dyadic2.y0n]
  · simp [normalizationAtomEquiv, ofFase2, Montagens.dec_s, normalization_unpack2,
      normalization_Qstar2, Dyadic2.sn]

end SemanticBridge
