module
public import Unified.SemanticBridge.Geometry
@[expose] public section

/-!
# Pontes de parâmetros e reendereçamento

Cada fase enumera `(k,m,y₀,s)` possivelmente em ordem diferente. Para evitar
a hipótese falsa de igualdade dos endereços naturais, cada quadrupla é
convertida no tipo geométrico `Dyadic.Lib.Atom`, e depois reendereçada pela
bijeção canônica `Dyadic.Lib.encode` / `Dyadic.Lib.decode`.
-/

namespace SemanticBridge

/-- Representação geométrica do átomo de um endereço da Fase 1. -/
noncomputable def ofFase1 (n : ℕ) : Dyadic.Lib.Atom :=
  { k := Fase1.kOf n
    m := Fase1.mOf n
    y0 := Fase1.y0n n
    s := (Fase1.sn n).1
    hs := (Fase1.sn n).2 }

/-- Representação geométrica do átomo de um endereço da Fase 2. -/
noncomputable def ofFase2 (n : ℕ) : Dyadic.Lib.Atom :=
  { k := Dyadic2.scale n
    m := Dyadic2.cellIdx n
    y0 := Dyadic2.y0n n
    s := Dyadic2.sn n
    hs := Dyadic2.sn_ne_zero n }

/-- Representação geométrica do átomo de um endereço da Fase 3. -/
noncomputable def ofFase3 (n : ℕ) : Dyadic.Lib.Atom :=
  { k := Fase3.gK n
    m := Fase3.gM n
    y0 := Fase3.y0 n
    s := Fase3.slope n
    hs := Fase3.slope_ne_zero n }

/-- Endereço canônico correspondente aos parâmetros da Fase 1. -/
noncomputable def readdress1 (n : ℕ) : ℕ := Dyadic.Lib.encode (ofFase1 n)
/-- Endereço canônico correspondente aos parâmetros da Fase 2. -/
noncomputable def readdress2 (n : ℕ) : ℕ := Dyadic.Lib.encode (ofFase2 n)
/-- Endereço canônico correspondente aos parâmetros da Fase 3. -/
noncomputable def readdress3 (n : ℕ) : ℕ := Dyadic.Lib.encode (ofFase3 n)

/-- A decodificação canônica recupera exatamente os parâmetros da Fase 1. -/
theorem readdress1_spec (n : ℕ) :
    Dyadic.Lib.decode (readdress1 n) = ofFase1 n :=
  Dyadic.Lib.decode_encode (ofFase1 n)

/-- A decodificação canônica recupera exatamente os parâmetros da Fase 2. -/
theorem readdress2_spec (n : ℕ) :
    Dyadic.Lib.decode (readdress2 n) = ofFase2 n :=
  Dyadic.Lib.decode_encode (ofFase2 n)

/-- A decodificação canônica recupera exatamente os parâmetros da Fase 3. -/
theorem readdress3_spec (n : ℕ) :
    Dyadic.Lib.decode (readdress3 n) = ofFase3 n :=
  Dyadic.Lib.decode_encode (ofFase3 n)

/-- O reendereçamento não altera a escala e a célula da Fase 2. -/
theorem readdress2_cell_params (n : ℕ) :
    (Dyadic.Lib.decode (readdress2 n)).k = Dyadic2.scale n ∧
    (Dyadic.Lib.decode (readdress2 n)).m = Dyadic2.cellIdx n := by
  rw [readdress2_spec]
  exact ⟨rfl, rfl⟩

/-- O reendereçamento não altera valor ancorado nem inclinação da Fase 2. -/
theorem readdress2_line_params (n : ℕ) :
    (Dyadic.Lib.decode (readdress2 n)).y0 = Dyadic2.y0n n ∧
    (Dyadic.Lib.decode (readdress2 n)).s = Dyadic2.sn n := by
  rw [readdress2_spec]
  exact ⟨rfl, rfl⟩

/-- Cada quadrupla de parâmetros canônicos aparece na Fase 2. -/
theorem canonical_params_in_fase2 (a : Dyadic.Lib.Atom) :
    ∃ n : ℕ, Dyadic2.scale n = a.k ∧ Dyadic2.cellIdx n = a.m ∧
      Dyadic2.y0n n = a.y0 ∧ Dyadic2.sn n = a.s :=
  Dyadic2.exists_address a.k a.m a.y0 a.s a.hs

end SemanticBridge
