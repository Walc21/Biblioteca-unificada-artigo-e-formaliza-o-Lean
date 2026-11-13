# Validação isolada dos pacotes recebidos

Os dois ambientes usam Lean 4.28.0 e o manifesto fixado da biblioteca local.
Essa é uma validação de compatibilidade reproduzível: os pacotes Aristotle
recebidos não incluem seus arquivos originais de configuração.

Cada ambiente tem seu próprio `.lake/build`. Apenas os pacotes de dependência
já instalados são compartilhados. Os fontes recebidos em `entradas/` são a
referência; não foram alterados para obter a compilação.

`ValidationAll.lean` importa todos os módulos, inclusive os que não são
alcançados pelo `Main.lean` original. O agregador do Artigo 2 importa 31
módulos; o da Parte I, nove.

Para reproduzir a validação completa a partir da raiz:

```bash
python3 scripts/validar_pacotes.py
```

Para conferir os hashes e resumir os logs já concluídos:

```bash
python3 scripts/validar_pacotes.py --resumir
```

Resultados em `resultados.json`. Cada pasta contém os logs de compilação,
auditoria de axiomas, conferência dos nomes do mapa e códigos de saída.
A auditoria usa o coletor oficial de axiomas do Lean, compartilhando a
visita ao grafo de dependências entre as declarações próprias.

| Pacote | Arquivos Lean | Declarações auditadas | Teoremas auditados |
| --- | --- | --- | --- |
| Parte I | 9 | 509 | 348 |
| Artigo 2 | 31 | 2.199 | 1.700 |

Ambos usam somente `propext`, `Classical.choice` e `Quot.sound`.
As contagens incluem declarações auxiliares geradas pelo Lean.

A validação isolada não afirma integração semântica. A Parte I tem agora
sua integração com a v2 provada separadamente nos seis módulos `Normalization*`,
descritos em `documentacao/INTEGRACAO_NORMALIZACAO.md`. O Artigo 2 permanece
separado, com suas diferenças de hipóteses registradas no mapa.
