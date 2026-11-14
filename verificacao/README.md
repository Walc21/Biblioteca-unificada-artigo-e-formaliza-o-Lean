# Verificação numérica (aritmética racional exata)

Seis programas em Python que acompanham o artigo. Eles **não fazem parte das demonstrações**: nenhum
teorema, lema ou proposição do volume depende deles. Registram verificações de **instâncias finitas** em
aritmética exata (`fractions.Fraction`) e geram tabelas e figuras. A prova formal está em [`lean4/`](../lean4).

| Programa | Onde aparece no artigo | Resultados registrados |
|---|---|---|
| `reproduzir_curvas.py` | Partes I e III: indexação, complexidade de endereços, catálogos finitos, equivalência ReLU, aritmética intervalar, formatos de codificação (4096 montagens), tabelas do refinamento adaptativo e figuras da Parte I | `resultados_curvas.json` |
| `seletor_dinamico_exato.py` | Parte III, «Validação computacional exata» (tabelas de comparação e de auditoria e figuras do estado de fronteira e da comparação de seletores) | `resultados.json` |
| `constante_diadica.py` | Parte III, constante quadrática, fases e envelope $C^2$ (figuras da constante, das fases e do envelope) | `resultados_constante_diadica.json` |
| `espacos_aproximacao.py` | Parte IV, auditoria racional das alturas (tabela de alturas e figura das agendas) | `resultados_espacos_aproximacao.json` |
| `reversibilidade_regularizada.py` | Parte IV, «Validação executável» (2952 idas e voltas, 84 redes quantizadas, 1260 instâncias) | `resultados_reversibilidade.json` |
| `restricoes_rede.py` | Parte IV, figura de restrições de rede | `resultados_restricoes_rede.json` |

Os `.json` são as saídas registradas na edição do artigo. Nos diagnósticos logarítmicos auxiliares há ponto
flutuante, e por isso não se exige identidade byte a byte desses campos entre plataformas.

## Como executar

```bash
pip install -r requirements.txt
python3 seletor_dinamico_exato.py --output-root /tmp/saida
```

Passe sempre `--output-root` apontando para uma pasta de trabalho: os programas criam nela
`reproducibility/selecao/` com os resultados e as figuras. No `seletor_dinamico_exato.py` o padrão é a
pasta-pai deste diretório, isto é, a raiz do repositório. O `numpy` e o `matplotlib` só entram depois da
seleção, para desenhar as figuras.

O `reproduzir_curvas.py` grava `resultados.json` e as figuras em `--output-root`; aqui o registro foi guardado como `resultados_curvas.json`, para não colidir com o do seletor. Os resultados registrados foram gerados com Python 3.12.
