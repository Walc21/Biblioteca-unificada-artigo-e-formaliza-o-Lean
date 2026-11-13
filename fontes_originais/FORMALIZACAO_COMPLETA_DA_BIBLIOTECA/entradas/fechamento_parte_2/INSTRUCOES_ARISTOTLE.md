# Formalização do fechamento da parte 2

O objetivo é formalizar o documento `Fechamento_Parte_2_Formalizacao_Aristotle.tex` como uma extensão do projeto `RequestProject` incluído neste pacote. O documento é autocontido para os objetos usados nas novas construções e indica quais teoremas originais podem ser reutilizados.

Preserve os 31 módulos originais e seus enunciados públicos. Acrescente os módulos de fechamento no namespace `Artigo.Closure`, provando as igualdades com os objetos existentes antes de substituir usos da especificação por versões computáveis.

Execute as etapas na ordem da seção “Ordem de execução para o Aristotle”. As entregas principais são:

1. A família extrema como cadeia para todo N par admissível e seu testemunho de árvore bem formada para N potência de dois.
2. A extensão C² explícita por jatos dos extremos, o conversor de `ContDiffOn` para os jatos locais e o transporte dos erros, da curvatura e das coberturas.
3. Continuidade pública das avaliações e igualdade entre a soma de perdas por folhas e a perda empírica por índices de observações.
4. DP racional executável, com ausência explícita, ponteiros e reconstrução, e sua igualdade com `Cfix`, `Cvar`, `Cb` e `Cstar`.
5. Instrumentação operacional do mesmo programa, tamanho dos custos, limites de trabalho e memória e uma instanciação concreta do backend aritmético. A cota rápida requer as provas do backend correspondente; a multiplicação isoladamente não supre a normalização de frações.
6. Lei eventual e extremos das fases sincronizadas sem aplicar o envelope C² à função quadrática por partes.
7. Interfaces de domínio para altura mínima e sua compatibilidade com `heightFor` onde existe testemunho.

Não acrescente `sorry`, `admit` ou novos axiomas. Não transforme uma conclusão em hipótese nem reintroduza C² global nos enunciados locais. Propriedades paramétricas do backend devem aparecer como hipóteses de um teorema sobre um backend e ser demonstradas na instanciação concreta.

Registre o ambiente efetivamente utilizado e entregue `lean-toolchain`, configuração Lake e `lake-manifest.json`, todos os fontes, os testes finitos e os logs de compilação. Se o ambiente original não estiver disponível, escolha uma versão compatível explicitamente e valide nela todos os módulos; não apresente isso como reprodução da execução antiga.

O `Main.lean` original importa apenas Mathlib. Construa um agregador que importe todos os módulos originais e novos. Rode `#print axioms` para os resultados públicos e exporte a saída real. Compile o conjunto completo, incluindo os módulos que não forem alcançados pelo alvo padrão.

As demonstrações matemáticas estão no TeX. As verificações numéricas finitas no arquivo `checagens_matematicas.json` são verificações auxiliares das fórmulas, não certificados Lean. O documento LaTeX foi compilado e inspecionado; os módulos novos ainda precisam ser implementados e verificados pelo Aristotle.

O diretório `RequestProject` e o `Artigo_2_original.tex` preservam os conteúdos originais usados na revisão. As figuras do artigo original não integram este pacote; o novo TeX não depende delas nem de arquivos externos.
