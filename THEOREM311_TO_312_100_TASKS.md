# 从 IUT III Theorem 3.11 到 Corollary 3.12 的 100 项待办

本清单以论文原文为边界，目标是从论文 Theorem 3.11 开头已经固定的
initial Theta-data 与 distinct Theta-Hodge-theater family，source-faithfully
推出 Theorem 3.11(i)--(iii)，再完成 Corollary 3.12 证明的 Step (xi)。

这里的“尽可能互不相干”指每项都有独立的对象边界、原文出处和验收产物；
它不声称数学依赖图没有边。一个任务可以消费另一个任务已经交付的、且有
编译证据的 source 对象，但不能把未证明的接口字段当作对象存在性。

## 不计入 100 项的当前已知边界

* Lean/Mathlib 普通算术、有限商、一般群作用、有限模型和 determinant kernel
  可以复用，但它们没有 IUT source 解释。
* `SourceSharedBoundary.lean` 的固定第 1 列投影是共享输入投影，不是完整
  Theorem 1.5 vertical coricity，也不是 Step (xi) 证明。
* `Contract.lean` 的 `cor312_of_constructed_stepXI` 只证明显式 contract 的
  `le_trans` 结论；`ParametricStepXI` 仍要求调用方提供 IPL/SHE/APT 和比较式。
* `SourcePacketDegreeLedger` 当前只能记为 `interface`：没有当前版本成功编译
  证据时，不得记为 `proved`，也不得把它的字段投影当作 Prop. 3.2/3.4 完成。
* Definition 3.1 的 arithmetic-to-source 路线（审计中的 D11-E）不是论文
  Theorem 3.11 的额外量词。本清单不把它偷换成论文输入；若项目另行要求，
  它应作为独立路线，不得覆盖下面的 source-input 任务。

## 统一验收闸门

每一项完成时都必须有：原文页码/命题引用、精确的 Lean 类型、从真实 source
对象构造而非同名字段注入、当前文件或目标模块编译成功、warning 为 0、无
`sorryAx`、无自定义 `axiom`/`opaque`，以及 endpoint 的 `#print axioms`。同时
要把该项的状态和证据写回审计文档。未满足任一项，状态保持 `pending` 或
`interface`，不能写 `proved`。

## A. 原文边界与输入合同（1--10）

1. **固定 Theorem 3.11 原文快照。** 锁定论文版本、SHA-256、物理页 153--159，建立 Theorem 3.11 开头、(i)、(ii)、(iii) 和 proof 的逐段引用索引。
2. **形式化 initial Theta-data 的原文量词。** 将 `F/F`, `X_{F,l}`, `C_K`, `V`, `V_mod^bad`, `epsilon` 的输入边界写成 source contract；尚无从 InitialThetaArithmeticData 构造完整 SourceDefinition31Data 的证明；reduction、torsion/Galois、orbicurve、section、cusp 等真实对象仍需构造不得用更小 arithmetic record 偷换。
3. **形式化 distinct Hodge-theater family。** 对所有 `n,m ∈ Z` 保留论文的全称量词、family carrier 和 distinctness；尚无从 initial Θ-data 构造任意论文要求的完整 distinct family；OriginalInput.family 目前是显式输入字段。不得以一个具体 theater 或 `Nonempty` 替代 family。
4. **固定二维 lattice 索引。** 证明论文的 `(n,m)` 索引、列/行投影和 Lean 的 index equivalence 逐项对应，保留 dependent carrier 的 `HEq` 需要。
5. **固定标签全集。** 构造并证明 `F_l`、`|F_l|`、`F_l^*`、`LabCusp^±` 的来源、包含关系和 cardinality；不得删除任意标签。
6. **建立术语来源台账。** 给每个 production 类型（theater、prime-strip、packet、log-shell、Frobenioid、Kummer map、pilot object）记录论文定义/命题来源和 Lean 声明。
7. **建立 source-input 非存在性闸门。** 证明 source contract 不能由字段名、`Nonempty`、`Classical.choice` 或接口 certificate 自动生成；把这条限制做成可检查的审计规则。
8. **建立 Theorem 3.11 输出骨架。** 写出与论文相同量词的 `(i)--(iii)` output type，但所有尚未构造的 source 对象必须显式留在待办边界，不得以占位结论填充。
9. **建立输入到输出依赖图。** 将原文开头输入、IUT I 1.5/6.9、IUT II 4.6--4.11、IUT III 2.1/2.3/3.2/3.4/3.5/3.7/3.9/3.10 和 Step (xi) 分成可审计边。
10. **建立状态更新脚本。** 使状态只能在编译、warning、`sorryAx`、custom-axiom、量词审计证据齐全后从 `pending/interface` 改变；文档更新不得反向制造数学结论。

## B. Hodge theaters、D-theater 与 procession（11--30）

11. **构造每列的 D-Theta bridge。** 从论文给出的 `n,m` theater family 和 IUT I vertical-coricit source 数据构造 `n,◦HT_D` 的 bridge；不是只声明一个 D-theater 类型。
12. **证明 D-theater 的 isomorphism-class 独立性。** 对“determined up to isomorphism”给出实际等价关系、代表无关性和后续 transport 定理。
13. **构造 Theorem 1.5(i) vertical coricity maps。** 对每个固定 `n`、所有 `m` 构造 vertical family、links 和 source/target carrier。
14. **证明 vertical coricity 的恒等、复合和逆向律。** 保留论文的 map 方向、索引和 dependent source/target，不改成普通同载体函数。
15. **构造 Theorem 1.5(ii) horizontal coricity maps。** 对相邻列 `n` 与 `n+1` 构造全量 horizontal arrows 及其 source objects。
16. **证明 Theorem 1.5(iii) bi-coric square。** 证明 horizontal/vertical 两条路线在论文指定部分的相容性，明确哪些 square 不是全局 1-commutative。
17. **构造 Theorem 1.5(iv) mono-analytic log-shell coricity。** 为 nonarchimedean 与 archimedean local carriers 分别给出真实 source/target 结构和 link。
18. **完成 IUT I Proposition 6.9(ii) 的 natural procession functor。** 从 D-Theta bridge 得到 D-prime-strip procession，而非只构造固定一列的 shadow。
19. **构造所有 procession stages。** 对 `0 ≤ k ≤ l*` 构造 `D_0,...,D_k`、stage inclusions、capsules 和最终有限 stage；不得只保留 `k=l*` 投影。
20. **证明 procession inclusion chain。** 证明论文显示的逐级嵌入、source/target carrier 一致性和 inclusion component 的自然性。
21. **证明 procession morphism 的 functoriality。** 对任意 source procession isomorphism 构造 induced map，并证明 stage、action、degree 和 packet transport 相容。
22. **构造 arbitrary spoke permutation。** 对所有允许的 spoke/index permutation 给出真实 permutation object、逆元和对 procession 的作用。
23. **证明 spoke permutation 的 link naturality。** 证明 permutation 与每一条 stage/link component 的交换式，保留论文的端点和方向。
24. **完成 `F_l` 到 `|F_l|` 的标签转换。** 将 arithmetic labels、naked index sets 与 mono-analytic ±-processions 的过渡逐项构造。
25. **完成 `|F_l|` 到 `F_l^*` 的标签转换。** 构造 `⋇`-procession 所需的标签识别和 `0`/`⟨F_l^*⟩` 的论文规定识别。
26. **证明标签全集不可省略。** 形式化论文关于必须使用全部 `F_l`/`|F_l|` labels 的约束，并让 packet/volume 构造依赖该全集。
27. **构造 F/D prime-strip equivalences。** 对 `F^{⊢×μ}`, `F^{⊩▶×μ}` 与 D-prime-strips 给出真实 poly-isomorphism，而非仅给 carrier equality。
28. **构造 D-strip action 与 degree。** 由 source monoid/action 产生 element action、multiplicative degree 和 unit/one/mul laws。
29. **完成全列 q/scale transport。** 对所有 `n,m,k,j` 证明 q、label-scale、log-scale 沿 vertical link、stage link 和 spoke map 的传输。
30. **交付 H1/H2 source-faithful alignment。** 将 bridge、theater、procession、spoke、label 和 transport 组装成可被 K1/K2/P1/P2 消费的真实 source object；不得把 projection ledger 标为完整 output。

## C. Proposition 3.2、3.4、3.9 的 packet/degree/volume（31--50）

31. **构造 `I(S_{j+1;n,◦D⊢}_{v_Q})`。** 对每个 `n,j,v_Q` 构造论文要求的 topological module 和 mono-analytic integral structure。
32. **证明 local integral inclusion。** 证明 `I(S) ⊆ I_Q(S)` 的 source inclusion、carrier 类型和每个 place index 的自然性。
33. **构造 `I_Q(S)` 的 Q-span。** 保留论文的张量/有理化来源，证明其不是任意 `Type` 或人为 product。
34. **构造 place-level packet `I(S_{j+1,j;n,◦D⊢}_v)`。** 对每个 `v|v_Q` 构造 local tensor packet 及其 integral carrier。
35. **构造 place-level Q-span。** 给出 `I_Q(S_{j+1,j;n,◦D⊢}_v)`、包含映射和与 `v_Q` packet 的 projection compatibility。
36. **证明 direct-summand 索引对应 places。** 证明论文所述 `j+1` 因子/direct summand 与 `v|v_Q` 的基数和索引一致。
37. **构造全标签 tensor packet。** 对每个 `j∈F_l^*`、每个 `v_Q` 将 place packets 按论文的 tensor product 装配，保留标签作用。
38. **构造 packet 上的 `Ism`/order-2 action。** 分别处理 nonarchimedean 的 `Ism` copies 和 archimedean 的 order-2 poly-automorphisms。
39. **证明 packet action 保持 integral/Q-span。** 证明 action 对两个 carrier 层均良定义，并保留 direct-summand 方向。
40. **构造 packet local log-volume。** 从 source Haar/mono-analytic volume 定义每个 packet 的 log-volume，不得使用普通 `Real` 函数替代 source volume。
41. **证明 procession-normalized volume。** 对 `j∈F_l^*` 按论文规定平均/归一化，并证明 label normalization 的精确因子。
42. **证明 volume 沿 stage/procession transport。** 对 inclusion、stage isomorphism 和 D/F poly-isomorphism 证明 log-volume 传输。
43. **证明 Ind1 volume invariance。** 对 procession automorphism 的 quotient action 证明 normalized log-volume 不变。
44. **证明 Ind2 volume invariance。** 对每个 local independent action 证明 packet volume 和 global normalized volume 不变。
45. **证明 Ind3 volume upper inequality。** 从 nonarchimedean inclusion/archimedean surjection 的真实 source maps 推出论文指定的上界方向，不能改成 equality。
46. **构造 Proposition 3.4(ii) 的 F/D packet poly-isomorphism。** 将 local packet、Q-span、degree 和 action 一起 transport，保留所有 place labels。
47. **构造 actual LGP monoid。** 从 source F-prime-strip、packet action 和 degree 构造论文的 `Ψ^⊥_{LGP}`/LGP-monoid carrier，不得用抽象 monoid 名称代替。
48. **构造 bad-place splitting monoid。** 对每个 `v∈V_mod^bad` 构造 Proposition 3.5(ii)(c) 的 splitting monoid、action 和 source embedding。
49. **构造 global product carrier。** 对每个 `j` 构造 `M_MOD,j^* = M_mod,j^*` 在 `∏_{v_Q} I_Q(S) ∏` 中的真实子集和 membership。
50. **证明 global degree/log-volume identity。** 证明 Proposition 3.9(iii) 中 global degree 由 local procession-normalized log-volumes 计算，并保留 `MOD`/`mod` 区别。

## D. Vertical log-Kummer、Frobenioid 与 Proposition 3.10（51--72）

51. **构造 local mono-theta environments。** 对每个 selected/bad place 从 source theater/curve 数据构造 local mono-theta environment，而非测试 carrier。
52. **构造 etale theta local Kummer map。** 将 cyclotome、roots、Galois action 和 theta monoid 组成真实 local Kummer correspondence。
53. **构造 κ-coric local Kummer map。** 使用 IUT I Definition 5.2/Example 5.1 的 source κ-coric data，保留 label 和 action。
54. **构造 labelled log-Kummer data。** 对每个 `t∈LabCusp^±(n,◦D≻)` 构造论文显示的 labelled objects 与 maps。
55. **证明 local Kummer map 是同构。** 给出 map、inverse、left/right inverse 和 dependent source/target 类型检查。
56. **证明 Kummer 与 local tensor packet 相容。** 逐项证明 `I`, `I_Q`、F/D packet 和 Kummer map 的 commuting squares。
57. **证明 Kummer 与 local log-volume 相容。** 证明 Proposition 3.9(ii)/(iv) 所需的 log-volume preservation/transport。
58. **证明 nonarchimedean upper-semi inclusion。** 对每个 `v_Q∈V_Q^non` 精确实现 `source ⊆ target` 的论文方向。
59. **证明 archimedean upper-semi surjection。** 对每个 `v_Q∈V_Q^arc` 精确实现 `target ↠ source` 及 witness，不改成集合相等。
60. **证明 vertical upper-semi 迭代。** 对任意 `m≤n` 构造 source witnesses、复合和单调链，保留 nonarch/arch 两种方向。
61. **证明 labelled Kummer global bijectivity。** 从 local labelled maps 组装全局 map，并证明 injective/surjective/bijective。
62. **构造 global number field `M_MOD,j^*`。** 对每个 `j` 从 source Frobenius/theater 数据得到实际 number field carrier。
63. **构造 global number field `M_mod,j^*`。** 单独构造 `mod` 版本，证明其来源和与 `MOD` 版本的关系，不能直接令二者 definitional equal。
64. **构造 global non-realified Frobenioids。** 构造 `F_MOD,j^*` 和 `F_mod,j^*` 的 objects、morphisms、degree、transport 和 monoid laws。
65. **构造 global realified Frobenioids。** 构造 `F_MOD,j^{*R}` 和 `F_mod,j^{*R}`，证明 realification 的 source definition 和 composition。
66. **构造 `MOD`/`mod` natural isomorphisms。** 给出 number field、non-realified、realified 三组自然同构及 component law。
67. **证明 Frobenioid degree/log-volume correspondence。** 对 global objects 证明 degree 可由 packet log-volume 计算，并保留 normalization。
68. **构造 realification maps。** 将 non-realified objects 映到 realified objects，证明 degree/realification 的 source equations。
69. **构造 Frobenioid transport maps。** 证明 transport 的 unit/mul/degree/realification law 以及与 Kummer map 的交换式。
70. **证明 `MOD` 沿 log-links 的 m-compatibility。** 只证明论文允许的 root-of-unity/zero-log-link compatibility，不扩展到 `mod` 版本。
71. **证明 `mod` 的 upper-semi boundary。** 保留论文的 local indeterminacy 和方向，明确不能从 map 名称推断逆元或 equality。
72. **完成 Proposition 3.10 comparison。** 构造 global/local Kummer、degree、realification、labelled/evaluation comparison 的完整 source square。

## E. Θ×μ LGP-link 横向兼容与 Theorem 3.11(iii) 前置（73--84）

73. **构造 Θ×μ LGP-link。** 对相邻列 `(n,m)` 与 `(n+1,m)` 构造论文的 full poly-isomorphism 和 source link carrier。
74. **构造 unit portion。** 构造 `F^{⊢×μ}` prime-strip 的 unit portion poly-isomorphism，并证明与 Kummer map 的相容性。
75. **构造 value-group portion。** 构造 `F^{⊩▶}` prime-strip 的 value-group poly-isomorphism，并证明 Θ-pilot 到 q-pilot 的方向。
76. **证明 etale theta cyclotomic rigidity。** 证明相关 cyclotomes/Kummer theory 对 horizontal link 的稳定性和无额外选择性。
77. **证明 κ-coric cyclotomic rigidity。** 对 κ-coric functions 的 source algorithm、cyclotome 和 horizontal transport 给出同样的兼容性。
78. **构造 environment-strip natural isomorphisms。** 将 `F^{⊢×μ}_△` 与 environment strips、D-side 与 F-side 对应起来。
79. **证明 horizontal full poly-isomorphism。** 证明 `n` 到 `n+1` 的 unit/value 两部分与 Theorem 1.5(ii)/(iii) horizontal arrows 兼容。
80. **构造 etale-picture permutation symmetry。** 对任意允许的 permutation symmetry 构造 theater、strip、R-data 的 induced poly-isomorphism。
81. **构造 `n,◦R` source data。** 从 D-theater 的 mono-theta environments、Kummer maps 和 prime-strips 构造论文的 `R` 数据。
82. **证明 `R` 数据的 horizontal poly-isomorphism。** 证明 `n,◦R ≃ n+1,◦R` 与 F-prime-strip、environment 和 Kummer constructions 同步。
83. **证明 stabilized/equivariant/functorial 性。** 对 horizontal link 的任意 domain/codomain automorphism 证明算法、Kummer、poly-isomorphism、evaluation 的自然性。
84. **处理 invisible indeterminacies 与评价自然性。** 形式化 roots of unity、`±1`、label forgetting 的 quotient/orbit，证明其不改变论文关心的 set/global Frobenioid/evaluation 结果。

## F. Theorem 3.11 组装与 Corollary 3.12 Step (xi)（85--100）

85. **组装 Theorem 3.11(i)。** 以论文原文量词交付 multiradial representation、(a)--(c) data、Ind1、Ind2、functoriality 和 permutation compatibility。
86. **组装 Theorem 3.11(ii)。** 以论文原文量词交付 labelled log-Kummer correspondence、packet/monoid/Frobenioid isomorphisms、Ind3 的两种方向和 log-volume compatibility。
87. **组装 Theorem 3.11(iii)。** 以论文原文量词交付 Θ×μ LGP-link compatibility、Kummer/evaluation squares、permutation stability 和无额外 indeterminacy 结论。
88. **构造 `(1,0)` 的 q-pilot object。** 在实际 global realified Frobenioid 与相关 holomorphic log-shell 中定义 q-pilot object，而非把一个实数叫作 q-pilot。
89. **构造 `(0,0)` 的 Θ-pilot object。** 在实际 Θ-theater、theta function/value、Frobenioid carrier 中定义第一幂 Θ-pilot object。
90. **证明 Θ×μ gluing sends Θ-pilot to q-pilot。** 证明 `(0,0) → (1,0)` link 的 gluing interpretation、unit/value portions 和 object-level correspondence。
91. **构造 multiradial possible-output set。** 从 Theorem 3.11 algorithm 得到 `{}_{0,◦}U`、`{}_{1,◦}U` 及其 ambient `U_Q`，保留“collection of possibilities”量词。
92. **证明 0-column 到 1-column 的 permutation identification。** 构造论文使用的 permutation-symmetry isomorphism，并证明 output set 的 transport。
93. **证明 IPL。** 证明 output possibilities 的 `F^{⊩▶}` prime-strip portion 与 `(1,0)` q-pilot input prime-strip 之间是 full poly-isomorphism。
94. **证明 SHE。** 证明 output construction 可完全用固定第 1 列 arithmetic holomorphic structure 的 ring/scheme operations 表达。
95. **构造 APT。** 构造 algorithmic parallel transport，明确输入、输出、路径复合、逆向和 source invariants。
96. **证明 APT 保持 IPL/SHE 与 indeterminacy invariants。** 证明 parallel transport 与 Ind1/Ind2/Ind3、Kummer、log-link、volume 数据相容。
97. **构造固定第 1 列 holomorphic log-shell。** 为所有相关 `v,j` 构造论文 Step (xi) 使用的 fixed one-column local holomorphic containers。
98. **构造 holomorphic hull 并证明紧性/包含性。** 从 possible images 构造 `{}_{1,◦}U ⊇ {}_{1,◦}U` 的 hull，证明论文所需 compactness、membership 和 finite negative log-volume。
99. **构造 arithmetic vector-bundle localizations。** 将 hull output 从 local-field tensor regions 改写为第 1 列 rings 上 arithmetic vector bundles 的 localizations，并保留 rank 大于 1 的 source carrier。
100. **完成 determinant、normalization、log-volume comparison 和最终 membership。** 构造正 tensor power 的 determinant，按 `j∈|F_l|` 正确归一化，证明 `-|log(q)| ∈ R_{≤-|log(Theta)|}`、`-|log(Theta)| ≥ -|log(q)|` 以及 Corollary 3.12 的 `C_Theta ≥ -1` 结论；同时证明 Step (xi-g) 的两种 q-pilot log-volume 计算相等。

## 交付记录格式

每项完成后只记录以下事实：`ID`、Lean 文件和声明、原文引用、实际构造的
source 对象、精确量词/映射方向、编译命令和退出码、warning 数、`#print axioms`
输出、`sorryAx`/custom axiom 检查结果、状态变更日期。失败项记录失败原因，
不得用“已有接口”“字段存在”“历史曾编译”替代成功证据。
