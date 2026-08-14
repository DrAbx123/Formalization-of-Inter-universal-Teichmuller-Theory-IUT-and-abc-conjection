# A2 initial Theta-data source completion checklist

更新时间：2026-08-15

本检查单只对应 `THEOREM311_TO_312_100_TASKS.md` 的第 2 项。它把当前
A2 状态和从 `InitialThetaArithmeticData` 到论文原文六元组的缺口拆成可逐项
关闭的检查项；不把接口字段当作对象存在性，也不覆盖既有研究日志。

## 状态定义

- `[x]`：有当前批次的编译、零 warning、公理审计和原文量词证据，可以记为
  `proved`。
- `[r]`：已有可复用的基础结果，但它本身不关闭 A2 source 构造门。
- `[~]`：已写出 source contract、条件识别或可复用基础，但没有完成该项所需
  的 source 构造；状态只能记为 `interface`。
- `[ ]`：尚未完成实际构造或证明；状态记为 `pending`。
- 本检查单创建批次只编辑文档，不执行 Lean 编译、warning 检查或公理审计。

## 总状态

- `[~]` **A2-source-witness assembly（未到达的后续接口）**：独立文件中存在从显式
  source witness 到 native datum 的组装、几何/处绑定和 Clause A--F constructors，
  但它们依赖当前顺序前沿之后的 source witness；本轮不把这些接口计为 A2 已完成。
- `[~]` **A2-interface**：已形式化论文 source contract 及 conditional
  recognition。对应 `SourceNativeInitialThetaData` 和 source-facing 量词；
  这只识别已经携带完整六条 clause 的 source 对象。
- `[ ]` **A2-construction**：尚不存在
  `InitialThetaArithmeticData → SourceNativeInitialThetaData` 的忠实完整构造。
  目标类型必须是
  `∀ A, ∃ T : SourceNativeInitialThetaData, T.arithmetic = A`，不能用不同
  arithmetic datum 的 witness 替代。
- `[ ]` **A2-verification**：当前未闭合构造不能标记 `proved`；关闭时必须有
  原文引用、精确 Lean 类型、实际 source 对象、量词/映射方向、编译退出码、零
  warning、`#print axioms`、`sorryAx`/custom axiom 检查和状态日期。

## 依赖链

按以下顺序推进；前一项没有实际证明时，不开始后一项：

- `[~]` 已有显式 source witness 到完整 native datum 的结构性组装代码，但该组装
  不是当前 arithmetic-to-source 目标，不能作为本目标的完成标记：
  `SourceCompletion.toSourceNativeInitialThetaData` 及其
  `sourceCompletion_to_sourceNative` arithmetic-preserving 结论均已编译并审计。
  该项的输入仍是 source witness，不是任意 arithmetic record。
- `[~]` `SourceCompletion` package 本身仍是 source-supplied interface；其几何、
  群、局部和 cusp 字段没有被 arithmetic record 自动填充。
- `[ ]` `InitialThetaArithmeticData → SourceCompletion` 的 universal gate；当前
  arithmetic record 缺少原文所需 reduction、torsion/Galois、orbicurve、local
  section 和 cusp 条件，不能用字段名或选择算子伪造这条箭头。
- `[~]` `SourceCompletionSignQuotient` → `SourceSignQuotientData` 的逐字段绑定虽
  已有独立实现，但它位于 universal gate 之后；当前顺序不把该后续接口计为完成。
- `[ ]` `SourceSignQuotientData` → `SourceClauseA`。
- `[ ]` `SourceClauseA` → `SourceClauseB`。
- `[ ]` `SourceClauseB` → `SourceClauseC`。
- `[ ]` `SourceClauseC` → `SourceClauseD`。
- `[ ]` `SourceClauseD` → `SourceClauseE`。
- `[ ]` `SourceClauseE` → `SourceClauseF`。
- `[~]` `SourceClauseF` 与同一 source 记录中的六元组字段组装和
  `SourceInitialThetaTuple` 的等式恢复虽有独立实现，但均依赖尚未通过顺序前沿
  的后续 source witness；当前不计为完成。

## 可复用基础（不关闭 A2 构造门）

- `[r]` `ArithmeticData.lean`：`Fmod/F/K` 数域塔、曲线、`sqrt(-1)` 和次数互素
  结果；只能作为后续真实构造的输入。
- `[r]` `EllipticTorsion.lean`：代数闭包扭点 carrier、Galois action、连续
  representation 和 kernel field 结果；不能直接改名为 `E_K[l]` 的 source
  结论。
- `[r]` `Places.lean`：`NumberFieldPlace.restrictionSection`；只能供选定处
  section 投影使用。
- `[r]` `LocalQParameter.lean`：`FinitePlaceQCandidate` 非空性；不等于 Tate
  uniformization 或 q-parameter。
- `[r]` `SourceArithmeticPrelude.lean`：从任意 arithmetic record 实际构造规范
  `Fbar`、restriction section 的 selected-place 结构和 K/F `LTorsion` transport；
  这三个是已验证 arithmetic kernel，不是 Clause A--F 的存在性。
- `[~]` 现有 source contract 的投影、条件识别和等式传输；这些是接口/包装
  结果，不提供缺失 source 对象。

## SourceSignQuotientData

- `[ ]` **真实 `xF/cF` 几何**：从 `A.curve` 构造论文要求的
  `HyperbolicOrbicurve`、stack geometry、唯一 `-1` involution、sign action、
  sign quotient 及其 universal witness。
- `[ ]` **真实 `K`-侧对象**：构造 `X_F/C_F/X_K/C_K` 的 finite-etale 基本群、
  profinite exact sequences、`X → C` inclusion，并证明这些对象来自上述曲线与
  quotient，而非同名 carrier。
- `[ ]` **处与 section**：复用 `NumberFieldPlace.restrictionSection` 构造
  `V` 的实际 selected-place 集合；另外证明 `V_mod_bad` 非空、奇剩余特征及其
  与曲线坏约化的 source 关系。
- `[r]` **处/section arithmetic binding**：`SourcePlaceSelection` 和
  `SourceArithmeticPrelude` 已构造 selected `V`、section、bijection、comap 左逆，
  并证明从同一 source record 传输；坏约化来源仍未证明。
- `[ ]` **边界 cusp**：从真实非零 rank-one quotient 构造
  `epsilon : OrbicurveBoundaryCusp cK`，并保留 canonical generator 的来源。

## Clause A

- `[~]` `SourceClauseA.ofGoodOrMultiplicativeReduction` 只有后续 source-facing
  binding 实现；该接口依赖尚未通过的 universal gate，本轮不计为顺序完成。
- `[ ]` 对所有 `v ∈ V(F)^non` 证明曲线 stable reduction；量词必须是原文的
  全部非阿基米德处，不能缩小为选定处的下移像。
- `[ ]` 从 source 数据构造 field-of-moduli、最大可解中间域 `F_sol`，并证明其
  finite、Galois、solvable 和对同类扩张的 maximality。

## Clause B

- `[~]` `SourceClauseB.ofTateComparisonWitnesses` 只有后续 source-facing binding
  实现；它没有从 arithmetic record 产生 multiplicative/Tate/coprimality 输入，
  本轮不计为顺序完成。
- `[ ]` 证明坏处集合非空、乘法约化和 `TateCurveComparison`；q-parameter 必须
  来自 Tate uniformization。
- `[ ]` 证明 q-order 与 `l` 互素，并记录其与坏处/剩余特征的独立来源。
- `[~]` `FinitePlaceQCandidate.Nonempty` 可复用，但仅是候选 q 的非空性，不能
  关闭本 clause。
- `[ ]` 不得以“奇剩余特征”直接推出“剩余特征与 `l` 互素”；所需 coprimality
  必须另行证明。

## Clause C

- `[~]` `SourceClauseC.ofCanonicalRepresentation` 只有后续 source-facing binding
  实现；rationality、大像和 kernel-field identification 尚未从 arithmetic record
  构造，本轮不计为顺序完成。
- `[ ]` 从 arithmetic/source 数据构造 `Torsion23Rational`、rank-two torsion
  basis 和 `SL₂(F_l)` 大像。
- `[~]` 在 basis 已给定时复用 Galois representation 的连续性和 kernel field
  的有限/Galois 性；仍需证明它们与本 clause 的真实 `E_K[l]` 对齐。
- `[ ]` 证明 `A.K ≃ₐ[A.F]` 的 kernel field descent/identification，不能只使用
  代数闭包上的 torsion quotient。

## Clause D

- `[~]` 当前 quotient、cover、group embeddings 只能作为接口记录。
- `[~]` `SourceOrbicurveGroupData.ofFundamentalGroup`、`SourceOrbicurveFiniteEtaleCover.ofMap`
  和 `SourceClauseD` 只有后续 source-facing binding 实现；完整论文图表尚未到达，
  本轮不计为顺序完成。
- `[ ]` 构造论文要求的完整 cartesian diagrams、finite-etale diagrams 和 open
  subgroup diagrams，并证明每张图的交换性、有限性和来源对象一致。

## Clause E

- `[~]` selected-place section/equivalence 可由已有 restriction-section 数据
  投影；该投影不构造局部几何。
- `[~]` `SourceClauseE.ofLocalFamilies` 只有后续 local-family binding 实现；局部
  orbicurve、local group 和 diagram compatibility 尚未到达，本轮不计为顺序完成。
- `[ ]` 对每个有限处和无限处构造 completion-level orbicurves、local
  fundamental groups、decomposition-group outer surjections、局部模型及其
  base-change/diagram compatibility。
- `[ ]` 证明 local data 与同一 `SourceSignQuotientData` 的全局对象相容，而不
  复用全局 exact sequence 冒充局部对象。

## Clause F

- `[~]` `SourceTorsionRankOneQuotient.lean` 已构造代数闭包
  `LTorsion` 的 rank-one `ZMod l` quotient、kernel、线性等价和非零 quotient
  class。
- `[~]` `SourceClauseF.ofCanonicalBoundaryData` 只有后续 boundary binding 实现；
  quotient 的 K-rational descent、真实 cusp origin 和 canonical sign compatibility
  尚未到达，本轮不计为顺序完成。
- `[ ]` 证明该 quotient 是论文要求的 `E_K[l] → Q ≅ Z/lZ`，包含 `K`-rational
  descent；不得把 `LTorsion` quotient 改名替代它。
- `[ ]` 从该真实 quotient 构造 tuple 的 `epsilon`，证明 cusp origin、canonical
  generator 以及坏处 canonical `+/-1` compatibility。

## 关闭条件与禁止事项

- `[ ]` 每个 clause 必须在其单独命题结束并记录后才能进入下一 clause。
- `[ ]` `SourceCompletion` 的每个字段都必须是有原文出处的真实对象或已证明
  的结构性映射；字段名、`Nonempty`、`Classical.choice`、任意实数或有限例子
  不得作为存在性证明。
- `[ ]` 所有依赖字段闭合后，才可把
  `SourceCompletion → SourceNativeInitialThetaData` 标成 `proved`；再之后才
  能处理 pending 的 universal construction gate。
- `[ ]` A2 尚未达到可关闭的 verification 状态；虽然若干基础文件已经逐文件编译，
  但 arithmetic-to-source 目标未闭合。以后每个新增 1000 行以上的实质批次仍须
  统一执行编译、零-warning、`#print axioms` 及 `sorryAx`/custom axiom 审计。
- `[ ]` 每次状态更新必须追加到
  `THEOREM311_A2_INITIAL_THETA_QUANTIFIERS.md` 和
  `THEOREM311_DEPENDENCY_AUDIT.md`，不得删除或覆盖历史记录。

## 逐项关闭登记模板

关闭任一 `[ ]` 或 `[~]` 项时，只能在下表追加一行；不得用文档勾选代替
Lean 证明。若一项只完成了接口或投影，状态继续写 `interface`，并把缺失的
真实 source 对象写入“未闭合依赖”。

| 日期 | 检查项 | 状态 | Lean 声明/文件 | 原文出处 | 未闭合依赖 | 编译/警告/公理证据 |
|---|---|---|---|---|---|---|
| 2026-08-14 | source contract 与 conditional recognition | interface | `SourceDefinition31Quantifiers.lean` | IUT I, Definition 3.1(a)-(f) | arithmetic-to-source universal gate；真实 Clause A-F 来源对象 | N/A：本批次尚未达到 3000 行验证门槛 |
| 2026-08-14 | 显式 `SourceCompletion` package | interface | `SourceCompletion.lean` | IUT I, Definition 3.1(a)-(f) | 从任意 `InitialThetaArithmeticData` 产生该 package 的证明 | N/A：本批次尚未达到 3000 行验证门槛 |
| 2026-08-15 | arithmetic kernel：closure、places、K/F torsion transport | provedKernel | `SourceArithmeticPrelude.lean`, `SourceTorsionTransport.lean`, `SourcePlaceSelection.lean` | IUT I, Definition 3.1(a),(c),(e) | stable/reduction、orbicurve、Tate、local、cusp 来源仍缺 | 三文件逐一退出码 0、Lean 输出为空；`a2_source_axiom_audit.lean` 仅列 `propext`/`Classical.choice`/`Quot.sound`；custom axioms 0 |
| 2026-08-15 | `SourceCompletion → SourceNativeInitialThetaData` | proved | `SourceCompletion.lean` | IUT I, Definition 3.1(a)-(f) | 输入仍需显式完整 source witness；无 arithmetic universal constructor | 退出码 0、无 warning；`sourceCompletion_to_sourceNative` 与 `toSourceNativeInitialThetaData` 已定向审计 |
| 2026-08-15 | `SourceCompletionSignQuotient` 与 place selection 绑定 | proved | `SourceSignQuotientConstruction.lean` | IUT I, Definition 3.1(e)-(f) | 不构造 geometric core、坏约化或 cusp origin | 退出码 0、输出为空；同一 source core/section 的 dependent 字段逐字段传输 |
| 2026-08-15 | Clause A-C source-witness constructors | proved | `SourceClauseConstructors.lean` | IUT I, Definition 3.1(a)-(c) | reduction、Tate、rationality、large image、kernel descent 仍需来源证明 | 退出码 0、输出为空；`ofGoodOrMultiplicativeReduction`、`ofTateComparisonWitnesses`、`ofCanonicalRepresentation` 已编译 |
| 2026-08-15 | Clause D-F source-witness constructors | proved | `SourceClauseConstructors.lean`, `SourceTorsionRankOneQuotient.lean` | IUT I, Definition 3.1(d)-(f) | 完整 cartesian/local diagrams、K-rational quotient descent、cusp origin 仍未构造 | 退出码 0、输出为空；`ofFundamentalGroup`、`ofLocalFamilies`、`ofCanonicalBoundaryData` 已编译 |
| 2026-08-15 | 移除无关的 gate-consequence 投影路线 | removed | `Project.lean`; 删除 `SourceArithmeticGateConsequences.lean` | A2 scope restriction | 不影响 source contract 或 universal gate | 原文件只从已假设 gate 投影必要条件，当前不是 A2 构造；已移除导入和文件 |

后续新增记录必须明确：使用的是哪一个已证明声明、原文量词是否逐字保留、
对象是否由 source 数据实际构造，以及是否仍受 3000 行验证门槛约束。失败的
编译、warning 或公理审计只能追加为失败记录，不能把状态改成 `[x]`。

## 下一步唯一入口

当前只允许处理
`InitialThetaArithmeticData → SourceCompletion` 的缺失原文条件和真实构造。
在该 universal gate 关闭前，不进入 `SourceSignQuotientData` 或 Clause A-F 的
下一个独立证明，也不推进 `THEOREM311_TO_312_100_TASKS.md` 的第 3 项。

## 当前停止点

当前唯一与目标相关的状态是：source contract/conditional recognition 为
`interface`；arithmetic closure/places/torsion kernel 仅为可复用基础；独立的
source-witness assembly 和 Clause A--F bindings 不计入当前顺序前沿；
`InitialThetaArithmeticData → SourceCompletion` 以及
`InitialThetaArithmeticData → SourceNativeInitialThetaData` 的忠实完整构造仍为
`pending`。在真实几何、reduction、Tate、local diagram、kernel descent 和 cusp
origin 闭合前，不推进 A2 之后的论文命题。

## Append-only implementation note: K-side torsion boundary correction (2026-08-14)

本轮只修正当前 source-boundary 的扭点载体，不推进 universal gate 或下一条
独立 clause 证明。`TorsionRankOneQuotientData` 已泛化为接收实际的
`PuncturedEllipticCurve F`；`TorsionQuotientBoundaryOrigin` 的 quotient carrier
现在明确是
`(A.curve.baseChange A.K).LTorsion l`，因此不能再把 F-side
`A.curve.LTorsion l` 的 quotient 改名当作论文的 `E_K[l]`。

为保持 Clause (c) 的 F-side 表示和 Clause (f) 的 K-side quotient 同时忠实，
`SourceClauseC` 新增显式的 `k_torsion_basis`、
`k_to_f_torsion_transport` 及其兼容等式；`SourceClauseF` 只把 boundary
quotient basis 绑定到 `k_torsion_basis`，再由该 transport 得到 F-side basis。
这些字段仍是 source-supplied interface，尚无从 `InitialThetaArithmeticData`
构造的定理，也不声称已完成 K-rational descent 或 cusp origin。

本轮编辑尚未达到 3000 行实质编辑门槛，未执行编译、warning、`#print axioms`
或 `sorryAx`/custom-axiom 审计；证据仍为 `N/A`。状态保持：source contract /
conditional recognition 为 `interface`，arithmetic-to-source universal gate 为
`pending`。

## Append-only research note: no reusable K/F torsion transport (2026-08-14)

检索 `EllipticTorsion.lean` 及当前 IUT 地基后，没有发现可直接复用的
`(A.curve.baseChange A.K).LTorsion l` 与 `A.curve.LTorsion l` 的线性等价、
`E_K[l]` 的 K-rational descent，或把两种代数闭包点集识别的定理。现有结果只
构造各自曲线在各自代数闭包上的扭点、Galois action、连续表示和 kernel field。
因此 `SourceClauseC.k_to_f_torsion_transport` 必须继续作为原文来源明确的
source dependency；不得用任意 algebraic-closure equivalence、
`Classical.choice` 或同名 carrier 伪造该依赖。

该检索不改变状态，也未触发 3000 行门槛内的编译或审计。

## Append-only source-text cross-check: Definition 3.1 clauses (2026-08-14)

重新核对 IUT I Definition 3.1(a)-(f), pp. 61-64 后，当前 contract 的量词边界
保持如下：Clause (a) 的 stable-reduction binder 是全部 `V(F)^non`；Clause (b)
的坏处条件来自 `V_mod^bad` 上方的 F-places；Clause (c) 的表示先作用于
`E_F[l]`，其 kernel 才定义 `K`；Clause (d) 才转入 `X_K/C_K` 的有限-etale
覆盖与 quotient；Clause (e) 对每个 selected finite/infinite place 要求独立
completion-level diagrams；Clause (f) 的 `epsilon` 必须来自同一 K-side
quotient 的非零类及 canonical generator up to sign。

因此当前新增的 K-side transport 只修正 carrier 方向，不能关闭 (d)-(f) 的
cartesian/open-subgroup/local-model/cusp-origin 构造缺口。该核对没有改变任何
状态，也没有使用简化对象或额外数学命题。

## Append-only construction note: algebraic-closure K/F torsion transport (2026-08-14)

针对前一条检索记录中“没有可直接复用的 K/F torsion transport”，本轮新增
`SourceTorsionTransport.lean`，从现有 Mathlib 地基实际构造该依赖：

- `initialTheta_finite_extension_is_algebraic` 使用 `A.finiteFK` 给出
  `Algebra.IsAlgebraic A.F A.K`；
- `initialThetaClosureAlgEquiv` 使用 `IsAlgClosure.equivOfAlgebraic` 构造真实的
  `AlgebraicClosure A.K ≃ₐ[A.F] AlgebraicClosure A.F`，并保留其 `commutes`、单射、
  满射和逆映射定理；
- `baseChange_algebraicClosure_projective_curve_eq` 以 projective Weierstrass
  `map_baseChange` 和 `IsScalarTower.toAlgHom` 证明先经 `K` 再经
  `AlgebraicClosure K` 与直接从 `F` base change 的曲线相等；
- `algebraicClosurePointAddEquiv` 通过真实 affine/projective 点群映射构造闭包点的
  `AddEquiv`；`AddEquiv.mapTorsionBy` 和
  `AddEquiv.mapTorsionByLinear` 将其限制到实际 `AddSubgroup.torsionBy`，再给出
  `ZMod l`-线性等价；
- `initialThetaKToFTorsionTransport` 的 domain 明确是
  `(A.curve.baseChange A.K).LTorsion l`，codomain 明确是 `A.curve.LTorsion l`。

`SourceClauseC` 现在只保留原文所需的 F-side torsion basis；其 K-side basis 定义为
该 basis 经上述 transport 的逆映射，transport 与 basis-compatibility theorem 均为
构造性定义/证明，不再是无来源的 source field。该改动不声称 `K`-rational descent、
大像、kernel-field identification、cusp origin 或 Clause (f) 已完成。

本记录目前没有编译证据：新增代码尚未达到本轮统一验证的 3000 行实质编辑门槛，
所以状态仍只能是 `interface`/未验证实现，不得写成 `[x] proved`。下一次关闭登记
必须同时给出单文件编译、全项目零 warning 与公理审计结果。

## Append-only verification note: source assembly batch (2026-08-14)

本批次已达到项目约定的 1000 行实质代码验证门槛。以下命令均以退出码 0
完成，并显式写出对应 `.olean`；Lean 输出无 warning：

- `lake env lean LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean -o .lake/build/lib/lean/LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.olean`
- `lake env lean LeanFormal/IUT/IUTI/InitialTheta/SourceCompletion.lean -o .lake/build/lib/lean/LeanFormal/IUT/IUTI/InitialTheta/SourceCompletion.olean`
- `lake env lean LeanFormal/IUT/IUTI/InitialTheta/SourceTorsionTransport.lean -o .lake/build/lib/lean/LeanFormal/IUT/IUTI/InitialTheta/SourceTorsionTransport.olean`
- `lake env lean LeanFormal/IUT/IUTI/InitialTheta/SourcePlaceSelection.lean -o .lake/build/lib/lean/LeanFormal/IUT/IUTI/InitialTheta/SourcePlaceSelection.olean`
- `lake env lean LeanFormal/IUT/IUTI/InitialTheta/SourceTorsionRankOneQuotient.lean -o .lake/build/lib/lean/LeanFormal/IUT/IUTI/InitialTheta/SourceTorsionRankOneQuotient.olean`

定向 `#print axioms` 检查覆盖 `sourceNativeInitialThetaData_predicate`、
`SourceCompletion.toSourceNativeInitialThetaData`、
`sourceCompletion_to_sourceNative`、`SourceNativeArithmeticToSourceGate`、
K/F 扭点 transport 和 rank-one quotient 的非零类。输出只含 Lean/Mathlib
标准基础边界 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx`；
`check_no_custom_axioms.ps1 -SourceRoot LeanFormal/IUT/IUTI/InitialTheta`
返回 `customAxiomDeclarations: 0`。

这组证据把 `SourceCompletion → SourceNativeInitialThetaData` 的逐字段组装
记录为 `proved`（结构性蕴含）；它不改变 package 本身的 `interface` 状态，
因为 package 仍要求 source-supplied 的几何、群、局部和 cusp 字段。全称门
`∀ A, ∃ T, T.arithmetic = A` 仍为 `pending`。尝试编译总入口
`LeanFormal/IUT/Project.lean` 时被既有缓存缺失
`.lake/build/lib/lean/LeanFormal/IUT/Foundations/Arithmetic/Radical.olean`
阻断；这不是本批次 A2 声明的错误，故不能据此声称全项目零 warning。

## Append-only arithmetic prelude construction (2026-08-14)

针对“没有可复用基础就停下”的问题，本轮实际新增
`LeanFormal/IUT/IUTI/InitialTheta/SourceArithmeticPrelude.lean`。它从任意
`InitialThetaArithmeticData A` 直接构造且只构造以下有来源对象：

- `SourceFbarExtension.canonical A`，其 carrier 是实际
  `AlgebraicClosure A.F`，比较映射是 `AlgEquiv.refl`；
- `NumberFieldPlace.restrictionSection` 及其 selected-place 集合、selected-place
  等价、comap 左逆和有限/无限处的覆盖与不交；
- `PuncturedEllipticCurve.initialThetaKToFTorsionTransport A`，其 domain/codomain
  分别是实际 K-side/F-side `LTorsion`，并保留双射证明。

`SourceCompletion` 新增 `arithmeticPrelude` 字段，`ofSourceNative` 使用
`SourceArithmeticPrelude.fromPlaceSection` 复用同一 source `V_section`，并保留
section 等式。该字段只是共享 arithmetic 基础；它没有构造坏处集合、
稳定约化、Tate 比较、orbicurve、finite-etale 群、大像、局部模型或 cusp，故
`SourceCompletion → SourceNativeInitialThetaData` 的 source assembly 仍不等于
`InitialThetaArithmeticData → SourceCompletion` 的 universal gate。

本轮新增代码尚未达到 3000 行实质编辑门槛，尚未执行编译、warning、
`#print axioms` 或 custom-axiom 审计；状态记录为 `interface`/待验证，
universal gate 继续为 `pending`。后续 clause 只能复用这些明确命名的真实
对象，不能再重复定义或把它们误当作原文六条 clause 的存在证明。

## Append-only verification note: arithmetic prelude and source package (2026-08-14)

本批次在累计实质编辑超过 3000 行后，实际编译并通过且无 Lean warning 的
A2 文件为：`SourceTorsionTransport.lean`、`SourcePlaceSelection.lean`、
`SourceDefinition31Quantifiers.lean`、`SourceArithmeticPrelude.lean`、
`SourceCompletion.lean`、`SourceTorsionRankOneQuotient.lean`。

新增的 prelude 投影包括实际 `AlgebraicClosure` 比较、restriction section 的
selected finite/infinite 处分解与 comap 左逆，以及 K/F `LTorsion` transport
的双射和逆映射。`SourceCompletion` 还证明其 source selected-place 集与该
prelude 的 selected 集相等，并由等式传输得到同一 selected-place 等价。
这些结果的输入仍是显式 `SourceCompletion`/source witness；它们没有构造
`SourceCompletionSignQuotient`、Clause A--F 的缺失来源字段，也没有关闭
`InitialThetaArithmeticData → SourceCompletion` 全称门。公理审计尚未在本批次
完成，因此状态继续保持 `interface`/`pending`，不能勾选 `[x]`。

## Append-only audit note: A2 batch trust boundary (2026-08-14)

定向 `#print axioms` 覆盖了
`sourceNativeInitialThetaData_predicate`、
`SourceCompletion.toSourceNativeInitialThetaData`、
`sourceCompletion_to_sourceNative`、
`SourceNativeArithmeticToSourceGate`、arithmetic prelude 的 canonical/from-place
构造、K/F torsion transport，以及 rank-one quotient 的非零类结论。输出仅含
`propext`、`Classical.choice`、`Quot.sound`；未出现 `sorryAx`。对
`LeanFormal/IUT/IUTI/InitialTheta` 执行 `check_no_custom_axioms.ps1` 返回
`customAxiomDeclarations: 0`。

尝试编译 `LeanFormal/IUT/Project.lean` 时，在先生成缺失的
`Radical.olean` 后仍被既有非 A2 缓存缺失
`Foundations/Arithmetic/PadicValuation.olean` 阻断；因此不能把总入口声明为
全项目验证通过。A2 目标文件本批次均已单文件无 warning 通过，但 universal
gate 仍为 `pending`，source package 仍为 `interface`。

## Append-only status closure: arithmetic public primitives (2026-08-14)

以下三项已由 arithmetic record 实际构造并有本批次编译/审计证据，状态收口为
`provedKernel`；它们不是 Clause A-F 的 source realization：

- `[x]` `SourceFbarExtension.canonical`：实际 `AlgebraicClosure A.F` carrier；
- `[x]` `NumberFieldPlace.restrictionSection`：selected-place equivalence、
  finite/infinite partition 与 comap 左逆；
- `[x]` `initialThetaKToFTorsionTransport`：实际 K-side/F-side `LTorsion` 的
  `ZMod l`-linear equivalence 与双射性。

其余 `SourceCompletionSignQuotient` 几何/群/cusp 字段和 Clause A-F 的原文
条件仍未由 arithmetic record 推出；不因上述三项关闭而改变 `interface` 或
universal `pending` 状态。

## Append-only construction note: singleton odd-place selection (2026-08-14)

`SourcePlaceSelection.singleton A p hodd` 现在从一个明确给出的有限处 `p` 及其
奇剩余特征证明，实际构造单点 `V_mod_bad = {p}`、非空性和 odd-characteristic
字段。该构造不添加坏约化、乘法约化或 Tate comparison；因此 Clause B 及
arithmetic-to-source universal gate 仍未关闭。

## Append-only carrier-binding note (2026-08-14)

`SourceArithmeticPrelude` 的 `fbar` 与 `torsionTransport` 已改为由 arithmetic
record 唯一决定的定义，不再是可任意填写的结构字段。`SourceCompletion` 新增
`source_fbar_to_arithmetic_prelude_fbar` 及其 commutation/bijectivity 定理，
把 source tuple 的 chosen closure 与 canonical prelude closure 通过真实
`AlgEquiv` 绑定；这消除了同名 carrier 未关联的结构性风险，仍不构造缺失的
orbicurve 或 Clause A-F 来源条件。

## Append-only final audit sample (2026-08-14)

新增的 chosen/canonical closure binding 也已纳入定向 `#print axioms`；输出仍
只有 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`，custom-axiom
扫描为 0。总入口的非 A2 缓存阻断记录保持不变。

## Append-only necessary-condition construction (2026-08-14)

针对“缺少可复用结论就应当实际构造”的要求，新增
`LeanFormal/IUT/IUTI/InitialTheta/SourceArithmeticGateConsequences.lean`。
该文件没有把缺失 source 对象塞进 `InitialThetaArithmeticData`，而是从一个
已经声称的
`SourceNativeArithmeticToSourceGate` 逐条构造必要条件的精确结论：

- `SourceCompletion` witness 与 native source witness 的 per-arithmetic
  等价，以及两种 universal gate 的等价；
- Clause A 的全部 `F`-finite-place stable-reduction 量词、field-of-moduli
  元素和 maximal-solvable containment；
- Clause B 的同一 `V_mod_bad` 非空/奇剩余特征、乘法约化、真实
  `SourceTateComparisonWitness` 和 residue-characteristic coprimality；
- Clause C 的 `Torsion23Rational`、rank-two basis、`SL₂` 大像和 kernel-field
  `AlgEquiv`；
- Clause D 的真实 K-side finite-etale cover 与 profinite group inclusion；
- Clause E 的每个 selected finite/infinite place 的独立 local source；
- Clause F 的同一 K-side `boundary_origin`、`epsilon` 相等和非零 quotient
  class。

每个结论都保留 `T.arithmetic = A` 和实际 native witness，不改变 source 量词，
也不把必要条件反向当作存在性。该层状态为 `interface`；本次编辑尚未达到
 3000 行验证门槛，因此编译、warning、`#print axioms` 和 custom-axiom 证据为
 `N/A`。universal gate 仍为 `pending`，而 `SourceCompletion → native` 的
 结构性组装仍为已证明的 source-witness implication。

## Append-only construction note: geometric core/place binding (2026-08-14)

新增 `LeanFormal/IUT/IUTI/InitialTheta/SourceSignQuotientConstruction.lean`。
`SourceSignQuotientGeometricCore` 将真实 source 的几何、sign quotient、
finite-etale 基本群、K-side scalar extension 和同一 `cK` 上的 boundary cusp
集中在一个 core 中；`SourcePlaceSelection` 唯一提供 `V_mod_bad`、odd residue
characteristic、非空性、canonical restriction section、selected `V`、place
equivalence 和 comap 左逆。`toSourceCompletionSignQuotient` 再逐字段构造
现有 `SourceCompletionSignQuotient`，因此同一输出中的 place 与 geometry 不再
可能来自两个未绑定的 source 记录。

该构造的输入仍是 source-supplied `SourceSignQuotientGeometricCore` 和
`SourcePlaceSelection`；它没有从 `InitialThetaArithmeticData` 生成几何 core，
也没有声称坏处上的 reduction/Tate 条件或 cusp origin 已由 arithmetic data
推出。新增文件当前未在本编辑批次编译，证据保持 `N/A`；universal gate
继续为 `pending`，构造层继续为 `interface`。

## Append-only place-level construction note (2026-08-14)

`SourcePlaceSelection` 新增 `selected_bad_place_mem`、
`selected_bad_place_is_finite`、`selected_bad_place_comap` 和
`V_bad_nonempty`。它们从同一个 `V_mod_bijection` 和 restriction section
构造坏模处的选定上方有限处，并证明其 `V_bad` 归属、有限性及 comap 恢复；
`V_bad` 非空由 `V_mod_bad.Nonempty` 实际推出。该层仍不证明曲线在这些处的
坏/乘法约化，也不产生 Tate comparison，因此 Clause B 与 universal gate 仍为
`pending`。本编辑批次未达到 3000 行验证阈值，机器证据为 `N/A`。

## Append-only staged clause-binding note (2026-08-14)

新增 `LeanFormal/IUT/IUTI/InitialTheta/SourceClauseConstructors.lean`，只收口
能够由已有 source 对象忠实传输的绑定：

- `SourceOrbicurveGroupData.ofFundamentalGroup` 从实际 etale fundamental group、
  projection 及其 surjectivity 构造 canonical kernel exact sequence；
- `SourceTateComparisonWitness.ofComparison` 和
  `SourceClauseB.ofTateComparisonWitnesses` 将同一个 q-parameter、真实
  `TateCurveComparison` 与独立的 order-coprimality 证明绑定；
- `SourceClauseC.ofCanonicalRepresentation` 把表示固定为实际
  `galoisLTorsionMatrixRepresentation`，不允许另选同名 representation；
- `SourceClauseE.ofLocalFamilies` 从同一 `S.V_section`/`S.V_mod_bijection`
  投影 selected-place 字段，仅保留独立 local source family；
- `SourceClauseF.ofCanonicalBoundaryData` 从 `D.k_torsion_basis` 实际构造
  rank-one quotient，再要求原文 cusp-origin map 和 decomposition witness。

这些构造没有从 `InitialThetaArithmeticData` 生成缺失的 reduction、orbicurve、
kernel-field descent、local diagrams 或 cusp origin；因此它们的状态为
`interface`，A2 universal gate 仍为 `pending`。本批次尚未达到 3000 行实质编辑
验证门槛，编译、warning、公理及 custom-axiom 证据保持 `N/A`。

## Append-only staged clause-binding verification (2026-08-15)

修正 `SourceClauseConstructors.lean` 的依赖索引和 Lean sort 错误后，运行：

`lake env lean LeanFormal/IUT/IUTI/InitialTheta/SourceClauseConstructors.lean -o .lake/build/lib/lean/LeanFormal/IUT/IUTI/InitialTheta/SourceClauseConstructors.olean`

退出码为 `0`，Lean 输出为空，因此该文件的单文件编译与 warning 检查通过。
修正内容保持原文来源边界：stable/multiplicative reduction 的投影只返回实际
`HasStableReductionAt`/`HasMultiplicativeReductionAt` 命题；Tate 字段使用
`Nonempty (SourceTateComparisonWitness A p)`；Clause (c) 的表示固定为实际
`galoisLTorsionMatrixRepresentation`；Clause (d)-(f) 的 dependent indices
显式绑定。此证据只关闭这些 source-witness binding 的实现验证，不构造
`InitialThetaArithmeticData → SourceCompletion`，universal gate 继续为
`pending`。本批次尚未运行公理/custom-axiom 审计，故审计证据保持 `N/A`。

## Append-only checklist correction and verification (2026-08-15)

前一版曾把若干独立 source-witness assembly/Clause binding 标成 `[x]`。这在本目标
的顺序要求下是不正确的：它们位于 `InitialThetaArithmeticData → SourceCompletion`
之后，不能作为 A2 的完成证据。现将活动清单中的这些条目改为 `[~]` 或 `[r]`，并
明确不计入当前前沿；历史登记行保留以便追溯，但由本纠正记录覆盖其“完成”含义。
当前目标没有任何 `[x]` 完成标记。

修复 `SourcePlaceSelection.selected_bad_place_mem` 的等式传输后，以下文件按单文件、
一次一个进程编译，均退出码 `0` 且 Lean 输出为空：
`SourcePlaceSelection.lean`、`SourceTorsionTransport.lean`、
`SourceArithmeticPrelude.lean`、`SourceDefinition31Quantifiers.lean`、
`SourceCompletion.lean`、`SourceSignQuotientConstruction.lean`、
`SourceClauseConstructors.lean`、`SourceTorsionRankOneQuotient.lean`。
`verification/a2_source_axiom_audit.lean` 的定向 `#print axioms` 仅报告
`propext`、`Classical.choice`、`Quot.sound`；
`tools/check_no_custom_axioms.ps1 -SourceRoot LeanFormal/IUT/IUTI/InitialTheta`
报告 `customAxiomDeclarations: 0`。本记录不把这些标准基础边界改写成非标准公理，
也不把全项目总入口的既有缓存阻断当作 A2 成功证据。

按 A2 范围移除了只从已假设 universal gate 投影必要条件的
`SourceArithmeticGateConsequences.lean` 及其 `Project.lean` 导入；该路线不是
arithmetic-to-source 构造，不能作为清单项目。
