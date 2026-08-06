# IUT 子目标登记

这份登记把“可以独立发布的 Lean 结果”和“尚未解决的数学问题”分开。
一个抽象接口定理或带 `sorry` 的条件推论不计为猜想的证明。

## 1. 当前可以独立交付的内核

这些结果已经在当前 Mathlib/Lean 版本中编译，并且没有自定义 `axiom` 或生产路径中的新增 `sorryAx`：

| 模块 | 数学范围 | 结论 |
|---|---|---|
| `Foundations/Theta/GaussianSquareSum` | 有限高斯平方和、奇数标签的 `l(l+1)/12` 归一化 | 已证；尚未赋予 IUT 的几何解释 |
| `IUTII/Frobenioid/PrimeStripArithmetic` | 普通素数索引的有限性和区间单调性 | 已证；不是 Frobenioid 的存在定理 |
| `IUTII/Frobenioid/PrimeStripDegree` | 有限值幺半群上的 `MonoidHom` 度数和乘法/总度数律 | 已证；尚未构造论文中的 etale prime-strip |
| `IUTI/HodgeTheater/PrimeStripCore` | D/F prime-strip 的群、核、作用和遗忘映射 | 已证的代数内核；算术几何实现仍待构造 |
| `Theorem311/Indeterminacy/OrbitTransport`、`UpperSemi` | 商轨道传递和上半连续对应的逻辑 | 已证的通用内核；不是 IUT 的 Galois/Kummer 结论 |

本轮底层审计还固定了以下可独立复用的模块：

| 模块 | 数学范围 | 当前边界 |
|---|---|---|
| `Foundations/Arithmetic/Radical`、`PrimitiveAdditive` | 自然数 radical、互素乘法、primitive additive triple 及 radical 分解 | 标准唯一分解算术已证；没有 ABC 常数或估计 |
| `Foundations/Arithmetic/PrimeIntervals`、`PrimeLabels` | 有限素数区间和奇素数标签 | 有限性、素性投影、奇性已证；不是 IUT prime-strip 存在性 |
| `Foundations/Geometry/WeierstrassModel`、`PuncturedEllipticCurve` | Mathlib Weierstrass 曲线、给定 `j` 不变量和去一点 carrier | 具体代数模型已证；不含数域上的 IUT 初始数据/一般位置构造 |
| `Foundations/LinearAlgebra/FiniteDeterminant` | 对角 determinant、tensor product normalization、rescaling 和有限 log-volume | 纯有限线性代数已证；不含 holomorphic hull 或 q-pilot 识别 |
| `Foundations/Arithmetic/NormLog` | 任意 `NormedField` 的单位范数、`Real.log` 与 `Multiplicative ℝ` 的 `MonoidHom` | 范数乘法和 log 加法已证；p-adic/Frobenioid 解释仍在上层 |
| `Foundations/Arithmetic/PadicValuation` | 自然数素数赋值、乘法/幂律和素数幂整除刻画 | Mathlib `padicValNat` 基础已证；不含局部域或高度估计 |
| `Foundations/NumberField/FinitePlaces` | 数域有限处、整数环高度一素理想、有限剩余域、素数剩余特征和处的 restriction | carrier、剩余特征素性、塔式传递性及 lying-over 满射性已证；不含椭圆约化或坏处选择 |
| `Foundations/NumberField/FinitePlaceExtension` | 上下方有限处的 ramification 公式与局部完备化映射 | 上方理想 lying-over、`k_v -> K_w` 的连续单射性、全体完备化元素上的 `v(x)^e = w(f(x))`、completed valuation-ring 局部单射环同态及剩余域单射已证；Tate 参数传递未证 |
| `Foundations/NumberField/Places` | 有限/无限处、restriction、place section 及其选定像 | 两类 place 及 restriction 传递性已证；非规范 section 由上下方处存在性构造，选定像与全部下层 places 等价；`V_mod^bad` 及约化条件未构造 |
| `Foundations/Geometry/LocalReduction` | 实际有限处完备化上的 good、multiplicative、split multiplicative、stable reduction 谓词 | 坐标表示和最小模型选择不变性及 split→multiplicative 已证；指定 IUT 输入曲线的约化存在性与 Tate 参数未证 |
| `Foundations/Geometry/ReductionBaseChange` | integral/minimal Weierstrass model、reduction 和三类约化沿有限处扩张的基变 | 判别式单位与 `c4` 单位的最小性判据、good/multiplicative 保持、剩余域上切锥多项式 splitting 及 split multiplicative 保持均已证；结论以真实下层约化假设为前提，不制造输入曲线的约化性质 |
| `Foundations/NumberField/LocalQParameter` | 实际有限处完备化中的非零 `q` 候选、离散阶和正整数幂 | DVR 不可约元给出候选、正阶及幂封闭性已证；尚未证明该候选 uniformize 指定椭圆曲线，不能称为曲线的 Tate 参数 |
| `Foundations/Geometry/EllipticTorsion` | `E[l]`、绝对 Galois 作用、连续矩阵表示和核固定域 | 点作用/开放稳定子已证；给定真实二维基时，连续表示及有限 Galois 核域已证；二维基存在性、6-torsion 有理性与像包含 `SL₂` 未证 |
| `IUTII/Kummer/KummerPolynomial`、`RootRealization`、`CompatibleRoots`、`NatRootSystem`、`KummerClass`、`KummerRootRatio`、`VerticalLogKummer` | 多项式根、兼容根链、单位值 Kummer class、根比与上半连续 log 对应内核 | 低层 carrier 与代数律已证；etale/Frobenioid/论文中的垂直对应仍是待构造义务 |
| `IUTII/Frobenioid/ConcreteLocalKummerExample` | 将实际局部 `q=p` 放入积分闭包群化并构造一致有理根系统 | 非平凡局部 Kummer carrier 已证；尚未证明 etale/Frobenioid theta-link 识别 |
| `Foundations/Geometry/TateDeckAction` | 代数闭包单位上的 base-field Galois 作用、`q^Z` deck 子群和商群作用 | 单位、子群保持和商群乘法等价已证；Tate uniformization 与曲线点识别仍未证 |
| `IUTII/Kummer/ConcreteEtaleKummerBridge` | 有限 `Z/lZ` Tate 方向核与实际 `q=p` 兼容根系统的整数桥 | 零标签的 `l`-倍根指数和标签一根已证；几何 etale/Frobenioid theta-link 仍未证 |
| `IUTI/HodgeTheater/ConcreteIntegralHodgeTheaterExample` | 将 Q(i) arithmetic、有限素点区间、实际 integral F-prime-strip、三层 carrier 与 q=5 Kummer realization 组装 | 一个具体有限 carrier/test input 已证；不等同论文的历史、theta-link 或 etale Hodge theater |

基础基线在 `60/60` 串行构建中逐文件通过；随后新增的 p-adic valuation
模块单独通过并进入生产聚合，数域 place 批次又在 `3/3` 定向串行中通过。
局部约化模块及其数域依赖链随后在 `4/4` 定向串行中通过，生产聚合为
`3649 jobs`；有限处 q 候选加入后又在 `5/5` 定向串行中通过，最新生产
聚合为 `3650 jobs`；椭圆扭点/Galois 批次在 `4/4` 定向串行中通过；有限处
完备化扩张批次又在 `6/6` 定向串行中通过；三类约化基变加入后在 `7/7`
定向串行中通过，当前生产构建为 `3655 jobs`。
各批次的精确聚合和公理证据见 `AUDIT_LEDGER.md`。这些模块应先于任何
source-faithful Ind1/Ind2/Ind3、IPL、SHE、APT 实现，且不能被上层接口字段
当作已经完成的几何对象。

数域 place 批次的下一真实依赖不是 Theorem 3.11，而是：从同一条椭圆
曲线证明所需 place 上的 stable/split multiplicative reduction。沿已构造的
`k_v -> K_w`、valuation-ring local map 和剩余域嵌入保持 good、multiplicative、
split multiplicative reduction 已完成；下一步是把已经构造的局部 q 候选与相应曲线的 Tate
uniformization 真实联系起来，并证明参数阶/局部高度性质；最后才能从同一曲线
和已证的 place section 定义原文的非空 `V_mod^bad` 及其 bad/good 补集，并加入
Initial Theta data。当前代码已经完成 selected place 的 section/像集形状、
局部约化谓词、坐标不变性、有限处完备化、valuation-ring/剩余域单射及三类
约化的条件式基变、纯 DVR 的
q 候选和条件式的实际 Galois 表示/核域；
仍须证明 `E[l]` 的二维基、6-torsion 有理性和大像条件。没有把这些尚未证明的
曲线联系或源假设伪装成任意布尔标签或结构字段。

这些是可审计的阶段性成果，但它们本身不是“尚未解决的猜想”。

### 最新底层批次（2026-08-06）

本轮按约一千行有效代码作为一个批次，先完成了 C 层上方所依赖的局部
Tate/Kummer 代数地基：

| 模块 | 已真正证明的内容 | 明确未证明的内容 |
|---|---|---|
| `Foundations/Geometry/ConcreteTateParameter` | `q=p` in `Q_p`、严格收缩、q-series 收敛、q-unit 非平凡性及幂收缩 | 不等同指定数域椭圆曲线的 Tate 参数 |
| `Foundations/Geometry/ConcreteTateKummerPacket` | 实际积分载体、兼容根系统、整数根加法/zsmul、有限 reduction kernel | etale/Frobenioid/Kummer 几何识别 |
| `Foundations/Geometry/ConcreteTateFiniteLevel` | 实际 kernel 商与 `ZMod l` 的加法等价、代表元与倍数类律 | etale cover 或基本群解释 |
| `Foundations/Geometry/ConcreteTateDeckQuotient` | `q^Z` deck 子群、局部绝对 Galois 保持性、商作用的恒等/复合 | 曲线点 uniformization 和 Galois-equivariant 点识别 |
| `Foundations/Geometry/ConcreteTateLocalCarrier` | 上述五个底层对象的依赖组装和投影定理 | stable reduction、source Hodge theater、theta/log-link |
| `Foundations/Geometry/TateCurveArithmetic` | canonical q-series 的 `b₂,b₄,b₆,b₈,c₄,c₆,Δ` 精确公式、变量变换权、非退化/椭圆性判据，以及带显式 integral/minimal witness 的 good/multiplicative reduction 传输 | `q=p` 的判别式非零、指定输入曲线的实际证书、Tate uniformization、点的 Galois 等变性 |
| `Foundations/Geometry/TateCurvePadicEstimates` | 对实际 `q=p ∈ Q_p` 证明 Lambert 级数项的几何范数界、有限截断误差、首项严格支配尾项；证明 canonical `a₄/a₆/c₄` 非零，`c₄` 为单位，并构造 `PadicInt` 积分系数/分母/有限 packet 证书 | 输入曲线识别、stable/split multiplicative reduction 存在性、Tate uniformization、Galois-equivariant 点识别、source-faithful theta/log-link |
| `Foundations/Geometry/TateCurveDiscriminantEstimates` | 将 canonical `Δ` 分解为 `-a₆` 与四项修正，逐项证明严格小范数并聚合为 `||Δ|| = ||q||`；真实证明 canonical q-series 曲线判别式非零、椭圆性、积分 discriminant 见证、余域零像及积分 `c₄` 单位，并提供可复用严格支配/输出包 | 不识别单独给定的数域椭圆曲线；不证明该输入曲线在选定处 stable/split multiplicative reduction、Tate uniformization、点级 Galois 等变性或 source-faithful theta/log-link |

本批次 `lake build` 为 `3850/3850` 且零 warning；唯一允许的生产
`sorryAx` 仍为 `theorem311_produces_stepXI_contract`。因此 C 层仍不能标记为
完成，下一批必须先处理指定输入曲线在选定处的真实 stable/split
multiplicative reduction，以及 q-series 曲线与该输入曲线之间的真实
Tate uniformization；不能用本批次的 carrier 代替这些定理。

随后完成的 995 行 `TateCurveArithmetic` 批次已在 `3851/3851` 生产构建中
通过且零 warning。它闭合的是 canonical 方程的算术和证书传输层，不是
q-series 椭圆性或 Tate uniformization 的存在性；因此 C 层的 source-faithful
几何部分仍保持未完成状态。

本轮完成的 `TateCurvePadicEstimates` 是上述算术层之后的约 2,400 行有效
底层估计代码。独立编译日志 `logs/lean/tate-padic-estimates-batch-20260806-r11.log`
为零错误、零 warning；接入 `LeanFormal.IUT.Project` 后生产构建日志
`logs/lean/tate-padic-estimates-project-20260806-r4.log` 以 `3850/3850`
通过且零 warning。关键端点的 `#print axioms` 结果记录在
`logs/lean/tate-padic-estimates-axiom-audit-r2-20260806.log`，只出现
`propext`、`Classical.choice`、`Quot.sound`；生产源码自定义
`axiom/opaque` 扫描为零，见
`logs/lean/tate-padic-estimates-custom-axiom-scan-20260806.log`。
这批次把 q-series 的 p-adic估计和积分载体真正闭合，但没有把
“`c₄` 为单位”误报成“判别式非零”，因此 C 层仍不能标记为完成。

随后完成的 `TateCurveDiscriminantEstimates` 是约 1,000 行的判别式闭合
批次。它在同一 `q=p ∈ Q_p` 载体上真实证明四项修正均严格小于 `a₆`，从而
证明 canonical `Δ ≠ 0`、`||Δ|| = ||q||` 和 canonical q-series 曲线的
椭圆性；同时把 discriminant 传到 `PadicInt` 积分 Weierstrass 模型，证明
其余域像为零、generic-fiber 像非零且 `c₄` 为单位。独立编译日志为
`logs/lean/tate-curve-discriminant-batch-20260806-r12.log`，Project 日志为
`logs/lean/tate-curve-discriminant-project-20260806-r2.log`，全量构建为
`logs/lean/tate-curve-discriminant-full-20260806.log`（`3853/3853`，零 warning）。
新模块无 `sorry/axiom/opaque`；端点公理审计为
`logs/lean/tate-curve-discriminant-axiom-audit-r2-20260806.log`，只含
Lean/Mathlib 标准基础公理。这个闭合的是 canonical q-series 的椭圆性，
不是指定数域输入曲线的识别、约化存在性或 Tate uniformization，因此 C 层
仍不能整体标记为完成。

## 2. 最有价值的 IUT 内部发布目标

下面的目标比直接声称 ABC 更小，而且能直接检验论文中的关键步骤：

1. **Source-faithful Step-XI target**：给出一个明确的数域、椭圆曲线、prime-strip 和三层 indeterminacy 数据，构造实际的 Ind1/Ind2/Ind3、IPL、SHE、APT、holomorphic hull、determinant/tensor normalization 和 log-volume 比较，并无 `sorry` 地生成 `FiniteStepXILinkEvidence`。
2. **One-family Corollary 3.12**：在上述同一族、同一组源数据上证明 Theorem 3.11 输出足以满足 Step-XI 合同。这个结果仍是 IUT 内部结果，不应表述为全局 ABC。
3. **Negative/independence check**：若无法构造源数据，则在 Lean 中给出反模型或缺失假设证明，说明当前抽象假设不足以推出 Corollary 3.12。这同样是有价值的数学结果，因为它能定位论文推导中的缺口。

这三个目标的验收条件是：源数据不是任意空记录；生产路径没有自定义公理；`#print axioms` 只出现 Lean/Mathlib 的标准基础（当前审计中的 `propext`、`Classical.choice`、`Quot.sound`）；每个定义和证明都带原文页码和依赖台账。

## 3. 外部开放猜想候选

这些问题在公开资料中仍被当作开放问题，但当前代码**尚未**能推出其中任何一个。是否采用某一项，必须先固定精确定义，再单独做文献核查。

| 候选 | 为什么与 IUT 相邻 | 风险/优先级 |
|---|---|---|
| **Hall 型不良逼近（椭圆曲线/Mordell 方程）** | 直接涉及 `x^2-y^3` 的小差、椭圆曲线高度和积分点；可作为一族明确的 height/radical 目标 | 开放但有很多变体；先选一个非平凡、未被现有定理覆盖的固定表述。优先级：中 |
| **受限 Szpiro 不等式** | 与 IUT 的椭圆曲线判别式、导子、Arakelov 高度最接近；全局版本是 ABC 的近邻 | 不能把“固定曲线”或有界坏素数的平凡情形算作猜想；必须选择仍未解决的、明确变化的半稳定族。优先级：中低 |
| **固定签名的 Fermat–Catalan 有限性** | ABC 型高度-根式估计的直接下游 | 不同签名的状态不同，若签名已有结果就没有研究价值；必须逐签名核查。优先级：低 |
| **选定曲线族上的有效积分点/弱 Vojta 不等式** | 可把 holomorphic-hull 和 log-volume 目标转成高度上界 | 不是单一标准猜想，需先写出精确族和常数依赖；优先级：中低 |

Hall 猜想的标准问题背景是 Mordell 方程中的平方与立方差；Szpiro 猜想则把椭圆曲线的判别式与导子联系起来。公开资料仍将 ABC、Hall 和 Szpiro 视为开放方向；这并不表示 IUT 的部分接口已经证明了它们。

## 4. 不应作为“新猜想成果”的目标

- Mason–Stothers（多项式 ABC）、费马大定理、Faltings/Mordell 的非有效有限性等已经有独立证明；形式化它们有价值，但不能冒充 IUT 的新开放结果。
- 只在有限枚举、固定有界参数或空类型上成立的命题，不计为受限猜想。
- 仅把 `Prop` 塞进结构、给出 `sorry`、或把外部猜想当作字段输入，都是接口完成，不是证明。

## 5. 推荐顺序

`M0`（审计和资料库）→ `M1`（具体 Initial Theta/数域/椭圆曲线）→ `M2`（真实 Ind1/2/3）→ `M3`（一个源忠实的 Step-XI 证书）→ `M4`（明确曲线族的受限 Hall/Szpiro/高度结果）→ `M5`（全局 Corollary 3.12 和 ABC）。

只有 `M3` 无 `sorry` 且通过公理审计后，才值得把 `M4` 作为“由 IUT 产生的开放猜想结果”来宣称；在此之前，外部候选都只是研究计划。
