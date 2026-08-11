# IUT III Theorem 3.11 前置依赖链审计

审计日期：2026-08-08  
工作树提交：`daa99d72` (`master`)  
Lean：`v4.32.2`（见 `lean-toolchain`）  
Mathlib：`v4.32.2`（见 `lake-manifest.json`）

`lake-manifest.json` 的 mathlib resolved revision 为
`905b95818eb32af7874a58b427f50c1711a5e96c`；当前锁定的辅助包 revisions 为
`plausible=e12c1910`、`LeanSearchClient=c5d5b8f`、`importGraph=7e9612b`、
`proofwidgets=6e311e2`、`aesop=a7dbf0c`、`Qq=38d591e`、
`batteries=023ce7d`、`Cli=88679d`。这些版本只提供 Lean/Mathlib 基础，
不包含 IUT-specific theorem。

## 结论摘要

结论是否定的：当前工作树没有按照 Mochizuki IUT I--IV 原文的对象、假设、
存在性和兼容性，完整证明 IUT III Theorem 3.11。更精确地说，搜索在以下
源命题处遇到未闭合的前置构造：

1. IUT I Definition 3.1 的任意初始 Theta-data 的构造，以及其稳定约化、坏处、
   局部基本群、扭点/大像、截面和 cusp 条件；当前已完成对已携带全部条件的
   source 对象的全称识别，但尚未从任意 arithmetic input 构造这样的对象；
2. 由这些数据构造的、相互 distinct 的 Theta+-ell-NF Hodge theaters、
   LGP-Gaussian log-theta-lattice 及 D-Theta+-bridge；
3. IUT II 的真实 vertical log-Kummer correspondence、Frobenioid/prime-strip
   数据及其与局部整数、全局 realified 数据的兼容；
4. IUT III Theorem 1.5、Propositions 2.1、3.2、3.4、3.5、3.7、3.9、3.10
   所需的 source-facing 构造，以及 Theorem 3.11(iii) 的横向 LGP-link/evaluation
   兼容。

仓库中确实有大量 Lean 已证明的普通代数、序、商、有限矩阵/对数体积、数域
处和局部曲线算术，也有一个明确标注为测试载体的 `Q(i)`-at-5 有限模型。这些
结果的陈述和证明本身可以复用；但它们没有证明原文要求的任意初始数据、任意
procession、真实 Hodge theater 或真实 log-Kummer/Frobenioid 识别。因此不能
把它们升级为 Theorem 3.11 的 source-faithful 证明。

用户允许替代证明路线，但本审计采用“实质一致”门槛：替代路线必须证明同一
载体（或给出已证明的载体等价/实现桥）、同一量词和假设、同一映射方向及同一
兼容性结论。仅仅把命题放进结构字段、使用较小的有限模型、或证明同名的
抽象序/商引理，不满足该门槛。

## 1. 审计规则和证据

### 1.1 通过条件

一个源命题只有同时满足以下条件，才记为 `source-faithful proved`：

* 原文对象、假设、量词和结论都出现在 Lean 类型中；
* 若使用不同载体，存在已证明的等价、实现或自然性桥，而不是标签或注释；
* 目标构造由低层对象实际构造，不能只从 record/certificate 字段投影；
* 当前 Lean/Mathlib 工具链编译通过，且 `#print axioms` 的结果已记录；
* “upper-semi” 的包含/满射方向与原文一致，不能误写成 equality。

状态含义：

| 状态 | 含义 |
|---|---|
| `proved` | 该声明本身由 Lean 检查，且没有隐藏 source-specific premise； |
| `interface` | 类型和下游定理已检查，但关键数学对象由字段/前提提供； |
| `pending` | 尚未构造或明确登记为待办； |
| `test carrier` | 一个具体、有限或特例实例；不能代表原文任意输入； |
| `historical evidence` | 旧日志/旧台账，仅作为线索，不能替代当前 HEAD 复核。 |

### 1.2 原文证据

原始 PDF 和提取方法已经在 `papers/motizuki_corpus/SOURCE_TEXT_AUDIT.md`
固定。主要证据如下：

* IUT III 原文 SHA-256：
  `9A7EE3C77B1C7717210C0613EB39B6844649D0040DC3D9E1BE7D544F8F91A0B9`；
* IUT III Theorem 3.11 连续文本：
  `papers/motizuki_corpus/text/Inter-universal Teichmuller Theory III.txt`
  行 9151--9618，物理页 153--159；
* 页面化、逐页的工作文本：
  `papers/motizuki_corpus/text/source_audit/IUTIII_Theorem311_through_Corollary312_pp153-186.plain.txt`
  和同名 `.layout.txt`；
* IUT III Corollary 3.12 Step (xi) 的物理页 181--185 也在上述 153--186
  提取中；
* IUT I Definition 3.1：IUT I 连续文本行 3123--3280；Definition 5.2：
  行 7702--7775；Proposition 6.9/Corollary 6.10：行 9811--9995；
* IUT II Corollaries 4.6、4.7、4.8、Definition 4.9、Corollaries 4.10、
  4.11：分别为 IUT II 连续文本行 8831--9065、9111--9294、9707--9916、
  10035--10155、10313--10601、10717--10767。

PDF 提取文本只作定位索引；公式方向发生冲突时以渲染页和周围类型为准。
这一规则与 `SOURCE_TEXT_AUDIT.md` 的视觉复核规则一致。

## 2. Theorem 3.11 的源命题合同

Mochizuki 在 IUT III p.159 的 proof 只写“各断言立即由定义和所引用的
参考得到”（连续文本行 9616--9618）。这不是独立证明，所以所有被引用的
定义/命题都是 3.11 的真实前置，而非可忽略的背景。

### 2.1 输入

Theorem 3.11 以 IUT I Definition 3.1 的 initial Theta-data
`(F/F, X_F,l, C_K, V, V_mod^bad, epsilon)` 和一族 distinct
`Theta+-ell-NF-Hodge theaters` 为输入；这些 theaters 被认为来自
LGP-Gaussian log-theta-lattice。每个 `n` 还要有由 vertical coricity 得到的
`n,0 HT_D-Theta+-ell-NF` 和相应 D-Theta+-bridge（IUT III 行 9151--9175）。

### 2.2 Part (i): multiradial representation

| 源断言 | 原文依赖 | 必须实际存在的内容 |
|---|---|---|
| D-prime-strip procession | IUT I Prop. 6.9(ii)，III 行 9164--9175 | procession、自然函子、有限/无限阶段及其 morphism laws； |
| local packets/integral structures | III Props. 3.2(ii), 3.4(ii), 3.9(ii)，行 9176--9191 | place-indexed topological modules、mono-analytic integral structures、procession-normalized log-volume； |
| bad-place splitting monoid | III Prop. 3.5(ii)(c)，行 9192--9221 | 真实 `V_mod^bad` 上的 splitting monoid 与 tensor direct-summand action； |
| global fields/Frobenioids | III Props. 3.9(iii), 3.10(i)，行 9222--9253 | number fields、MOD/mod、non-realified/realified Frobenioids 及 degree/log-volume 计算； |
| Ind1 | III 行 9254--9260 | procession automorphism 产生的商不变性； |
| Ind2 | III 行 9261--9273 | 每个 direct summand 上独立 `Ism` 或 order-2 poly-automorphism 的作用和商； |
| functoriality/permutation | IUT I Cor. 6.10(iii)、IUT II Cor. 4.11(ii),(iii)、III Cor. 2.3(ii) | 任意 etale-picture spoke permutation 下的 poly-isomorphism 和稳定性。 |

### 2.3 Part (ii): labelled log-Kummer correspondence

| 源断言 | 原文依赖 | 不可省略的方向/兼容性 |
|---|---|---|
| labelled Kummer isomorphisms | IUT II Cor. 4.6(iii), 4.8(i),(ii)，III Props. 3.5(i), 3.10(i) | labeled `F`/`D`/`M` 数据之间的实际等价； |
| local tensor packets | III Props. 3.2(i),(ii), 3.4(ii), 3.5(i), 3.9(ii) | packet carrier、Q-span、splitting monoid 和 log-volume 同时相容； |
| global fields/Frobenioids | III Prop. 3.7(iii)--(v), 3.10(i) | global realification、MOD/mod naturality 和 LGP/lgp prime strips； |
| vertical variation | III Prop. 3.5(ii)(a),(b)，行 9437--9449 | nonarchimedean 是自然 inclusion `⊆`，archimedean 是自然 surjection `↠`；这是 upper-semi，不是 equality； |
| m-compatibility | III Props. 3.5(ii)(c), 3.10(ii),(iii), Remark 3.10.1 | roots of unity 的零对数效应、MOD 与 mod 的不对称、log-volume 精确兼容。 |

### 2.4 Part (iii): Theta-times-mu LGP-link compatibility

III 行 9450--9615 要求横向 LGP link 上的：

* `F⋊±_l` symmetry 和全 prime-strip poly-isomorphism；
* environment prime-strip 的自然同构；
* `n,0 R` projective-system datum 与 etale-picture permutation 的稳定/等变/函子性；
* Kummer isomorphisms、evaluation maps 和 local/global Frobenioid 的同时兼容。

具体引用包括 IUT III Theorem 1.5(iii)、Proposition 2.1(ii),(iii),(vi)、
Corollary 2.3(ii),(iii),(iv)、Propositions 3.4(ii)、3.7(iii)--(v)，以及
IUT II Corollaries 4.6(iv),(v)、4.7(iii)、4.8(iii)、4.10(ii),(iii)、
4.11(i)，IUT I Definition 5.2(vi),(viii) 和 IUT II Definitions 4.2/4.4/4.9
中的评价结构。仅证明一个 finite quotient 或一个 commutative square 不够。

## 3. 依赖图和逐层审计

```text
Lean kernel / Std / Mathlib
        |
        v
普通数域、处、完备化、p-adic、Weierstrass、有限线性代数、序和商
        |
        +--> IUT I Def.3.1 initial Theta-data  [全称识别 proved；任意输入构造未完成]
        |          |
        |          +--> Hodge theaters / histories / D-Theta bridge [source projection added; realization assumed]
        |          +--> Def.5.2 F/D-prime-strips                  [source projection + abstract kernel]
        |          +--> Prop.6.9 procession, Cor.6.10 symmetry       [source procession projection added]
        |
        +--> IUT II theta/Kummer/Frobenioid constructions          [接口/待办]
                   |
                   +--> III Thm.1.5, Props.2.1/3.2/3.4/3.5/3.7
                   +--> III Def.3.8, Props.3.9/3.10                 [未实现源对象]
                              |
                              v
                       IUT III Theorem 3.11(i)-(iii)                [pending]
                              |
                              v
                       Cor.3.12 Step (xi-a)-(xi-g)                  [contract only]
                              |
                              v
                       IUT IV estimates / ABC bridge               [downstream pending]
```

### 3.1 Lean/Mathlib 根层（已证明但不是 IUT 源命题）

这些节点是依赖链中真正被 Lean 证明、并可作为普通数学复用的部分：

| 节点/文件 | 已检查内容 | 边界 |
|---|---|---|
| Lean kernel、`Std`、`Init` | 归纳类型、函数/依赖类型、等式归纳、`Quot`、类型类和基础计算 | 不是 IUT 对象；非计算选择仍通过标准逻辑公理记录； |
| Mathlib `NumberField`/`Ideal`/completion APIs | number-field carrier、height-one prime、residue field、lying-over、completion maps、ramification API | 没有从这些 API 自动得到 IUT 的 bad-place、stable reduction 或 Hodge theater； |
| Mathlib p-adic/topology/analysis | `padicValNat`、DVR、连续性、完备性、范数/对数和有限和 | 没有 Tate uniformization、点级 Galois equivariance 或 q-pilot 识别； |
| Mathlib Weierstrass/elliptic API | 给定方程的判别式、`c4`、约化谓词、坐标变换和有限处传递 | 条件式曲线算术，不是原文任意输入曲线存在性； |
| Mathlib finite groups/quotients/matrices | `ZMod`、加法商、`Matrix.det`、`Finset`、tensor/determinant 规则 | 不能代替 Frobenioid、log-Kummer 或 holomorphic hull。 |

仓库中的对应 proved modules 为：
`Foundations/Arithmetic/{Radical,PrimitiveAdditive,PrimeIntervals,PrimeLabels,NormLog,PadicValuation}`、
`Foundations/NumberField/{FinitePlaces,FinitePlaceExtension,Places,LocalQParameter*}`、
`Foundations/Geometry/{WeierstrassModel,PuncturedEllipticCurve,EllipticTorsion,LocalReduction,ReductionBaseChange}`、
`Foundations/LinearAlgebra/FiniteDeterminant`、
`Foundations/Volumes/{WeightedVolume,HaarLogVolume}` 和
`Foundations/Theta/{GaussianKernel,GaussianSquareSum,SignedLabelEquiv}`。

这些模块的源文件没有自定义顶层 `axiom`/`opaque`；端点由
`verification/axiom_audit.lean` 和 `verification/upstream_foundations_axiom_audit.lean`
逐声明列出并使用 `#print axioms` 审计。历史成功日志显示典型端点只依赖
`propext`、`Classical.choice`、`Quot.sound`。这三项是 Lean/Mathlib 的标准
基础，不是把 IUT 命题当作公理；但它们也不能增加源命题的数学内容。

### 3.2 IUT I initial Theta-data（第一处实质断点）

源 Definition 3.1 的六组条件在 IUT I 行 3123--3280：

* `F` 为含 `sqrt(-1)` 的数域，带 `F_mod`、`K` 和指定椭圆曲线/去 cusp 曲线；
* 指定非阿基米德 bad places 上的 stable reduction、split/multiplicative
  reduction、局部 q-parameter；
* `l >= 5`、六扭点/模 `l` Galois 表示和像包含 `SL_2(F_l)` 的条件；
* `C_K`/`X_K` orbicurve、覆盖和基本群精确序列；
* `V` 到 `V_mod` 的 section、局部基本群和有限/无限处数据；
* cusp parameter `epsilon` 及其兼容性。

本仓库映射：

| 文件/声明 | 状态 | 审计理由 |
|---|---|---|
| `IUTI/InitialTheta/ArithmeticData.lean:102-110` `initialThetaArithmeticData` | `interface` | 记录把算术和椭圆曲线输入显式化，但 note 明确说 reduction/anabelian/torsion 条件未证明； |
| `IUTI/InitialTheta/SourceDefinition31Boundary.lean` `SourceDefinition31Data` | `interface` | Definition 3.1 的 reduction、bad/selected places、q、torsion、orbicurve exact sequence、section 和 cusp 字段全部显式化；逐字段投影到 `InitialThetaInput` 已证明，但从任意 arithmetic data 构造 inhabitant 仍未证明； |
| `IUTI/InitialTheta/SourceInitialThetaData.lean` `initialThetaData_conclusion` / `ofClauses_conclusion` | `proved` | `∀ S : SourceInitialThetaData l, InitialThetaDataConclusion S`，并对任意候选及其六组 clause 记录给出同一结论；(a)--(f) 的实际数据族和原始 place/q/torsion/exact-sequence/section/cusp 全称量词均保留；不声明 `Nonempty`，也不构造任意 arithmetic input 的 source inhabitant； |
| `IUTI/InitialTheta/SourceObligations.lean` `initialThetaData` | `proved`（全称识别） | obligation 的 Lean 结论是上述全称 source-faithful recognition theorem；原始的“从 arithmetic input 构造 source data”仍是未完成的上游构造，不被该结论替代； |
| `IUTI/HodgeTheater/HodgeTheaterCore.lean:31-104` | `proved`（结构律） | `HodgeTheaterLink` 的 refl/symm/trans 等代数律成立；载体和存在性仍是结构字段； |
| `IUTI/HodgeTheater/HodgeTheaterCore.lean:115-129` `hodgeTheaterCore` | `interface` | 明确保留 full anabelian/Hodge-Arakelov compatibility 为后续字段； |
| `IUTI/HodgeTheater/History.lean` | `interface/test carrier` | 有具体 history/link 组合，但没有任意 distinct theater family 的构造； |
| `IUTI/InitialTheta/Concrete*` | `test carrier` | `Q(i)`、处 5、`q=5` 的有限/局部例子，不能推出 Definition 3.1 的任意输入。 |

因此 3.11 的第一项假设还没有 source-faithful inhabitant。一个
`ThetaFieldTower` 或 `ConcreteInitialThetaCStage` 只能证明它自己的有限实例。

### 3.3 IUT I prime strips、procession 和 etale-picture

源 Definition 5.2（IUT I 行 7702--7775）和 Proposition 6.9(ii)/Corollary 6.10(iii)
（行 9811--9995）要求真实的 F/D-prime-strips、capsule、自然函子、procession
和 arbitrary spoke permutation。

本仓库：

* `IUTI/HodgeTheater/PrimeStripCore.lean:24-251` 的 `DPrimeStrip`、
  `FPrimeStrip`、equivalence、action、total degree 和 group laws 是
  `proved` 的抽象核；
* 该文件 `:253-261` 的 obligation note 明确写出 arithmetic-geometric
  realization 仍 pending；
* `IUTII/Frobenioid/LocalPrimeStrip.lean:30-91` 的局部 carrier、degree 和
  action laws 可证明，但 `:93-102` 将 integral Frobenioid、arithmetic
  Frobenius 和 etale realization 标成 `interface`；
* `SourceDefinition52*`、`SourceFiniteStage*` 和 `Iut/Foundations` 的
  finite-stage/reconstruction/tempered kernels是可复用的 alternative-route
  foundation，但并未证明给定 IUT initial data 满足全部原文假设。

这一步的“抽象 `FPrimeStrip` 存在”不能作为“原文 D-prime-strip procession
存在”。二者之间尚缺 source carrier bridge。

### 3.4 IUT II Kummer、Frobenioid 和 vertical correspondence

源 IUT II Corollaries 4.6--4.11 和 Definition 4.9 的依赖范围见第 2 节。仓库
状态：

| 文件/声明 | 状态 | 已证明的最强内容 | 仍缺内容 |
|---|---|---|---|
| `IUTII/Kummer/KummerPolynomial.lean`、`RootRealization.lean` | `proved` | 多项式根、代数闭包嵌入、根幂律 | etale/Frobenioid source map； |
| `CompatibleRoots.lean`、`NatRootSystem.lean`、`RationalRootSystem.lean` | `proved` | 兼容根链和整数/有理标签律 | 原文的 global Kummer correspondence； |
| `KummerClass.lean`、`KummerRootRatio.lean` | `proved` kernel | unit-valued Kummer class、root ratio、序/对数辅助律 | 真实 local/global log-shell； |
| `VerticalLogKummer.lean:13-51` | `interface` | transport 迭代和 `kummer_le_transport` 的 upper-semi 序理 | 论文的 maps、carrier、Frobenioid 和 compatibility； |
| `VerticalCorrespondence.lean:5-20` | `pending` | 只有 obligation | IUT II vertical log-Kummer correspondence 全部构造； |
| `ConcreteLocalKummerExample.lean`、`ConcreteEtaleKummerBridge.lean` | `test carrier` | `q=p` 的有限兼容根/商和局部 action | 曲线点、etale 基本群、source theta-link 识别。 |

尤其要保留 IUT III 中 `Ind3` 的方向：非阿基米德自然包含、阿基米德自然满射。
仓库的 `UpperSemiCorrespondence` 只证明任意单调函数的抽象复合律，不能证明
这些实际 maps 存在。

### 3.5 IUT III 中间命题

Theorem 3.11 直接消费以下 IUT III 结果：

| 源结果 | 原文位置 | 本地对应 | 判定 |
|---|---|---|---|
| Theorem 1.5 vertical/horizontal/bi-coricity | IUT III 行 2825--3103 | `HodgeTheater`/prime-strip kernels | 只有抽象/接口，未 source realization； |
| Proposition 2.1 | 行 3412--3555 | `IUTII/Theta`、Kummer bridge | 局部代数有证明，vertical coric construction 未闭合； |
| Corollary 2.3 | 行 4214--4388 | etale/finite model kernels | permutation/etale-picture source object 未闭合； |
| Proposition 3.2 | 行 5655--5787 | finite tensor packet/determinant modules | 有限 packet arithmetic proved，任意 place-indexed packet 未构造； |
| Proposition 3.4 | 行 5941--6020 | local prime-strip/LGP interfaces | actual LGP monoid 未构造； |
| Proposition 3.5 | 行 6021--6180 | `VerticalLogKummer` contract | upper-semi contract only； |
| Proposition 3.7 | 行 6390--6616 | source Frobenioid bridges | concrete/finite source model only； |
| Definition 3.8 | 行 6617--6801 | theta/lattice vocabulary | source LGP-Gaussian lattice not constructed； |
| Proposition 3.9 | 行 6838--6994 | `HaarLogVolume`/finite determinant | ordinary log-volume identities only； |
| Proposition 3.10 | 行 8717--8941 | Kummer/Frobenioid comparison interfaces | global vertically coric field/Frobenioid construction absent。 |

因此 3.11 的“由 definitions/references 立即得到”链在这些节点中断，而不是
在最后一行的 `le_trans` 处才中断。

### 3.6 Theorem 3.11 本地文件和有限测试模型

| 文件/声明 | 状态 | 实际范围 |
|---|---|---|
| `Theorem311/Obligations.lean:5-10` `theorem311Output` | `pending` | 明确要求 actual IUT I--II data； |
| `Theorem311/Output/MultiradialAlgorithm.lean:5-10` | `pending` | 只登记算法目标； |
| `Theorem311/Indeterminacy/Ind1.lean:5-10`、`Ind2.lean:5-10`、`Ind3.lean:5-10` | `pending` | 只登记 source obligations； |
| `Indeterminacy/QuotientTransport.lean:18-66` | `proved` kernel | 一般商映射和三层 transport；无 IUT carrier； |
| `Indeterminacy/OrbitTransport.lean:17-98` | `proved` kernel | 群轨道商的 representative/descent；无真实 Ind1/Ind2 group； |
| `Indeterminacy/UpperSemi.lean:18-70` | `proved` kernel | `UpperSemiCorrespondence` 的 singleton/compose/order laws；无实际 log-Kummer image； |
| `MultiradialOutputKernel.lean`、`MultiradialProfileKernel.lean` | `proved` kernel | abstract Ind1/2/3 steps、route、level 和 volume monotonicity； |
| `ConcreteFiniteModel.lean`、`SourceFinite*`、`Parametric*` | `test carrier/interface` | 两个 `ZMod l` translation 和一个 `Nat` level 的有限 procession；不能量化任意 D-prime-strip/Hodge theater； |
| `SourceProcessionBoundary.lean` | `test carrier/interface` | 将 Q(i)-at-5 history、packet、finite route 组装；不是原文 theorem output。 |
| `Theorem311/SourceH1H2Construction.lean` | `source projection (build pending)` | 从完整 `OriginalInput` 暴露 H1 的 D-Theta bridge、H2 的 F/D procession 和 spoke naturality；不从 arithmetic-only data 生成 Hodge theaters。 |
| `Theorem311/SourceK1K2Construction.lean:56-270` `K1VerticalBoundary` | `interface (build pending)` | 消费已供给的 `SourceVerticalRealization` 形状，逐项保留 vertical upper-semi、nonarchimedean inclusion、archimedean target-to-source lift、profile 等式和 labelled Kummer 双射；不从 H1/H2 构造真实 log-shell/Frobenioid carrier。 |
| `Theorem311/SourceK1K2Construction.lean:350-578` `K2FrobenioidBoundary` | `interface (build pending)` | 消费 local/global `SourceProposition37Frobenioid`、MOD/mod maps、degree/realification/transport 方程、Prop. 3.10 comparison 与 K1 upper-semi；不由映射名称推断逆元或 source 存在性。 |

有限模型中“Ind1/Ind2 invariance”和“Ind3 monotonicity”是真实 Lean 定理，
但其载体是人为选定的 `ZMod`/`Nat` 结构；没有证明它等价于原文的
procession automorphisms、独立 `Ism` actions 或 local upper-semi Kummer maps。

### 3.6.1 Theorem 3.11/H1-H2 与 Corollary 3.12 的共通输入

`Theorem311/SourceH1H2Construction.lean` 现在只接受原文开头已经给出的
`OriginalInput`，并逐项投影出 H1/H2 的 source carrier。`StepXI/SourceSharedBoundary.lean`
进一步固定第 `1` 列，证明 `l*` 阶段的有限索引、真实 D-prime-strip、D-link、
spoke 的 `isoPi` 双射及 projection compatibility，并记录该列 q/label-scale
沿 source link 和 spoke 的传输。

这些结论是 3.11(i)--(iii) 与 3.12 Step (xi) 都会读取的共通输入，因此可以
提前完成；它们没有把 Theorem 3.11 的 multiradial output、Ind1--Ind3、IPL、
SHE、APT、holomorphic hull 或最终 log-volume membership 加入 H1/H2。当前构建
结束前状态记为 `source projection (build pending)`；编译和公理审计通过后再按
声明逐项更新为 `proved kernel/source projection`。

K1/K2 的新增组装层同样不越过 source gate：`k1OfRealization` 只从已经携带
`SourceVerticalRealization` 的 `SourceTheorem311Realization` 做字段投影；
`k2FromFields` 要求调用方显式提供 local/global Frobenioid、MOD/mod、degree、
realification、transport 和 comparison 字段。K1 的 inclusion/surjection 方向
分别保持 source 的 `z ∈ S -> z ∈ nonarchimedeanImage` 与
`z ∈ archimedeanImage -> ∃ y ∈ S, z ≤ y`，没有改成无条件 equality。当前两项
状态为 `interface (build pending)`，待本轮统一编译、warning 和公理审计后再更新。

### 3.7 Corollary 3.12 Step (xi) 和 IUT IV

IUT III pp.181--185（连续文本行约 10751--10951）要求：

* IPL（input prime-strip link）；
* SHE（simultaneous holomorphic expressibility）；
* APT（algorithmic parallel transport）；
* fixed one-column arithmetic holomorphic structure 中的 holomorphic hull；
* determinant 的正 tensor power、label normalization、1-column log-Kummer
  correspondence；
* 关键 membership `-|log(q)| ∈ R_{<= -|log(Theta)|}`。

本地状态：

| 文件 | 状态 | 说明 |
|---|---|---|
| `Corollary312/StepXI/Contract.lean:32-58` | `proved conditional` | 从已供给的 `StepXIContract` 用 `le_trans` 得到结论和 q 正性； |
| `Contract.lean:61-78` `stepXIContractConstruction` | `pending` | contract 从 source 3.11 output 的构造未完成； |
| `StepXI/ParametricStepXI.lean:27-183` | `interface` | IPL/SHE/APT 等是 `StepXIInput` 字段，投影定理不是构造证明； |
| `StepXI/SourceSharedBoundary.lean` | `source projection (build pending)` | 复用 H1/H2 的固定第 1 列 procession、`l*` stage、D-link/spoke transport 和 q/label-scale transport；不构造 Step (xi) 的额外比较命题； |
| `StepXI/HolomorphicHull/Volume.lean:23-169` | `proved kernel` | finite positive packet 的 determinant/tensor/rescale/log identities； |
| `Volume.lean:179-186` `hullDeterminantLogVolume` | `interface` | source holomorphic hull 和 log-volume construction 未完成； |
| `StepXI/HolomorphicHull/WeightedNormalization.lean:25-107` | `proved kernel` | finite positive denominator 的 weighted normalization； |
| `IUTIV/Estimates/Section1.lean:5-9`、`Section2.lean:5-9` | `pending` | 明确依赖 Corollary 3.12； |
| `ABCBridge/Bridge/IUTToABC.lean:8-12` | `pending` | downstream bridge 不能反向补足 3.11。 |

所以 `cor312_of_constructed_stepXI` 的类型正确性不等于 Corollary 3.12 已证，
更不等于 Theorem 3.11 的 source prerequisite 已证。

## 4. 上游仓库审计

上游固定版本和取舍记录在 `papers/motizuki_corpus/UPSTREAM_REUSE.md`。本节
补充与 3.11 直接相关的字段级检查。

### 4.1 `promachina/iut-lean`

审计过的快照：

* `vendor/promachina/snapshots/0d52e0fd5b53`（生产快照）；
* `vendor/promachina/snapshots/1fa6387f11fb6dc67eb618b8138e6bc64f56b039`
  （较新 source-trace 快照）；
* 上游公开 HEAD 在台账中记录为 `e2da14360c854e3ac1ad946339d581f737766a34`。

`vendor/promachina/snapshots/0d52e0fd5b53/LEANFORMAL_SNAPSHOT_MANIFEST.json`
固定了上游 commit `0d52e0fd5b532117a5f804809583da446fb9864b`（183 个 Lean
文件）；`vendor/promachina/patches/4.32.2/MANIFEST.json` 记录从上游
v4.30.0 到当前 Mathlib/Lean 4.32.2 的 20 个适配文件，其中 11 个字节一致、
其余有明确 patch/hash。故“来自上游”不是未固定的远程状态。

关键文件是 `Iut/Foundations/SourceTheorem311.lean`、
`SourceTheorem311Assembly.lean`、`SourceTheorem311Horizontal*.lean` 和
`Iut/Stage1/IUTStage1Theorem311*.lean`。

最新 `SourceTheorem311ColumnBoundary` 的字段（文件约 47--100 行）包括：

`lattice`、`logShellAlgorithm`、`column`、`verticalFamily`、
`verticalLogLinks`、`presentationConstruction`、`multiradialAlgorithm`、
`siteLabeled`、`labeledKummer`、`siteSplitting`、`badPrimeLogKummer`。

这些字段正好对应原文 3.11(i)--(iii) 的对象；但该 structure 的 inhabitant
需要调用方预先提供每一个字段。字段投影定理证明的是“若完整 source boundary
已给出，则 quotient/Ind1/Ind2/Ind3/volume 结论成立”，不是证明 boundary
存在。上游 `Stage1` 文件还把 algorithmic output 的 `certified`/qualitative
内容作为独立输入，审计注释明确称其为 opaque/obligation data。

更细的声明级检查给出同样结论：

* `SourceTheorem311Ind12Construction.lean:263-296` 的 candidate 有
  algorithm、Ind1 equality、permutation-biCoric 等字段，但
  `:302-317` 的 `SourceIUTIIITheorem311iRecognition` 只要求
  `candidate_exists : Nonempty ...`，`:320-337` 用 `Classical.choice` 取回
  candidate；这不是从 IUT I--II 数据构造 candidate；
* `SourceTheorem311VerticalConstruction.lean:193-243` 的 ii-candidate 把
  `fullLogLinks`、`siteLabeled`、`labeledKummer`、`siteSplitting`、
  `badPrimeLogKummer`、`globalNumberFieldLogKummer` 作为字段；`:254-293`
  的 construction 仍把 target realization、bad/global log domains 和
  `unitToLogUnit` 作为输入，`:326-432` 只是组装，`:441-477` 的 evaluation
  也以该 construction 为前提；
* `SourceTheorem311HorizontalConstruction.lean:182-226` 的 iii-candidate
  把 times-mu、environment strips、mono-theta systems、Kappa squares 和
  compatibility 作为字段；`:232-248` 仅有 `candidate_exists`，`:251-268`
  再以 `Classical.choice` 选取；
* `SourceTrace/Corollary312SourceGraph.lean:118-150,444-462` 的 acceptance
  规则明确禁止把上述 `candidate_exists`、full log links、labeled Kummer、
  splitting、global Kummer 或 lowercase cross-height exactness 当作已证明
  输入。其图把 3.11 setup 标为 premise/open-boundary，不能按 `constructed`
  标签解读为存在性证明。

因此上游实现的正确分类是：

* source-shape definitions 和若干 finite/category/tempered kernels：
  `proved` 或 `migrated-proof`；
* Theorem 3.11 boundary、labeled Kummer、holomorphic-hull、IPL/SHE/APT
  的存在性：`interface-only`；
* 任何从字段投影出的 ordered-real conclusion：`conditional`。

没有从该上游快照发现可在当前仓库直接消费、且已经证明任意源输入的
Theorem 3.11 theorem。

上游 README 的 `disputeSettledByCurrentStage=false` 以及“full Frobenioids、
holomorphic hulls、determinants、local-field/Haar compatibility 仍剩余”的
说明，与上述字段审计一致；其 legacy finite Theorem 3.11 模型也明确不是
论文的 procession/Indeterminacy/log-Kummer/algorithm 对象。

`logs/lean/axioms-upstream-foundations-20260806-085309/status.json` 记录了一次
成功的上游 foundation 审计：`exitCode=0`、`sorryAxFound=false`；其 stdout
包含 182 个 declaration-level `#print axioms` 报告，全部只出现
`propext`、`Classical.choice`、`Quot.sound`，没有 custom axiom。该结果说明
上游的有限/类别/tempered kernels 具有可审计的 Lean 证明，不说明其 source
对象的全部存在性已经被证明。

### 4.2 其他上游仓库

| 仓库/固定版本 | 可复用内容 | 对 3.11 的判定 |
|---|---|---|
| `Takkun-kohinata/IUT_LEAN@9d56c46` | ThetaGroup、MonoTheta、prime-strip/Frobenioid degree、compatible roots、Ind1--3 kernel | 只复用已审计的群/序/算术引理；source bridge 与 finite/model diagnostics 仍未解决； |
| `lana-project/iut4-sec1@a7551d2` | IUT IV Section 1 的 Mathlib-only 数值核 | downstream elementary kernel；不能提供 IUT III output； |
| `com-junkawasaki/iut-lean@ca4c0dd` | Mason--Stothers/多项式 ABC 及独立数论 | 不属于 IUT I--III 依赖链； |
| `PriestAmbrose/IUT-Corollary3_12-Lean@e5d5d20` | axioms-first 的 Corollary 3.12 词汇/边界 | comparison/registry only；抽象 theorem 不能证明 disputed implication。 |

所有上游代码都按固定 commit、Lean/Mathlib 版本、许可证和 declaration-level
axiom 状态登记；没有把外部 theorem 作为无条件 axiom 导入生产路径。

## 5. Lean4 自带内容和公理边界

### 5.1 直接检查的命令

在仓库根目录运行：

```text
lake build LeanFormal
lake env lean verification/axiom_audit.lean
lake env lean verification/upstream_foundations_axiom_audit.lean
powershell -File tools/check_no_custom_axioms.ps1
powershell -File tools/check_axiom_boundary_logged.ps1
```

`verification/axiom_audit.lean` 对 arithmetic、number-field、geometry、
Kummer、Frobenioid、finite Theorem 3.11 和 Step-XI endpoints 逐一使用
`#print axioms`；`upstream_foundations_axiom_audit.lean` 对 `Iut/Foundations`
的 imported source kernels 做同样检查。

### 5.2 解释

典型已证明 endpoint 的结果是：

```text
depends on axioms: [propext, Classical.choice, Quot.sound]
```

含义是：

* `propext`：命题外延性；
* `Classical.choice`：Mathlib/Lean 的非构造性选择；
* `Quot.sound`：商类型的等价关系消去。

它们属于 Lean/Mathlib 的标准逻辑基线。它们不能被解释为 IUT-specific
axioms，也不能由“只用了标准公理”推出 IUT source construction。

当前源文件扫描规则是：

```text
rg -n "(?m)^\s*(axiom|opaque)\b|\bsorry\b|sorryAx" LeanFormal Iut -g '*.lean'
```

注意：`AUDIT_LEDGER.md` 和若干 2026-08-07 历史日志仍记录旧版本中
`LeanFormal.IUT.theorem311_produces_stepXI_contract` 的 `sorryAx`。当前
`Contract.lean` 已移除该声明，`tools/check_axiom_boundary_logged.ps1`
现在要求当前工具链输出中的 `sorryAx` 行数严格为零；历史日志不参与当前
生产边界判定。

截至本报告生成时对当前源文件的只读扫描结果为：`LeanFormal/IUT` 和
`Iut` 中没有顶层 `axiom` 或 `opaque`，也没有实际 `sorry`/`sorryAx` 声明；
命中的四行只是 `abc_with_sorry` 的测试说明和字符串注释。这一结果只说明
当前源码没有文字级自定义占位符，仍需下面的当前工具链 `#print axioms` 和
全量构建来确认生成的 `.olean` 没有旧缓存污染。

## 6. 依赖闭包中的已证明内容清单

下面列出从 3.11 入口向下实际遇到、且可以独立归类为 proved 的内容。每行
后面的“边界”是它不能越过的下一条 source obligation；这就是“若 A 需要
BCD，则审计 BCD；若 B 未证明，则继续向下审计已经证明的低层，而不把 B
伪装成已证”的闭包结果。

### 6.1 普通算术和序

* `Radical`：自然数 radical 的零值、正性、整除性、互素乘法；
  `PrimitiveAdditive`：primitive additive triple 和 radical 分解；
  `PrimeIntervals`/`PrimeLabels`：有限素数区间、素性和奇性标签；
* `NormLog`：norm 的乘法、`Real.log` 加法和 `Multiplicative Real` hom；
* `PadicValuation`：自然数素数赋值的乘法/幂律、素数支撑和素幂整除刻画；
* `GaussianKernel`/`GaussianSquareSum`/`SignedLabelEquiv`：有限标签求和、
  Gaussian square-sum 归一化、signed-label 平移等价。

这些是可复用的 L0 结果，但没有 theta value、q-pilot 或 ABC 估计的 IUT 解释。

### 6.2 数域处和局部几何

* `FinitePlaces`/`Places`：finite/infinite places、restriction、section image、
  residue characteristic；
* `FinitePlaceExtension`/`LocalQParameter*`：完备化映射、ramification、
  valuation-ring/residue maps、DVR q-candidate；
* `WeierstrassModel`/`PuncturedEllipticCurve`：具体曲线模型、去一点 carrier、
  j-invariant；
* `LocalReduction`/`ReductionBaseChange`：给定模型的 good/multiplicative/
  split/stable reduction 及条件式基变；
* `EllipticTorsion`：给定真实二维基后的点作用、连续矩阵表示和核固定域。

边界是“指定 IUT 输入曲线在指定处具有这些性质”和“Tate uniformization/
Galois-equivariant points”仍未证。

### 6.3 canonical q-series 和具体 Q(i)-at-5 carrier

* `TateCurveArithmetic`、`TateCurvePadicEstimates`、
  `TateCurveDiscriminantEstimates`、`TateCurveLocalReduction`：canonical
  `q=p` 方程的系数、判别式、椭圆性、积分性、split multiplicative reduction；
* `ConcreteSplitMultiplicativeCurve`、`ConcreteSplitCurvePadic`、
  `ConcreteSplitCurveFivePlace`：有理曲线 `y^2+xy=x^3+5`、真实处 5 和
  `Q_5`/completion transport；
* `ConcreteTateKummerPacket`/`ConcreteTateFiniteLevel`/`ConcreteTateDeckQuotient`：
  q-deck、有限 kernel 商和兼容根。

这些闭合的是一个具体 local certificate；没有证明它是原文给定的任意
number-field elliptic curve，也没有点级 Tate uniformization。

### 6.4 IUT II 的有限代数核

* `CyclicQuotient`、`FiniteCyclicQuotient`、
  `FiniteCyclicQuotientTransport`：一般 commutative/additive group 的商、
  representative、kernel、descent 和 commuting-square transport；
* Kummer polynomial/root/ratio/class/compatible-root 文件中的 algebraic laws；
* `PrimeStripArithmetic`/`PrimeStripDegree`：有限标签和 monoid degree laws；
* `LocalIntegralMonoid*`、`LocalUnitKummer*`、`TimesMu*`：具体 integral
  carrier 上的 action、Kummer map、injectivity/residual finite kernels。

边界是 etale fundamental-group、Frobenioid realization、source theta-link。

### 6.5 IUT III generic and finite model kernels

* `QuotientTransport`、`OrbitTransport`、`UpperSemi`；
* `MultiradialOutputKernel`、`MultiradialProfileKernel`：抽象 action、route、
  level、log-volume invariance/monotonicity、possible-image upper bound；
* `ConcreteFiniteModel`、`SourceFiniteOutput`、`SourceFiniteMultiradial`、
  `ParametricCarrier`、`ParametricDStage`、`ParametricRouteAlgebra`、
  `ConcreteRouteNormalForm`、`ConcreteRouteUniqueness`：把上述 kernel 组装
  到 `ZMod`/`Nat` 有限模型并证明其内部 laws；
* `HolomorphicHull/Volume` 与 `WeightedNormalization`：finite positive packet
  determinant/tensor/rescaling/log identities。

这些内容的共同边界是 source carrier/existence，不是 Lean 的逻辑公理。

## 10. 当前复核（2026-08-08）

本轮新增 `LeanFormal/IUT/IUTIII/Theorem311/SourceFaithfulBoundary.lean`，并由
`LeanFormal/IUT/Project.lean` 接入生产入口。该文件按 3.11(i)--(iii) 的顺序
逐条证明以下结论：

* procession 的 Ind1/Ind2/Ind3 群律、交换律、层级单调性和水平路线商不变性；
* local tensor packet 的正性、行列式/对数体积兼容，以及 Ind1/Ind2 不变和
  Ind3 上界；
* Ind1/Ind2 生成商的良定义、层级不塌缩和体积/像下降；
* labelled Kummer 双射、vertical transport 的上半连续不等式，并保留
  非阿基米德 `⊆` 与阿基米德 `↠` 的不同字段方向；
* Theta-times-mu 横向 square、评价映射自然性、theater permutation 稳定性，
  以及三部分 `Theorem311Output` 组装。

本轮还把 `VerticalSiteData` 从原先的可选说明提升为 `Input.verticalSite`
的强制前置，并分别证明了非阿基米德 source-to-target 包含、阿基米德
target-to-source 满射提升、两种目标集合等式、成员刻画和迭代提升链；因此
Part II 不再通过 `Option.none` 隐去垂直 site 对象。该对象本身仍需由真实的
IUT II log-shell/Frobenioid 构造提供，强制字段不等于已经完成该构造。

随后新增 `SourceDefinition31Boundary.lean`，逐项封装 Definition 3.1 的六类
条件，并证明 `SourceDefinition31Data.toInitialThetaInput` 保留每个字段；该层
登记为 `IUT-I.initial-theta-source-definition31-boundary`（`interface`），不把
record 的字段投影误记为任意输入的存在性证明。又新增
`SourceInitialThetaData.lean`，对已经携带全部 (a)--(f) 条件的任意 source tuple
证明 `initialThetaData_conclusion` 的全称结论，并在
`SourceObligations.lean` 登记为 `proved`；这只是定义的忠实识别定理，不是
arithmetic-to-source 构造定理。

这些定理的载体、映射和兼容性均作为 `Input` 的显式类型化前置参数；没有
`sorry`、自定义 `axiom` 或 `candidate_exists`/`Classical.choice` 形式的隐式
存在性补洞。`lake build LeanFormal` 于本次复核通过（4309 jobs），
`lake env lean verification/axiom_audit.lean` 通过；新入口的
`#print axioms` 只出现 `[propext, Classical.choice, Quot.sound]`。

边界没有被改写：`Input` 的任意 Definition 3.1 inhabitant、真实 Hodge
theater/procession 以及 global log-Kummer/Frobenioid 的构造仍是前置待办，故
原文“任意初始数据无条件存在 Theorem 3.11 output”仍不能标为
`source-faithful proved`。新增结果登记为
`IUT-III.theorem-3.11-explicit-prerequisite-boundary`（`proved`），原有
`IUT-III.theorem-3.11-output` 保持 `pending`。

## 7. 缺口、停止点和后续所需证明

### 7.1 当前停止点

按用户的迭代规则，3.11 的直接输入至少要求 A = initial Theta/Hodge theater、
B = procession/D-prime-strip、C = vertical log-Kummer/Frobenioid。A 的
arithmetic-to-source 构造和 C 在当前仓库分别是 `pending/interface`，B 只有
抽象 prime-strip kernel；A 的 source tuple 全称识别层已 proved，但不提供
新的 inhabitant。因而
搜索在“source-faithful input inhabitant”处停止；继续堆积 finite quotient 或
ordered-real lemmas 不会闭合 3.11。

### 7.2 要解除停止点的最小证明包

1. 从 Definition 3.1 的任意 arithmetic input 构造完整 initial Theta-data，并
   证明每个 field 的 reduction、torsion、Galois、orbicurve、section、cusp 条件；
2. 从该数据构造 distinct Hodge theaters、histories、D-Theta bridge、
   `Prc(n,0 D^|_T)` procession，并证明 IUT I Prop. 6.9(ii) 的自然性；
3. 在真实 selected/bad places 上构造 IUT II local/global Frobenioid、
   mono-theta/log-shell、Kummer maps 和 Prop. 3.5 的 upper-semi inclusion/
   archimedean surjection；
4. 构造 III Props. 3.2/3.4/3.7/3.9/3.10 的 packet、degree、log-volume、
   MOD/mod/realification 和 m-compatibility；
5. 用 Theorem 1.5、Cor. 2.3 及 II Cor. 4.6--4.11 构造横向 LGP-link 的
   Kummer/evaluation/permutation compatibility；
6. 只有 1--5 全部通过后，才能把 `IUT-III.theorem-3.11-output`、Ind1、
   Ind2、Ind3 的 obligation 由 pending 改为 source-faithful proved。

随后还必须独立构造 Corollary 3.12 Step (xi) 的 IPL/SHE/APT、holomorphic hull、
determinant normalization 和 q/Theta membership；IUT IV 不能补救这些上游缺口。

## 8. 复核记录

历史成功构建和公理日志保存在 `logs/lean/`，尤其是：

* `logs/lean/concrete-theorem311-finite-model-project-20260807.log`；
* `logs/lean/concrete-theorem311-finite-model-axiom-boundary-20260807-r2.log`；
* `logs/lean/axiom-audit-20260807-full-r1.log`；
* `logs/lean/axioms-20260807-073811/axiom_audit.stdout.log`；
* `logs/lean/axioms-upstream-foundations-20260804-063457/axiom_audit.stdout.log`。

这些日志证明相应历史快照中的 finite kernels 使用标准 Lean/Mathlib 公理；
它们不证明当前 source-faithful 3.11 已完成。当前复核应以本报告日期、
`git rev-parse HEAD`、当前 `lake build` 和重新生成的 `#print axioms` 输出为准。

## 9. 最终判定

* IUT III Theorem 3.11：**未按原文 source-faithfully proved**；
* Theorem 3.11 的 generic quotient/order/determinant kernels：**proved**；
* `Q(i)`-at-5 finite carrier：**proved test carrier**；
* Theorem 3.11 source output、Ind1、Ind2、Ind3：**pending/interface**；
* Corollary 3.12 Step XI：**conditional contract only**；
* IUT IV estimates 和 ABC bridge：**downstream pending**。

## 11. 从根层到 Definition 3.1 的可审计路线图

本节是 Definition 3.1 的唯一推进路线。代码重写、模块拆分或替代证明都必须
在这里找到对应的节点和证据；没有节点的辅助定理不进入生产路径。路线图中的
“完成”指 source-faithful proved，而不是“某个 record 有字段”或“某个有限例子
通过”。每个节点都要有一个明确的 Lean 声明、一个原文量词检查和一次独立的
`#print axioms` 记录。节点只能按编号顺序关闭，不能用后面的证书投影提前标记
前面的构造完成。

### 11.1 不可改变的量词和对象边界

* 根层的输入是 `l : PrimeGeFive` 和原文允许的 arithmetic data；不能把
  `SourceDefinition31Data`, `InitialThetaInput`, `Certificate`, 或任何
  `..._proved` 字段当作新的外部假设。
* `SourceDefinition31Data` 只能作为 Definition 3.1 全部六类条件已经被证明后
  的内部汇总对象。由 `S` 投影一个字段的定理只关闭“识别”节点，不能关闭
  “从 arithmetic data 构造 `S`”节点。
* 所有 place、torsion、orbicurve、section 和 cusp 的结论都保持原文的
  `∀`/`∃`/函数方向。特别是 upper-semi 的非阿基米德包含和阿基米德满射不能
  被替换为 equality，也不能用 `Nonempty` 替换一般构造。
* 不允许 `axiom`、`opaque`、实际 `sorry`、未审计的外部 theorem，或把待证明
  结论塞进 input/certificate 字段。`Classical.choice` 只能在已经证明存在性后
  选取一个坐标，并且必须同时保留其 witness 定理。

### 11.2 阶段表（根层至 source data）

| 节点 | 原文对象/目标 | Lean 交付物和关闭证据 | 当前状态 |
|---|---|---|---|
| D0 | Lean kernel、Std、Mathlib 的基础类型、群、域、有限维和范数 | `#print axioms` 只出现标准基础；没有 IUT-specific 输入 | `proved` |
| D1 | 素数标签 `l >= 5`、`l` 为奇素数 | `PrimeGeFive.prime`, `.odd`, `.ge_five` 的全称投影；`l.value != 0` | `proved` |
| D2 | `F_mod`, `F`, `K` 的数域塔和椭圆曲线载体 | 从实际 `InitialThetaArithmeticData` 字段得到实例、`ThetaFieldTower`、曲线；证明 `sqrt(-1)` 和 `Coprime(finrank,l)` | `interface`，待任意输入构造 |
| D3 | IUT I Def.3.1(a) 的 place partition | 对任意 `Selected`, `Bad` 构造 `SourcePlacePartition`，证明 bad inclusion、非空、有限、label compatibility | `interface`；字段投影定理已可证 |
| D4 | Def.3.1(b) stable/multiplicative/split reduction | 对每个 bad place 的三个全称谓词、split -> multiplicative、q 非零、`||q|| < 1` 和稳定兼容 | `interface`；从曲线/处的数学构造待证 |
| D5 | Def.3.1(c) torsion 和 Galois 大像 | `SourceInitialThetaData` 给定后，真实 `LTorsion` carrier、canonical representation、SL₂ 大像、K-kernel、kernel 闭包、有限 Galois/连续性逐项投影 | `proved(kernel)`；从 arithmetic curve 构造这些 Clause C 字段仍待完成 |
| D6 | Def.3.1(d) orbicurve 和基本群精确序列 | `SourceInitialThetaData` 给定后，四条 exact sequence 的 injection/projection/section、逐点 exact iff、注入单射、投影满射、section 右逆/单射、残差分解和三个嵌入 square | `proved(kernel)`；真实 orbicurve/基本群构造仍待完成 |
| D7 | Def.3.1(e) sections 和 local groups | `SourceInitialThetaData` 给定后，finite/infinite place partition、局部 carrier、exactness、section 右逆/单射、局部类型和自然性逐项投影 | `proved(kernel)`；从原文 arithmetic 输入构造 local data 仍待完成 |
| D8 | Def.3.1(f) cusp parameter | `SourceInitialThetaData` 给定后，cusp 非零商、canonical generator、sign/diagram compatibility、derived orbicurve signatures/cover/open/exactness 逐项投影 | `proved(kernel)`；原文 cusp 的根层构造仍待完成 |
| D9 | 五组 arithmetic compatibility | source tuple 的两项 clause coherence 已投影；`SourceDefinition31Data` 的五组 arithmetic compatibility 尚未从 arithmetic input 构造 | `pending` |
| D10 | 完整 initial Theta-data | 已有 `all_six_clause_records`、`d10_complete_clause_records` 和显式 `d10_arithmetic_to_source_gate`；尚无 `InitialThetaArithmeticData -> SourceInitialThetaData` 全称构造 | `pending` |
| D11 | Definition 3.1 faithful conclusion | 给定 source tuple 时 `initialThetaData_conclusion`/`d11_source_conclusion` 完整装配且字段可恢复；无条件 `d11_faithful_conclusion_gate` 仍待证明 | `pending` |

### 11.3 每个节点的证明顺序和不可替代证据

#### D0--D2：算术根层

1. 先固定 `l` 的实例和 universe，不引入额外的 `Fintype`, `NumberField`,
   `IsGalois` 假设；这些必须来自原文 arithmetic input 的字段或 Mathlib 已有
   实例。
2. 对 `ThetaFieldTower` 的每个字段写独立投影定理：`sqrtNegOne_spec`、
   `degreePrimeToL_spec`、tower 的 scalar/action 实例和曲线字段。投影定理的
   目标必须是字段的类型，而不能写成字段证明项本身。
3. `ArithmeticData` 的 obligation 只能在所有这些字段从根层构造后改为
   `proved`；当前 `initialThetaArithmeticData` 仍然是 `interface`，因此 D2
   不得提前关闭。

#### D3--D4：places、reduction 和 q

1. 证明 place partition 的四个独立事实：`Nonempty Selected`、`Fintype Bad`、
   `badIncluded : Bad -> Selected`、label compatibility。`Fintype Bad` 是实例
   数据，不得从 `Nonempty Bad` 消去到类型；使用时通过局部实例或显式参数传递。
2. 对任意 `b : Bad` 依次关闭 stable、multiplicative、split；再证明
   `split -> multiplicative`。这些是逐处全称定理，不是一个存在坏处定理。
3. 由 `qParameter_nonzero` 证明 `0 < ||q||`，与 contracting 合成
   `||q|| in Ioo 0 1`。log 负性只在已有正范数和严格小于 1 后证明；不声明
   `q_log_abs_negative` 为输入字段。
4. 所有幂次、逆元、范数和对数辅助定理都放在 `RootReduction` 命名空间，作为
   D4 的可复用 consequences；它们不扩张原文对象的量词。

#### D5：torsion/Galois

1. 先定义真实 torsion carrier 和表示的目标群，再证明表示是同态；当前
   `ClauseC` 的源字段是 canonical representation、`image_contains_SL2`、
   `K_kernel_field_compatibility`、坏处互素、kernel finite-Galois 与连续性，
   不额外添加结构中不存在的“全表示满射/六扭点独立/l-compatibility”字段。
2. `image_contains_SL2` 必须从曲线和 Galois 表示的数学构造得到；当前
   `image_contains_SL2_proved` 只在给定 source tuple 后被消费，不能制造
   arithmetic-to-source 构造。
3. 表示 kernel 的乘法、逆元、幂闭包是普通群论可复用结论，标记为
   `proved(kernel)`；它们不等价于大像定理，不能改变 D5 状态。

#### D6：orbicurve 和 exact sequence

1. 先构造 `curve`, `puncturedCurve`, `cover` 和真实 cover map，并证明 cover
   map 的逐点满射及 cusp count 正性。
2. 再构造基本群的三条映射。对每个 `x : coverGroup` 证明
   `projection x = 1 <-> exists y, injection y = x`；两侧方向都必须出现，不能
   只证明 kernel 包含。
3. section 的右逆是独立字段，但必须证明其映射方向与原文一致；由右逆得到的
   section 单射和 split decomposition 只能作为 D6 的派生定理。
4. `residual x = x * section(projection x)^(-1)` 和 canonical kernel coordinate
   的 witness/uniqueness 是 D6 的第一组可审计根引理；`Classical.choice` 的
   axiom 使用必须在 audit 输出中列出。

#### D7--D8：section/local group 和 cusp

1. 对 valuation section 先证明左逆、右逆，再由 `Equiv` 得到单射、满射和双射。
   local-group map 在每个 `x` 上单独证明 injective/surjective，不能以一个
   未解释的全局 `Equiv` 替代所有处。
2. finite-place 和 infinite-place 数据必须保留为原文谓词；普通 section 的
   双射不自动证明这两个谓词。
3. cusp 先证明 `0 < epsilon`, `epsilon != 0`, `0 < cuspScale` 和原文兼容性，
   再定义规范化参数。`epsilon/cuspScale > 0` 是 D8 的派生结论，不应倒填成
   cusp 输入字段。

#### D9--D11：兼容性、装配和停止条件

1. 五组 arithmetic compatibility 必须分别关联到原文的 arithmetic/geometric
   maps；一个合取证书只能在五个独立定理完成后构造。
2. `SourceDefinition31Data` 的构造函数必须在其每个字段处给出 D2--D9 的证明；
   禁止 `exact` 一个同名的 structure/certificate 字段来绕过根层构造。
3. `toInitialThetaInput` 只能作为向 3.11 输入边界的忠实投影，不能反向用来
   构造 `SourceDefinition31Data`。
4. D11 关闭时必须同时提供：逐字段 theorem 列表、原文量词对照表、完整
   `lake build LeanFormal` 输出、`warning` 计数为 0、custom axiom 搜索为空、
   endpoint 的 `#print axioms` 记录。缺一项即保持 `pending`。

### 11.4 代码标记和审计记录约定

每个节点只允许一个状态标记，格式固定为：

```text
STATUS Dn: pending | interface | proved(kernel) | proved(source-faithful)
DECLARATION Dn: <fully-qualified Lean declaration>
SOURCE Dn: <原文页/行或 Definition 字段>
EVIDENCE Dn: <构建日志、#print axioms、量词检查文件>
```

命题关闭后立即在对应模块末尾写入 `theorem ..._status : True := by trivial` 仅作为
机器可检索的标记，同时在本文件更新表格；这个 `True` 不是数学证明，也不得取代
实际命题。任何失败的构建都不得将节点从 `pending` 改为 `proved`。

### 11.5 与 Theorem 3.11 的连接闸门

Definition 3.1 的 D11 关闭只是 3.11 的第一道闸门。其后仍按以下顺序推进：

* H1：由完整 source data 构造任意 distinct Hodge-theater family 和 D-Theta bridge；
* H2：构造 IUT I procession、F/D-prime-strips 及 arbitrary spoke permutation；
* K1：构造 IUT II vertical log-Kummer correspondence 的真实 carrier 和 maps；
* K2：构造 local/global Frobenioid、realification、MOD/mod 和 upper-semi 方向；
* P1：构造 III Props. 3.2/3.4/3.5/3.7/3.9/3.10 的 packet、degree、volume；
* P2：构造 III Theorem 1.5、Prop. 2.1、Cor. 2.3 所需的横向兼容性；
* T1：以原文相同量词组装 Theorem 3.11(i)；
* T2：组装 Theorem 3.11(ii)，逐项保留 nonarchimedean inclusion 和 archimedean
  surjection；
* T3：组装 Theorem 3.11(iii) 的 Theta-times-mu LGP-link/evaluation square；
* A1：单独构造 Corollary 3.12 Step (xi)，不能由 T1--T3 的名称推断。

只有 H1--T3 的每一项都达到 `proved(source-faithful)`，并通过同一份公理、
warning 和量词审计，才可以把 `theorem311Output` 从 `pending` 改为
`source-faithful proved`。本路线不承诺 Mathlib 自动提供这些 IUT-specific
构造；它的作用是防止前面已完成的根引理在后续重写中被遗忘或被误标为完整定理。

这一区分同时承认已完成的 Lean 数学工作，并拒绝把接口字段、上游包装或
有限示例误报为 Mochizuki 原文命题的证明。

## 12. 本轮 D0-D11 内核推进记录

本轮新增并接入 `IUTI/InitialTheta/SourceDefinition31RootLemmas.lean` 的
`Definition31StageKernel` 命名空间。新增内容按依赖顺序排列：

* D0-D2：继续保留数域塔、曲线、`sqrt(-1)`、有限维、Galois 和 `l` 的
  素数投影；修正了素数奇偶性、互素性和幂次 API 的显式参数方向。
* D3：使用实际 `NumberFieldPlace` carrier 及其 restriction section，证明
  finite/infinite place 的 comap/lift、selected image、injectivity 和
  finite-place residue characteristic 的逐点传递。
* D4：使用 curve-level good/multiplicative/stable reduction 谓词，证明
  stable = good ∪ multiplicative、两个子集包含关系以及每个 completed-DVR
  q-candidate 的非零、严格 valuation、正 order 和正幂闭包。这里仍明确不把
  q-candidate 解释成指定椭圆曲线的 Tate uniformization。
* D5：证明已给 representation 同态的 one/mul/inv/pow/zpow、surjectivity、
  kernel 的乘法/逆元/幂闭包，以及 torsion label、large-image 和
  independence 字段的逐项消费。这些是 supplied torsion datum 的 kernel，
  不是从 arithmetic curve 构造 Galois representation 的定理。
* D6：证明 exact sequence 的 projection/injection/section 群律、kernel
  iff、witness uniqueness、canonical residual decomposition，以及
  conjugation/action 的 identity、composition、inverse、bijectivity。
* D7-D8：证明 section/local-group 的双射与等价、finite/infinite place
  clauses、cusp 的正性/非零/规范化唯一性和比例恒等式。
* D9-D11：加入五项 compatibility 的独立投影/重组定理和
  `StageConstructionTrace`。trace 只有在每个 D2-D9 构造和证明已经显式
  提供时才可转成 `SourceDefinition31Data`，随后才可得到 D11 recognition。

本轮没有把上述 trace 的存在性从 `InitialThetaArithmeticData` 推出；因此
审计状态仍为：D2 `interface`，D3-D4 `interface`，D5-D10 `pending`，D11
`pending`。任何一次构建失败或 warning 都不得改变这些状态。下一次验证只在
完成本轮连续实质编辑后进行，并以 Lean 输出和公理审计为准。

### 12.1 本轮验证记录

本轮先修正 `stage_d5_kernel_pow` 的 `Nat` 归纳分支和 `Int.ofNat` 的
`zpow` 分支，随后串行执行：

```text
lake env lean LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31RootLemmas.lean
lake build
lake env lean verification/axiom_audit.lean
lake env lean verification/upstream_foundations_axiom_audit.lean
```

四条命令均以退出码 0 完成。`lake build` 报告 `Build completed successfully
(4312 jobs)`，没有 warning。两份 `#print axioms` 审计的声明级输出只出现
`propext`、`Classical.choice`、`Quot.sound`；没有发现 custom axiom、
`sorryAx` 或 `opaque`。这份证据只关闭了 D0/D1 的机器验证和各阶段已有
kernel consequences，不能关闭 D2-D11 的 arithmetic-to-source 构造闸门。

随后运行 `tools/check_no_custom_axioms.ps1` 和
`tools/check_axiom_boundary_logged.ps1`，两者均退出码 0；后者记录
`sorryAxLines = 0`。边界脚本已按当前源码状态更新为“零 `sorryAx` 才通过”，
不再把历史版本的 Step-XI 占位符当作生产允许项。

### 12.2 D3-D4 source-contract 根层验证（2026-08-11）

本轮新增 `IUTI/InitialTheta/SourceDefinition31D3D4Root.lean`，其输入是实际的
`SourceInitialThetaData l`，并按 D3、D4 顺序逐项投影原文字段：selected/moduli
place 的双射和 comap 兼容性、finite/infinite partition、坏处/好处的原文
分类与局部 exact-sequence/section 字段，以及 bad place 上 stable、multiplicative
reduction 和 valuation-theoretic q-candidate 的非零、严格估值、正阶和正幂闭包。
所有结论保持原始的 `∀`、`∃`、函数方向和有限/无限处区分；没有把
`FinitePlaceQCandidate` 宣称为指定椭圆曲线的 Tate uniformization。

该模块已接入 `LeanFormal/IUT/Project.lean`。串行证据如下：

```text
lake env lean LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31D3D4Root.lean
  exitCode = 0
lake build
  Build completed successfully (4313 jobs), warning 输出为 0
lake env lean verification/axiom_audit.lean
  exitCode = 0; 仅标准 propext / Classical.choice / Quot.sound
lake env lean verification/upstream_foundations_axiom_audit.lean
  exitCode = 0
tools/check_no_custom_axioms.ps1
  customAxiomDeclarations = 0
tools/check_axiom_boundary_logged.ps1
  exitCode = 0; sorryAxLines = 0; boundaryPassed = true
```

这组证据关闭的是 D3-D4 的 source-contract 识别与可复用根层推论，不能关闭
审计表中的 arithmetic-to-source 构造闸门；因此 D2、D3、D4 仍保持
`interface`，D5-D11 仍按“已给 source datum 的 kernel consequences/接口”
与“从原文允许输入的实际构造”严格区分。

### 12.3 D5-D8 source-kernel 与 D9-D11 装配验证（2026-08-11）

本轮新增并接入 `IUTI/InitialTheta/SourceDefinition31D5D8Root.lean`（1548 行）。
该文件按 D5、D6、D7、D8 顺序消费一个显式
`SourceInitialThetaData l`，逐项给出 torsion/Galois、四条 exact sequence、
finite/infinite local data、cusp/derived orbicurve、coherence、六组 clause
records 和 `InitialThetaDataConclusion` 的可恢复定理。section 只使用原文结构
提供的右逆，因此只推出 section injective；没有把它改写成 bijective 或
arithmetic carrier 上的满射。D10/D11 的两个 arithmetic-to-source gates 保持为
显式 `Prop`，并且要求产出的 source candidate 的 arithmetic 字段等于输入 `A`；
没有把存在性或结论结构当作无条件公理。

串行证据：

```text
lake env lean LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31D5D8Root.lean
  exitCode = 0; warning 输出为 0
lake build LeanFormal.IUT.Project
  Build completed successfully (4312 jobs); warning 输出为 0
powershell -NoProfile -File tools/check_no_custom_axioms.ps1
  customAxiomDeclarations = 0
powershell -NoProfile -File tools/check_axiom_boundary_logged.ps1
  exitCode = 0; sorryAxLines = 0; boundaryPassed = true
powershell -NoProfile -File tools/run_upstream_foundations_axiom_audit_logged.ps1
  exitCode = 0; sorryAxFound = false
powershell -NoProfile -File tools/check_source_text_audit.ps1
  passed = true
```

当前可关闭的是给定 source tuple 的 D5-D8 kernel consequences、D9 coherence
投影和 D10/D11 source-record 装配；D2-D4 的 arithmetic-to-source 以及 D9 五组
compatibility、D10 全称构造、D11 无条件 faithful gate 仍按表中状态保留，不能
由本轮的 projection theorem 越级关闭。
