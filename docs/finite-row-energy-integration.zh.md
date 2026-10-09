# 有限行检测器到实际正能量的接合

这些模块使用 OpenAI/math 的实际 Hecke 多项式、primePool、positiveSlotRow、Schwartz profile 和 NaturalState。验证范围与独立回放记录见 [算术 capsule](../upstream/plain-kappa/README.md)；本文说明接口和下一步需要供给的条件。

## 已构造的证明部件

| 模块 | 实际作用 | 仍显式保留的条件 |
|---|---|---|
| FinitePositiveRowDomination | 将实际有限行正平方和嵌入同一归一化的总 energy；从 product_bounded 导出可求和性。 | keep 包含所选行，径向权在这些行等于一，权非负，正尺度与实际 plain profile 支撑。 |
| FixedRadialRowDomination | 对固定 b>0 先选一个 Schwartz 函数，再对所有有限行、字符、slots 和尺度给出上述控制。 | 行理想范数不超过 bK；keep 包含这些行。 |
| FiniteFamilyNonexceptional | 用实际分子赋值和有限例外行论证，对任意固定有限字符/理想族取得统一的大行非例外事件。 | Q 非零、非全环、Q≤span{72}、Q≤η.modulus，固定正行增长指数。掩码的非零、goodLambda 与 2 整除条件。 |
| FiniteRowNaturalState | 先选共同径向函数，随后实际构造 NaturalState Z 0 2；保留行谓词恰为给定有限行集。 | 上述固定理想条件，rmin>0、ρ>0，以及 Z^rmin≤rowNorm≤Z^d、d≥0。 |
| FiberRelativeEnergyBridge | 把实际 fiber 的两个 plain 多项式与 physicalProduct 的平方和接到任意 ray character 的相对 energy。 | 实际 rowData 字典、M≤span{rowMaskElement}、非零 profile 对应的素理想互素、共同 profile/upper、径向覆盖。 |
| FiniteSupportedWitnessRetraction | 将非空有限行上的真实 SupportedWitness 延到 FreeRow 全域；原有限行上的整个结构以 HEq 保持。 | 有限行非空以及已供给的真实有限见证。 |
| DetectorPairControl | 构造两个实际 detectorSchwartz 组成的 Profiles，并统一控制其 control 的平方。 | 半范数集先给定，随后 J、C 先于 reverse、j/k≤2、σ∈[0,1]、t。 |

FiniteRowNaturalState 的共同 profile 等于一于 [0,1]，支撑在 [-1,2]，实部非负且虚部为零。对于 U=Z^d，状态的 rowWidth=d、characterWidth=ρ、width=d+ρ、radial.scale=U、puncture=1。保留行均非零且非例外；固定有限字符族的导体界统一由 Z^ρ 吸收。其掩码仍是实际 fixedBadMask*idealGenerator(1)，不把 idealGenerator(1) 当作字面上的一。

Witness 延拓取一个回缩 r:FreeRow→rows，R 外映到一个 R 内元素，R 内保持恒等。全域 family=χ∘r，W(u)=w(r(u))。有限行上完整 witness 的 HEq 保留 label、zero、dyadic 区间、长度和证明字段。空行集应走单独的零和分支。

## 精确的字典与损失

在实际 identityClass primePool 上，每个 ray quotient character 的理想系数都是一，因而

    idealCoeff(relativeCharacter η θ, P) = idealCoeff(η.inverse, P).

FiberRelativeEnergyBridge 保留实际 F.external 的参数：slot profile 为 conj(W)，实部参数为 1-Re(F.external)，频率为 -Im(F.external)。plain profile 使用原有 orientedProfile 与 orientedFrequency。energy 的时间参数为零；plain 多项式中的测试频率已写入两个 Schwartz profile。F.external 与 SupportedWitness.zero 是不同对象。

DetectorPairControl 对实际 p=detectorPairProfiles 证明

    (p.control S)^2 ≤ C^4 * (1+‖t‖)^(4J).

两个 sourceControl 相乘后还要平方，频率指数因此是 4J。J、C 先于所有 profile 参数；它们不随所选有限行或高度变化。径向函数也先固定，其 diagonalControl 可以进入共同常数。

## 从实际 source Batch 到终端上界

ArbitraryTotalSourceBatch 保留原 Batch 的真实 supply=7/37 条件。对 Lambda>0、d>=dmin>0、sum(ell)=Lambda、ell_s<=dmin*mesh，条件 d<=37*Lambda/7 推出所有宽度 ell_s/d 正且不超过 mesh，并满足 supply。retainedSourceBatchTotal 调用原实际构造，保留已供给的 SupportedWitness。

ActualSourceBatchTotal 进一步调用原 supported_witnesses_from_source_cube，实际构造 Batch 并证明 rows、data、reverse、slots、widths、profile、upper、external、mesh、binWidth 和有限行 family 的完整字典。它保留中央行带、校准非零、rowNorm<=Z^(d-margin)、检测器 current/next maxima、a>51/100 及原见证预算

    12e*(22+2) + 8*kappa_w + 2*heightCost <= epsilon/2.

这里 kappa_w 是小见证参数，和能量的 kappaTerminal 分别使用。总长度只在 supply 推导中参与；新的 dmax<=37*Lambda/7 替代原 dmax<=37/42。原窗口和 external 仍可指定，实际使用时要给出统一 profile/upper 与高度界。

FiberPositiveAtLowKappa 将真实 PositiveAt 应用到同一个 marked square sum。FiniteLabelPositiveAtLowKappa 在固定有限 eta/Q 族上从真正的 terminal certificate 构造 PositiveAt，并统一常数与 atTop 阈值，包含空标签集。它没有要求调用者另给 CertifiedBand 或 PositiveAt。

MarkedHeightBudgetLowKappa 先选 rho、epsilon_E，再对 degree/J 和任意正 ceiling 选 tau。若 external 高度和测试频率均不超过 Z^h，则已证明

    rho + epsilon_E + h*(degree+4J) <= dmin*epsilon_m

足以把 energy 上界的两个高度因子吸收到固定常数乘 U^(1+epsilon_m)，U=Z^d。对源事件常取 h=2*tau，已证明的选择预算相应为 rho+epsilon_E+2*tau*(degree+4J)。这个确定性吸收不供给实际高度不等式本身。

SourceMomentsAt 要求对每个满足实际 source 字典的 q、Batch 及非空 fiber 供给完整 Moments。这是固定 source 数据下的全称接口；只证明某一个选定 Batch 不够。完整 Moments 的 inverse_raw、inverse_marked、plain_marked、plain_unmarked 四个字段仍须分别供给。

FiniteLabelPositiveAtLowKappa 的已验类型先固定有限 eta/Q maps，再存在 degree/S 和共同常数。UniformDegreePositiveAtLowKappa 已直接从原生 terminal certificate 证明 degree/S 先于所有 eta/Q 的统一性；这个独立结果没有改变有限族整合定理的量词。RawMomentInput 的完整四字段接口还要求共同次数先于所有 eta、各 C_eta 先于任意 tau，仍须在 source 装配中保留这些顺序。

PlainMarkedAdmissionLowKappa 已从真实容量 2m+6*kappaPlain*sum(widths)<=1 和 kappaEnergy<=kappaPlain 推出原生能量容量。F.lengths 供给 m>=0；kappaPlain>=0 进一步给 m<=1/2，再由 d/2<=L 供给真实多项式长度 cap。

EventualFiniteSourcePlainMarkedLowKappa 对固定有限 eta/Q 族实际构造 PositiveAt 与 NaturalState，统一正 Ctotal=max(1,C*Cp^4*diagonalControl(Phi)*2^(degree+4J)) 和 atTop 阈值，供给所有满足行下界、source 字典、共同 profile/upper、互素、scaled mesh、external.re=17/50 与高度条件的 fiber 的 marked 上界。rho 在 Mcap-dmax 的正余量内选择；tau 随后支付精确 2*tau*(degree+4J) 费用。该定理的族仍在 degree/J/tau 之前固定；它与下述更强的全称源包装分别核验，类型没有被悄悄加强。

UniformHeightSourcePlainMarkedLowKappa 已独立核验真正更强的顺序：固定 Slot 后，先选择 rho/epsilon_E、degree/J 和共同正 tau，再对任意有限 eta/Q maps 选择 Phi 与正 Ctotal。这个 Ctotal 和同一个 atTop 阈值先于所有 0<tau_prime<=tau，预算由单调性支付；它没有把原弱有限族定理的存在量词交换。该结论只供给 one-field 和有上限的高度范围，不等于完整 RawMomentInput 的四字段及任意 tau<=1。

LossesBeforeSlotSourcePlainMarkedLowKappa 已直接证明损耗先于任意有限 Slot 类型的顺序：固定算术源与 W 后先选正 ρ、εE，再对任意 Slot 选择 degree/J/共同 τ，随后对有限 η/Q maps 选共同常数与 eventual 阈值。这里保留真实的原生能量构造，没有交换旧定理的存在量词。

GenericSourceIdealAndMesh 从实际素集 S 和 M=product(S) 推出非零、proper 与 internalQ 条件。Q0=M⊓span{72}；internalQ≤span{72} 与 internalQ≤η.modulus 是并列两界，不宣称 span{72}≤η.modulus 或 Q0≤η.modulus。实际 source_product_le_rowMask 另供 mask 条件，由全称包装组装。它按绝对能量 fineMesh 与 Batch 的 scaled mesh 同时选择任意正总长度的 distinct ell，证明实际 fiber 的 d*width=ell。绝对条件 ell≤energyFineMesh 与 ell/d≤batchMesh 分别保留。

SourcePlainMarkedUniversalLowKappa 将这些部件接到真正的 source 字典。固定素集 S、product ideal M、H 和共同 W 后，量词顺序为

    标量损耗 ρ/εE → fineMesh → N/ell/slotLower → Slot=Fin N
    → degree/J/共同 τ → 任意 outer η → 正 Cη/eventual Z
    → 任意 0<τ′≤τ、实际行集、q、所有匹配 Batch 和非空 fiber。

它从真实 source 条件推出 rowMask、互素、共同 profile/upper、external、绝对 ell mesh 与行上下界，实际构造 NaturalState 和 PositiveAt，再得到移动 κ 的 plain_marked 上界。没有把最终平方和、PositiveAt、CertifiedBand 或 NaturalState 作为整个结论的替代输入。全称范围覆盖所有匹配 Batch；这些 Batch 的存在性仍由 ActualSourceBatchTotal 在其真实检测器前提下另行供给。这仅是一字段与有上限的高度接口，不等于完整 SourceMomentsAt 或 RawMomentInput。

PlainUnmarkedAdmissionLowKappa 已另行证明正确的无标记准入。真实 Fiber.lengths 允许 m≤1/2+75ε；取 selected 为空后不再附加 marked 容量，因此没有 m≤1/2 限制。原生 rowWidth 改为 d*max(1,2m)，总 state.width=d*max(1,2m)+ρ，得到指数 U^(max(1,2m)+εm)。该准入保留真实 PositiveAt、state.width≤Mcap、径向覆盖/keep/profile 与多项式 cap d*(1/2+75ε)≤L；它还没有为所有源纤维构造这个放大状态和统一 cap。

若 0≤ε≤εmax，则 max(1,2m)≤1+150εmax。因此可用

    dmax*(1+150εmax)+ρ≤Mcap，
    dmax*(1/2+75εmax)≤L

建立源族的统一容量。marked 所用的 L≥dmax/2 不足以支付正 ε 的统一多项式余量；下一构造需要实际正余量或更强的 L。

[实际 source 包装审计](source-plain-wrapper-audit/README.md) 列出 q、Batch 和非空 fiber 的全称范围，以及绝对槽长 ell<=energyFineMesh、外部高度与素理想互素等真实准入门槛。

## 下一步实际供给

1. 该关键顺序接口现已补齐。LossesBeforeArithmeticSourcePlainMarkedLowKappa 先从标量预算构造 ρ/εE，再引入任意 M/H 与有限 Slot；SourceAfterSlotsPlainMarkedLowKappa 随后证明 ρ/εE、mesh、N/ell → 任意后给的正 detector e 和 prime seed → 实际 SourceExclusions 与 FirstTail(4e) 的最终 S → 非零 product ideal/H → degree/J/共同 τ → outer η 的常数/eventual 阈值 → 所有匹配 Batch 和非空 fiber 的 marked 上界。这里的 e 是检测器参数，区别于总槽长和能量误差 εE。它接受以后按槽预算选好的真实 e，不构造完整 HighData 的其余预算；没有交换旧存在量词。保留原字节的 [历史装配顺序审计](source-assembly-order-audit/audit.md)与[后续证明状态](source-assembly-order-audit/README.md)分别说明旧缺口和新接口。
2. 将已验的 ActualSourceBatchTotal 实例化到真实 retained rows、detector maxima、校准、行增长和 margin；完成 source-wide plain_unmarked 的放大 NaturalState 与上述统一 cap，同时分别供给 inverse_raw、inverse_marked。完整四字段记录仍未构造。
3. 把已验的全称 marked sum 交给 generic plain_fiber_count，统一修改下游分母 6κPlain、crossing 和 count 优化。保留 β≥51/100、κTerminal≥37/50、2β−1≤κTerminal 与 κTerminal≤κPlain；旧 Moments 的 plain_marked 固定 3/4+2Δ，其 inverse 参数不能替代新的 plain κ。padding 后的 κ 上限也需真实 bootstrap/margin。
4. 完成 variable lx/ly/total 的实际 reflected-energy 与 small/middle/floor/outer estimates，组装完整 low/raw-high probe，并保留共同高度先于后续 tail order。当前界只涵盖 0<τ′≤共同 τ，不自动给出旧 RawMomentInput 的任意 0<τ≤1。
5. 实例化完整有限阶 Hecke 族及其延拓结论，并在同一固定 Lean 环境中验证最终算术定理。

新的[三个源顺序声明](../upstream/plain-kappa/verification/source-after-slots3/strict-replay-result.json)已通过正式编译、完整类型/传递公理审查和独立内核回放；本轮不增加新边界或无条件无零结论。

[完整源审计](finite-row-energy-audit/README.md) 保留实际源码与历史候选记录；[两批新增证明记录](../upstream/plain-kappa/verification/generic-losses4/strict-replay-result.json)与[全称源/无标记准入记录](../upstream/plain-kappa/verification/source-universal-unmarked3/strict-replay-result.json)分别核验本轮四根和三根。ArithmeticProbeObligation 仍需完整 Moments、改进 count 与实际 low/raw-high probe，尚无已证明的 inhabitant。
