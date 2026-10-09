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

FiniteLabelPositiveAtLowKappa 的已验类型先固定有限 eta/Q maps，再存在 degree/S 和共同常数。RawMomentInput 还要求 degree 先于所有 eta 的更强量词顺序；后续须直接使用原生 terminal certificate 证明该统一性，不能仅从当前有限族类型推出。

## 下一步实际供给

1. 用已证明的 ActualSourceBatchTotal 作用于实际保留行与 detector maxima，供给其校准、行增长、margin 和 mesh 条件。再证明共同窗口与 upper、素理想互素和实际 external 的界。
2. 接合已构造的有限标签 PositiveAt、fiber 字典和 NaturalState。需要保留 β≥51/100、κTerminal≥37/50、2β−1≤κTerminal，以及 internalQ 的实际条件。κPlain 的 padding 与 terminal κ 要满足真实容量比较。
3. 应用已证明的有限标签统一与高度吸收；在 certificate 的 degree/S 和 profile 的 J 确定后选择高度指数 h，使

       ρ + εE + h*(degree+4J) ≤ dmin*εm.

   εm 是 Moments 中独立的正实数。实际测试频率和 external 高度均需共同界；i≤I 的固定因子进入共同常数。由此才能从 Z^(d+ρ+εE) 推出 U^(1+εm)。源参数 τ 可取满足 h=2τ 的值，其选择先于后续 tail order。
4. 把实际 marked sum 交给 generic plain_fiber_count，统一修改下游分母 6κPlain、crossing 和 count 优化，并分别供给 inverse_raw、inverse_marked、plain_unmarked。旧 Moments 的 plain_marked 固定 3/4+2Δ；其 inverse 参数不能替代新的 plain κ。
5. 完成 variable lx/ly/total 的实际 reflected-energy 和 small/floor/outer estimates，组装完整 low/raw-high probe，并在一个固定 Lean 环境中验证最终算术结论。

[完整源审计](finite-row-energy-audit/README.md) 保存 canonical Batch 尚缺条件的实际源码和历史候选记录。ArithmeticProbeObligation 仍需完整 marked moments、改进 count 和实际 low/raw-high probe 的证明供给。
