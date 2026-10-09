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

## 下一步实际供给

1. 从真正的中心 rowBand、source family 和 detector witnesses 构造 canonical Batch，证明 source coefficient/data 字典、宽度 ell_s/d、共同窗口与 upper、行范围和实际 external 的界。有限 witness 回缩解决类型延拓，不供给这些有限见证本身。
2. 用完整低 κ terminal certificate 供给实际 PositiveAt，再应用 fiber 字典和已构造的 NaturalState。需要保留 β≥51/100、κTerminal≥37/50、2β−1≤κTerminal，以及 internalQ 的实际条件。κPlain 的 padding 与 terminal κ 要满足真实容量比较。
3. 统一有限 source labels 的常数和阈值；在 certificate 的 degree/S 和 profile 的 J 确定后选择高度指数 τ，使

       ρ + εE + τ*(degree+4J) ≤ dmin*εm.

   εm 是 Moments 中独立的正实数。实际测试频率和 external 高度均需共同界；i≤I 的固定因子进入共同常数。由此才能从 Z^(d+ρ+εE) 推出 U^(1+εm)。τ 的选择先于后续 tail order。
4. 把实际 marked sum 交给 generic plain_fiber_count，统一修改下游分母 6κPlain、crossing 和 count 优化，并分别供给 inverse_raw、inverse_marked、plain_unmarked。旧 Moments 的 plain_marked 固定 3/4+2Δ；其 inverse 参数不能替代新的 plain κ。
5. 完成 variable lx/ly/total 的实际 reflected-energy 和 small/floor/outer estimates，组装完整 low/raw-high probe，并在一个固定 Lean 环境中验证最终算术结论。

[完整源审计](finite-row-energy-audit/README.md) 保存 canonical Batch 尚缺条件的实际源码和历史候选记录。ArithmeticProbeObligation 仍需完整 marked moments、改进 count 和实际 low/raw-high probe 的证明供给。
