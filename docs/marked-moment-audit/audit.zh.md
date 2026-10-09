# 实际 marked moment → count 接口只读审查（2026-10-09）

本记录只读审查实际 Lean 类型与函数；未新增、修改或编译任何数学源。文件中的“待证明”是实际数学接口缺口，不能作为新公理、已有构造或已完成的无零结论记账。审核对象为 `RH-Zero-Free-Formalization/tmp/upstream-plain`；部分 Energy 源属于冻结的 41 模块低 κ 补丁，实际依赖编译仍在进行。逐文件 raw/LF SHA 见同目录 `metadata.json`。

## 1. 最小第一门槛：实际平方和，而非抽象包络

`Hecke/DetectorPlainFiberCount.lean:13 plain_fiber_count` 已接受任意 `κplain ≥ 0`。令 `m = logb U (2^K)`、`z = 请求总 slot 长度`。输入是实际函数的全量估计：

```
∀ selected ⊆ slots,
  2m + 6 κplain (Σs∈selected widths s) ≤ 1 →
∀ j k, j+k ≤ 2 → ∀ σ∈[0,1], ∀ freq∈[-height,height],
  Σu∈rows ‖polynomial(χ u label,false,logProfile^j positiveAnnular,U^m,σ,freq)
            *polynomial(χ u label,false,logProfile^k positiveAnnular,U^m,σ,freq)
            *Πs∈selected physical(M,H,row,W,b,widths,zs,U,u,s)‖²
    ≤ C U^(1+εm).
```

它还需要实际 supported-witness、固定 label/dyadic indices、正 slot widths、mesh/供给和 amplitude bins，以及 `2π allowance + 3i T ≤ height`。结论是

`rows.card ≤ 192(1+height) C · U^(1−2(2a−1)m−2 weightedMean·z+4ε+(2a−1)mesh+εm)`。

此定理没有 `κplain ≤ 1` 前提。它无需修改即可使用新 **已证明实际** hraw；替换末端抽象 count envelope 不提供 hraw。

## 2. κ 名称的四种语义

| 参数 | 实际来源 | 作用 |
| --- | --- | --- |
| `D.κ` | `ParametersHighData.lean:16`，预算 :39–40；实际选择 `ParametersDetectorScales.lean:31` | detector 小损失。由预算及 ε≤1/1000 可得 ≤1/16000，不能当成 0.74 的谱参数 |
| `Moments … κ …` | `Hecke/DetectorRawFiber.lean:62–66` | 仅传给 `inverse_raw` 的 `RawMoment`；为逆多项式平方和的增长损失 |
| `κplain` | 同文件 `plain_marked:72–79` | 当前直接硬编码 `3/4+2Δ`，忽略上述 Moments 参数 κ |
| terminal κ | `Energy/CertifiedExistence.lean:40–45`；`Energy/PositiveHighPhysical.lean:39–41` | 角色族能量容量参数，要求 `37/50≤κ`、`51/100≤β`、`2β−1≤κ`；必须随真实 β 移动 |

最后一个参数已经可变，并不自动产生第三种参数的实际 marked moment。

## 3. 旧硬编码消费者与最小拓扑

- `DetectorRawFiber.Moments.plain_marked:72`、`DetectorRawBranches.Fiber.plain_marked_count:30` 固定容量 `6(3/4+2Δ)`。
- `DetectorBranchBudget.plain_marked_loss:36`、`plain_requested_capacity:60` 固定请求 `(1−2m)/(9/2+12Δ)−ν`。后者使用 `crossing_bounds` 与 dyadic-length 关系获得 `m≥1/4`，再保证请求 ≤ **现有总供给 7/37**。
- `DetectorCountFromMoments.count_from_raw_moments:12` 在 :76–86 选择该固定请求。它接受 Moments 实参，不构造 Moments。
- `DetectorRowCountCrossing.lean:8–18` 的 denominator/primeWeight/crossing/plainExponent，以及 :124 `capacity_loss`/:140 `plain_capacity_comparison`，使用基准 `1/(6·3/4)=2/9`。不能仅把分母替换成 `6κplain` 而保留旧 crossing 和包络结论。
- `DetectorRowCountOptimization.count_bound_of_source_branches:9` 消费固定分母分支，在 :57–68 使用旧 κplain≤1 的 zero-capacity 分支。
- 后续 `DetectorBatchCount:12`、`DetectorFixedAmplitudeCount:45`、`PrimeRows/NonfloorCount:14/:58`、`Detector/FinalAssemblyCountParameters:13` 继续接受 Moments 实参。`exists_count_parameters:49` 构造的是这些 **条件计数接口**，并不构造 hraw。

最小拓扑是：实际 marked hraw → 原 generic `plain_fiber_count` → 一般请求/损失 → 一般 crossing/优化 → batch/final assembly。首先应补 actual hraw；如果 κplain≤旧值，可用容量单调性接回旧 Moments，但这样不会利用改进后的计数收益。

一般请求至少需正 `κplain`、请求非负、请求≤现有供给、容量满足；不能只改系数。仍有 `m≥1/4` 时，保证最大请求 ≤7/37 的充分条件是 `κplain≥37/84`，故 0.74 在该检查上有余量。若新 crossing 改变 m 的下界，必须重新验证。

## 4. 已有 fiber/batch 扇区接口的精确边界

`Moments/NaturalFixedRaySourceFiber.lean:68 fiber_plain_sector_energy` 需要：

1. `F.rowData = momentData η₀`；
2. `M ≤ span {rowMaskElement}`，`0<U`；
3. selected 的相关 primePool 中，profile 非零的 prime 与 η₀.modulus 互素。

它对任意 selected、j、k、σ、t（比 j+k≤2 的目标范围更宽）只证明

`目标有限平方和 ≤ Σθ ‖averageWeight‖ · Σu∈F.rows ‖fiberSector θ u‖²`。

没有数值 C、指数 1+εm、容量限制或实际矩上界。`NaturalFixedRaySourceProduct.lean:49 averageWeight_mass` 已给 Σθ‖weight‖=1；若所有扇区真的有同一个 CU^(1+εm) 上界，平均这一步已足够。

`Moments/NaturalFixedRaySourceBatch.lean:20 eventually_source_batch_plain_sectors` 的事件在 Z 前固定 S、η、ell、W，之后量化 **所有 d≠0、所有 batch、所有 fiber、所有 selected/j/k/σ/t**。它需 batch.data=sourceMomentData、batch.widths=ell/d、batch.profile=W，及 W 的正 support。`sourceData_batch_gate:56` 对现有 SourceData/HighData 做同样扇区归约。它们通过 `eventually_source_slots_coprime` 实际获得所需互素性；依然不提供扇区的数量上界。

## 5. PositiveHighAt / actual_positive_high_physical 不能直接供给全量 plain_marked

准确接口是 `Energy/PositiveHighSourceBound.lean:49 PositiveHighAt`，没有额外的 `actualPositiveHighAt` 别名或已构造实例。它是一个 **Prop 定义**：

- 固定 W、公共 bslot、支持区间、lo/hi、能量 cap、ε、κ、η₀、Q、有限控制 seminorm 集/degree/C；
- 对 selected T、ray θ、非负 widths w≤Lslot、slot σ∈[lo,hi]、slot freq 有界、NaturalState、Profiles、X₁/X₂ 全量化；
- 必须有 state.fixedModulus=internalQ Q η₀、`rho≤state.width≤Mcap`；
- 容量 `length Z X₁+length Z X₂+6κ Σw≤state.width`；
- **另有高带条件** `5 state.width/6≤length Z X₁+length Z X₂+Σw`；
- 结论控制径向 **无限实际 energy**，右边含 `C·diagonalControl(radial.profile)·p.control(S)²·(1+|t|+height)^degree·Z^(state.width+ε)`。

`Energy/PositiveHighPhysical.lean:30 actual_positive_high_physical` 是实际定理，但在结论内部显式接受 **ZeroAt child** 和 **PositiveAt child**，只构造 `PhysicalHighAt`。后者还要求 balanced input 的四尺度≥Z^(state.width/4)。`actual_high_stage_from_physical:66` 再需要 `PositiveLowAt` 才合成 `PositiveHighAt`；`positive_from_stages:135` 需要 old/small-width、low、high 三块，才得到 `Bands.PositiveAt:39` 的完整容量覆盖。

因此仅有高带定理不覆盖 Moments.plain_marked 的全部容量量词；小 width 和低带不能省略。完整供给的实际来源应为 `CertifiedExistence.terminal_certificate` + `CappedWidthInduction.certified_terminal:94`（尚须实际依赖编译/审验完成），它们内部建立 child，而不是把 child 新增为最终结果的永久假设。

## 6. 最小连接宜优先绕过逐扇区，而不是再加条件包装

更短的现有接口是 `Moments/DetectorDictionaryFiber.lean:27 fiber_plain_energy_eq`：目标平方和 **等于** `Σu∈F.rows ‖detectorPositiveRow F η₀ … u‖²`。`detectorPositiveRow:18` 已用与 `Bands.PositiveAt` 相同的 ray primePool。

`DetectorDictionarySlots.lean:23 physicalSlotCoefficient_annular` 精确给

`physicalSlotCoefficient η₀ W P external = idealCoeff η₀.inverse · annularWeight (conj W) P (1−external.re) (−external.im)`。

在 identityClass primePool 上，不仅平凡 θ，任意 `θ : RayQuotient.Characters M H` 的 idealCharacter 都应为 1：identityClass 给存在 generator，其 residue 在 H；可沿 `IdealCharacter.ofResidue_of_generator` 与 `mem_characters_iff` 实际证明（尚未找到现成组合 lemma）。于是任意 θ 的 relativeCharacter 系数都与 η₀.inverse 匹配。真实 source W 来自实值 w，conj W=W。这个加强的系数恒等式仍需实际 Lean 补齐，本审查不把它列作已完成证明；使用平凡 θ 已足以建立最短连接。

与此相比，`fiberSector` 的 slot 是全 `primePolynomial`（经 ray average 展开），而 `PositiveAt` 的 slot 是 identityClass `primePool`，两者不是可以直接 `exact` 的同一函数。若坚持扇区路线，还须证明 whole-prime sector 到对应能量接口的实际等式/比较；可以优先避免此额外桥。

## 7. 最小待证明清单与真实前提

1. **实际 batch 几何与行域**：明确 canonical source batch，而非任意 Batch 的自带字段。需要 rowData/sourceMomentData、widths=ell/d、公共 source profile/upper（或证明不同 upper 的合法传输）、external.re 在固定紧区间、external.im 的统一高度界。现有 Batch/Fiber 没有这些 external/upper 界。
2. **非例外与 NaturalState**：固定 `Q=sourceFixedIdeal`，取真实 source label η₀，构造固定径向 bump、keep 和 row/character widths。证明原 fiber 有限行被实际非负径向权 ≥1 覆盖，并且 keep 排除 FixedInducingRow、row≠0，modulus/scale/fixedModulus 等满足 State 字段。已有 `sourceFixedIdeal:16` 的非零/非顶/≤72 证明，以及 `eventually_source_no_exceptional:57` 可在 rowNorm≥Z^(1/100) 的实际范围供给非例外；如保留更小行需分块或估计例外贡献，不能假定它们没有例外。
3. **容量和 mesh 的统一变换**：U=Z^d、fiber widths=ell/d、X₁=X₂=U^m。需证明 `2dm+6κ Σell≤state.width`，真实 norm/mask margin 会改变 state.width，故需 padding 或额外余量。新 slot-length 构造可以在 mesh/d 区间固定后选择 N，但不自动证明该容量式。
4. **完整能量供给**：使用真实 terminal certificate/certified_terminal 的完整 PositiveAt；不能仅给显式 ZeroAt/PositiveAt child 条件然后声称完成。固定 κ 必须满足 moving β 条件 `2β−1≤κ`、β≥.51、κ≥.74。
5. **实际函数/归一化连接**：fiber_plain_energy_eq → identityClass 上任意 ray coefficient identity（平凡 θ 足够）→ 有限平方和≤径向实际 energy。保持 positiveSlotRow 的归一化，不能另建抽象 envelope 或替代 polynomial。
6. **全部标记和频率量词/常数**：一个 C 与阈值必须固定在所有 selected、j+k≤2、σ∈[0,1]、t∈[-height,height]、有限 label/bin/dyadic fibers 之前；必要时固定 N 后由有限个根和统一 seminorm 合并。`NaturalFixedRaySourceDetectorProfile:50 detectorNormProfile_uniform` 已覆盖 reverse/n≤2/σ∈[0,1] 并给频率的多项式控制；它仍留下 `(1+height)^J`，必须吸收，不能默认为常数。
7. **损失预算及量词顺序**：目标是 Z^(d+d εm)。若能量给 Z^(state.width+εE)，需实际证明 `state.width+εE+高度/固定常数吸收损失≤d+d εm`。要对 d 统一，需固定正区间 dmin≤d≤dmax；batch 扇区归约的 ∀d≠0（含负 d）不能直接当作 energy 上界的域。degree/控制集先由真实 energy 得到，再选择 τ、height=Z^τ，并在选 N/slot 后保持最终 C/阈值对所有所用参数统一。
8. **消费新 κplain 的计数链**：hraw 真正完成后复用 generic plain_fiber_count，推广请求/损失/crossing/count envelope 与 batch 最终接口；并单独供给 Moments 的 inverse_raw、inverse_marked、plain_unmarked 三字段。仅供 plain_marked 不构成完整 Moments。

上述几何/非例外/mesh/高度/容量是需要从 canonical source 对象推导的真实前提，不是允许新增公理。若采用带前提的局部比较定理，应清楚记录其前提尚未由 source 构造供给；不能将同义的 hraw/完整 Moments 作为新“证明”输入。

## 8. κplain≤1 仅是下游分支限制及可修边界

`DetectorRowCountCrossing.plain_zero_capacity:167` 需要 κplain≤1，将请求≤ν 推为 `1−2δm≤1−δ+6δν`。旧优化以 Δ≤1/8 得 `3/4+2Δ≤1`。泛化成 κterminal+padding 后，κterminal≤1 本身不够；若只知道 β≤1，padding>0 可能使 κplain>1。可选择并证明严格余量/已有 β≤7/8 bootstrap，也可保留系数 `6κplain δν` 重新做下游误差预算。后者需真实常数上界；无限 κplain 不会保持旧固定 6ν。

这不限制上游 generic plain_fiber_count，也不是更强 marked moment 不可能的证据。

另 `plain_capacity_bound:104` 的 2/27 上界要求 κ≥3/4；在 m=1/3、κ=.74 时请求=25/333>2/27。搜索未见实际消费者，但若后续调用，必须改精确上界，不能沿用旧值。

## 9. 本次结论与状态

同对象的 direct fiber-energy 连接比逐扇区更短，尚需 7.1–7.7 的实际数学构造及完整量词/损失闭合。当前高带接口、扇区归约、条件 CountParameters 不能单独构造 Moments.plain_marked 或完整 Moments。全源树只读搜索未找到 `plain_marked :=`/`inverse_raw :=`/`Moments.mk` 的实际构造；这是检索证据，不替代编译或不可达性证明。

未新增冻结数学源，未修改 41 OAI 补丁/11 authored 源/原数学仓库/主库。六个 owned 模块的实际编译与 43-root fresh/Nano 审验继续由已有流程接应。

## 10. identityClass 系数原型后续只读审查

Root 已实际编译同目录 `IdentityClassCoefficient.lean`，全类型/公理输出只含标准三公理；本审查仅再次核对其数学内容。证明正确：identityClass 的非零理想/generator/unit residue 在 H 数据，经实际 `ofResidue_of_generator` 重写，再用 `mem_characters_iff` 得 χ(u)=1。该根不含额外无零、tail 或循环前提。

因此 direct detectorPositiveRow→PositiveAt 中可以使用 **任意 θ**，不再需要 θ=1 限制：原 `relativeCharacter_ideal` 加 `idealCoeff_character` 后，identityClass 上 ray 因子=1，剩下 η₀.inverse。无需额外 η₀ 在该 ideal 非零条件，若 η₀ 系数为0仍为正确等式。

这一原型仍未进入 11 冻结数学模块/13 target/Nano 成果；它只解决系数身份这一步，不解决径向行比较、容量/mesh、完整高低带、统一高度损失，也不把 whole-prime fiberSector 变成 ray primePool。

## 11. Canonical 中央行域已有下界，batch 实例仍待连接

`PrimeRows/CanonicalReduction.lean:33/:43–48 canonical_probe_minus_central` 实際將中央行取為 `rowBand (Z^(1/100)) (Z^(13/16+ζ))`；`CanonicalCubeReduction:44 R`、`CanonicalCubeChoice:42`、`CanonicalRayCube:43/:56` 延續該行集。`RowPartition:36 mem_rowBand` 自帶 `u.val≠1 ∧ Z^(1/100)≤rowNorm u ∧ rowNorm u<上端`。所以 **canonical central 部分无需另拆更小行**，可在實際 batch.rows⊆中央 rowBand 證明完成后，经 fiber 的 filter 继承下界，再调用 `eventually_source_no_exceptional:57`。

`NonfloorCount:14/:58` 只有 ∀B、接受 Moments 的條件計數，未返回 canonical source Batch。Batch/Fiber 只自带行范数 upper；全树 binWidth :=、widths_mesh :=、supply := 唯一实际构造在 `DetectorFiberPartition.toFiber`，未找到 canonical central→Batch 的实例。缺口是构造采用真实 source family/witness/标签与 slot geometry 的中央子集 batch，并证明其实际矩与全量量词，不能把 generic Batch 的上界當成既有中央行域。

小行已由 `PhysicalPartition.canonical_physical_probe_partition:39` / `ExhaustivePartition.nonprincipal_rows_partition:11` 单独分开，`CanonicalTails:25` 控制 `rowBand 1 (Z^(1/100))`。这仍是旧 β≥7/8、∑ell=1/6、旧 X/Y 尺度与预算的接口；新参数要实际适配，不能自动沿用，尤其 β>σStar 不自动给 β≥7/8。专项细节另见 `canonical-row-domain.md`；本节后冻结本次 review 记录。
