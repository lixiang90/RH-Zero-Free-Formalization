# Canonical 中央行下界专项核对

`PrimeRows/CanonicalReduction.lean:33/:43–48 canonical_probe_minus_central` 将中央行明确取为 `rowBand (Z^(1/100)) (Z^(13/16+ζ))`。`CanonicalCubeReduction.lean:44 R`、`CanonicalCubeChoice.lean:42`、`CanonicalRayCube.lean:43/:56` 延续同一行集。`RowPartition.lean:36 mem_rowBand` 直接给 `u.val≠1 ∧ Z^(1/100)≤rowNorm u ∧ rowNorm u<Z^(13/16+ζ)`。因此这部分 **实际中央行已有下界**。

若后来构造的 source Batch 满足 `B.rows ⊆ 中央 rowBand`，则 `Batch.fiberRows` / `DetectorFiberPartition.fiber` 是 `rows.filter`，`Finset.mem_filter.mp hu` 的第一分量给 u∈B.rows，立即继承下界。随后可用 `NaturalFixedRaySourceFreeExceptional.lean:57 eventually_source_no_exceptional`（全 label 统一）排除 FixedInducingRow。此处无需再对中央行做低范数拆分。

现在 `PrimeRows/NonfloorCount.lean:14/:58` 仅对任意 B 给 **接受 Moments 实参** 的计数定理，并未返回 canonical source Batch。`DetectorBatch.lean:11` 的唯一 row 范围字段是 :17 上界；`DetectorFiberPartition.toFiber:91 row_norm` 也仅继承该上界。全源树搜索 `binWidth :=` / `widths_mesh :=` / `supply :=` 只找到 toFiber 构造，没有找到 canonical central→source Batch 的实例。需要补的明确连接是：按实际 source detector/witness、amplitude/zero/dyadic 标签构造 B，其 rows 是中央行的所用子集，证明 row_coeff/data/profile/widths/external 几何并供给完整 Moments；不能从 NonfloorCount 的泛量词冒认已有 canonical 构造。

小行确实已单独分出：`PhysicalPartition.canonical_physical_probe_partition:39` / `ExhaustivePartition.nonprincipal_rows_partition:11` 把非主行拆为 small、central、large；`CanonicalTails.lean:25` 控制 `rowBand 1 (Z^(1/100))`。它们使用旧 β≥7/8、∑ell=1/6、旧 X/Y 参数和预算；新参数路线仍需合法对应，不能把旧小行尾估计视为新尺度已完成。

本项只读核对，没有修改或新增 Lean 源、没有重复编译。
