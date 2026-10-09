# 有限行、实际能量与 canonical Batch 的源审计

这里保存 2026-10-09 的只读源审计与私有候选的历史记录。51 个源快照按原字节保存；metadata.json 绑定实际源码、公开 Git blob 和 LF 哈希。它们是当时的审查输入，不代表整个依赖环境已完成独立回放。

[audit.md](audit.md) 给出 actual positiveSlotRow 到总能量的精确接口、径向覆盖、NaturalState、任意 ray character、Schwartz 控制和损失预算，并定位 canonical Batch 尚缺的构造。特别保留 external 参数与 SupportedWitness.zero 的区别、全域 witness 与有限保留行的区别，以及四种 κ 的不同用途。

历史 Candidate 的真实编译和 fresh 类型/公理检查通过。它当时未作为上游目标，未做独立 kernel 回放；其命名空间、日志和状态保持原样。

正式实现见 [FinitePositiveRowDomination.lean](../../upstream/plain-kappa/extensions/files/OAI/NumberTheory/DirichletL/Moments/FinitePositiveRowDomination.lean)。正式模块的编译与独立回放状态以 capsule 的公开记录为准。有限行桥仍明确保留 keep 和径向覆盖条件，不等于完整 Moments 实例或新无零定理。
