# PrimeMother TODO：Lean 状态与完成路线

审计日期：2026-10-07（UTC）  
审计基线：`master` @ [258fb757f4712b18ce45310bbebbd34e9dc9226d](https://github.com/cchx0000/primemother/commit/258fb757f4712b18ce45310bbebbd34e9dc9226d)

## 当前结论与验证边界

当前仓库是**一元 prime-birth 的算术模型与未完成证明骨架**，还不是论文全部结论的 Lean 形式化。

- 已逐个检查全部 3 个证明源模块（不含 `lakefile.lean`）、Lake 配置/锁文件、论文的主要结论及其依赖
- 源码中有 2 处显式 `sorry`：`Def_PrimeMother_Atlas.lean:78` 和 `Thm_PrimeMother_PrimeBirth.lean:76`；这不是仅删除两个占位符即可完成，主定理另有 API、归纳索引和整除证据接线错误
- 3 个模块中未见显式 `axiom` / `admit` 声明。出生定义没有调用 `Nat.Prime`，递归依赖严格更小的 `m`，未发现把最终结论作为显式假设输入的循环；但尚未通过内核依赖审计，不能据此称“无公理/无 sorry”
- `Prefix := Nat`、`rk H := H`、`HasRegAtlas H Pi := ∃ r ≥ 2, rk Pi * r = rk H`。这些是秩模型的定义；`clock_reconstruction` 的 `rfl` 不是抽象无标签路径的唯一 order isomorphism 证明，两个 atlas-rank 引理也不是实际分块/路径同构的构造
- `birth_iff_prime` 的声明仅带 `2 ≤ n`，但证明未完成；论文的有限联合 birth、return source、无限边界与唯一 provenance 等价类均无对应 Lean 实现
- 本次**没有运行 Lean/Lake 编译或测试**。基线提交说明只声称 Atlas 编译且保留 1 个 `sorry`，不是整库构建收据。基线没有 `.github/workflows`；查询 Actions runs、该 SHA 的 check-runs 与 commit statuses 均为空
- 已固定 Lean `v4.33.1` 与 mathlib `0df444a360eaa60ab8c11dca51a86af692955474`；已核对该 mathlib 提交的 `lean-toolchain` 也是 `v4.33.1`，未发现版本针本身不匹配
- 基线无 README、根目录 `todo.md` 或仓库级操作说明。本文件新增计划，不改动任何 Lean 证明或论文

以下行号均指上述审计基线。复查后续提交时应重新定位，不能把本快照当作实时构建状态。

## P0：先让一元模型成为可复现、无占位的内核检查结果

- [ ] **P0.1 建立完整构建基线，而非只检查 Atlas**
  - 路径：`lean/lean-toolchain`、`lean/lakefile.lean`、`lean/lake-manifest.json`；默认 Lake target 是 `Theorems`
  - 在有对应工具链的干净 checkout 中运行 `cd lean && lake build`，并运行 `lake build Definitions Theorems` 显式覆盖两个库；必要时先取固定依赖及 mathlib cache。保存实际命令、commit SHA、Lean/Lake 版本、退出码与完整错误日志
  - 逐模块定位失败：Source → Atlas → PrimeBirth。缓存或单模块成功不能代替默认目标成功；不要为凑通过而移除 `Theorems` 默认目标
  - 验收：精确到提交的完整默认构建退出 0，全部项目模块包含在构建中；记录 warning 和未完成声明，不把“含 sorry 能编译”写成“证明完成”

- [ ] **P0.2 完成良基递归展开与基础出生规则**
  - 路径：`lean/Definitions/Def_PrimeMother_Atlas.lean:47–78`
  - 声明：`PrimeMother.birth`、`birth_succ_succ`、`birth_root`、`birth_E`
  - 用 `WellFounded.fix_eq` 后的递归值与 `birth m` 的一致性完成展开；处理两个 `m < n+2` 证明及依赖 if 的同余，移除 L78 的 `sorry`。如简化递归结构，保留严格先前阶段依赖
  - 验收：三个边界/展开引理在固定工具链下编译；`birth_succ_succ` 不依赖 `sorryAx`；定义本身不引入素数判定或最终定理作为假设

- [ ] **P0.3 修复主定理的实际证明链**
  - 路径：`lean/Theorems/Thm_PrimeMother_PrimeBirth.lean`
  - 声明：`birth_ge_two`、`birth_iff_no_earlier_mother`、`birth_iff_prime`
  - L28–29：核验 `simp [birth]` 是否确实展开良基递归并关闭 0/1 分支；优先复用已证明的 `birth_root`、`birth_E`
  - L38–49：统一 `birth m = true` 与 Bool→Prop 的表达；有母体分支中反向蕴含应从“无母体”假设与已有见证导出矛盾，不是再次返回母体见证。逐个检查 if 分支的真实目标
  - L67–79：按固定 mathlib API 重建非平凡因子/素因子证据，移除 L76 的 `sorry`。`Nat.exists_dvd_of_not_prime2` 的两个显式输入是 `2 ≤ n` 与 `¬Nat.Prime n`，不是先传自然数；此处可由 `Nat.exists_dvd_of_not_prime2 h2 hnp` 直接得到 `hcomp`。`Nat.exists_prime_and_dvd` 需要 `d ≠ 1`，不能传 `hdvd : d ∣ n`。最终须有 `p.Prime`、`p ∣ d`、`d ∣ n`、`2 ≤ p`、`p < n`
  - L84–86：强归纳用在素因子 `p` 上；若已改写 `p = j+2`，用 `ih (j+2)`，不能用 `ih j` 证明 `birth (j+2)`
  - L88–97：先合成 `p ∣ n`，再取属于 `p` 的商。当前从 `hdvd : d ∣ n` 取出的 `r` 满足 `n = d*r`，不能直接用来构造 `HasRegAtlas n p`；用 `p<n` 与 `p≥2` 证明新商至少 2
  - L109–112：`Nat.prime_def_lt` 的类型是 `Nat.Prime p ↔ 2 ≤ p ∧ ∀ m < p, m ∣ p → m = 1`；不能用 `(Nat.prime_def_lt hp).mp ...`。可用 `(Nat.prime_def_lt.mp hp).2 m hmlt' hdvd` 得到 `m=1`，再与 `hm2` 矛盾。最后检查 `termination_by` 是否仍适用于最终证明结构
  - API 依据：[固定版本 Basic.lean L68–77](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Nat/Prime/Basic.lean#L68-L77)、[Defs.lean L107–120](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Nat/Prime/Defs.lean#L107-L120)、[Defs.lean L407–408](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Nat/Prime/Defs.lean#L407-L408)
  - 验收：原始目标 `∀ n, 2 ≤ n → (birth n = true ↔ Nat.Prime n)` 不削弱、不添加“结论已成立”类假设；整个文件编译且没有 `sorry`/`admit`

- [ ] **P0.4 生成内核依赖收据与回归测试**
  - 路径：上述 3 个 Lean 模块；建议新增专门测试/审计模块（后续实现任务）
  - 对 `birth_succ_succ`、`birth_iff_no_earlier_mother`、`birth_iff_prime` 执行 `#print axioms`，记录完整传递依赖。允许标准 Lean/mathlib 基础公理时应明确列出；拒绝 `sorryAx` 与未声明用途的自定义公理
  - 加入 0、1、2、3、4、6、9、25 等样例，覆盖单位排除、首批素数、合数与平方数；当前 `birth` 是 `noncomputable`，不能把未运行的 `#eval` 当测试。可先写证明式 examples，若需可执行枚举，另实现并证明有限算法等价
  - 验收：完整 build、样例、占位检查与公理检查共同通过；测试文件被实际执行；公开精确 SHA 的日志

## P1：补齐论文的一元语义与可维护性

- [ ] **P1.1 明确“秩模型”与“无标签源形式化”的边界**
  - 路径：`lean/Definitions/Def_PrimeMother_Source.lean:17–33`；论文 “Atomic successor source / Clock reconstruction”
  - 当前 `clock_reconstruction` 只是 `rk H = H`。构造抽象源、有限路径/前缀、原子后继及前缀序，证明秩的 order isomorphism、保根/后继与唯一性；再把当前 Nat 模型作为传输后的实现
  - 验收：真正的源→Nat 等价与唯一性有独立定理；若暂不实现，README/注释清楚标为“秩模型”，不得将 `rfl` 描述为论文完整源层证明

- [ ] **P1.2 保留 atlas 与 chronological provenance 证据**
  - 路径：`lean/Definitions/Def_PrimeMother_Atlas.lean:25–41`；论文 `lem:atlas-rank` 及 “Birth ledger / Stage provenance”
  - 定义实际连续分块、端点相交、内部不交、覆盖与路径同构见证；证明它们与当前乘法存在式等价及适用条件下唯一
  - 补 birth ledger 与 provenance 记录。当前 `Mother Pi H := HasRegAtlas H Pi` 没有“Pi 是更早 birth”的限制；应明确它只是裸 atlas 关系，或加入/单独证明 `birth Pi=true ∧ Pi<H` 的资格层
  - 覆盖零长/单位边界：当前裸关系可有 `Mother 0 0`、`Mother 1 2`，但这不等于出生递归真的把 0/1 当母体。不要把两个层次混为一谈
  - 验收：从记录可提取实际继承见证，出生记录可证明所有合格先前母体均失败；重命名源状态保持 ledger、mother 与 birth

- [ ] **P1.3 补一元结果与论文对应清单**
  - 路径：`lean/Theorems/`；论文 “Relabelling invariance / Path-sieve identity / Exact distribution identity”
  - 补素数母锥的后续倍数刻画、出生计数等于 `π(x)`，以及论文实际采用的出生测度/支撑恒等式；明确自然数截断与实数参数边界
  - 验收：每个宣称已形式化的论文结论都有准确 Lean 声明名；这些是支持集/计数恒等式，不宣称得到新的素数间隔估计

- [ ] **P1.4 增加 README 与 CI**
  - 路径：建议 `README.md`、`.github/workflows/lean.yml`
  - README 给出从 `lean/` 构建的命令、固定依赖、已验证提交与范围；修正 PrimeBirth 文件头的章节号（当前论文 Exact prime-birth theorem 是第 5 节，文件写 §6）
  - CI 覆盖 push/PR、固定工具链、`lake build`、全部模块及测试、公理/占位门禁。不能仅 grep 无 `sorry` 就声称证明可信
  - 验收：新提交有可访问的成功 run；失败/缺失/未运行状态分开显示，论文每项标记“已实现且检查 / 未完成 / 未实现”

## P2：论文最终结论的缺失实现，按依赖顺序推进

这一层目前没有 Lean 定义或定理；以下名称是建议模块/目标，不能当作现有成果。

- [ ] **P2.1 有限 return source 与实际 packet 几何**
  - 建议路径：`lean/Definitions/Def_PrimeMother_ReturnSource.lean`、`Def_PrimeMother_ReturnPacket.lean`
  - 对应论文：`prop:return-normal-form`、`thm:return-combination`
  - 实现有限顶点等价关系、不合并相邻点、new/old-class 扩张、规范词与无标签同构的双向对应；再定义 elementary return、simple-return sector、完整返回包和“共享原子边”的图
  - 证明任意**非空**有限互异素数集的 packet 构造，端点互异、不相邻、完整返回集合准确、交叠图为路径图；同时证明 born packet 的反向分类。论文定理 (ii) 写“every finite set”时应显式补非空前提以匹配总述
  - 验收：正向/反向分类分别有 Lean 定理，empty/singleton 情况明确；predicate 不以待证素数集合直接作定义

- [ ] **P2.2 Descent 与 mixed fibres**
  - 建议路径：`lean/Theorems/Thm_PrimeMother_ReturnDescent.lean`
  - 对应论文：有限 packet 章节、`thm:return-combination`、`cor:boundary-mixed-fibres` 的有限核心
  - 证明连通图可删除非指定根的生成树叶；split endpoint class 操作保持其余返回、atlas ledger 与连通性，能终止于任意指定 unary 成员
  - 实现相同 unary ranks 的 born/unborn 对照，例如 `[0,2],[1,4]` 与 `[0,2],[3,6]`；共享端点不等于共享原子边。证明不同 overlap patterns 可给出不同 connected-face posets
  - 验收：每一步有实际源操作与不变量，非仅存在素数子集链；用同影子不同判决见证“不可由 divisor shadow 决定”

- [ ] **P2.3 无限边界、shift 与有限语言**
  - 建议路径：`lean/Definitions/Def_PrimeMother_Boundary.lean`、`lean/Theorems/Thm_PrimeMother_BoundaryLanguage.lean`
  - 对应论文：`prop:finite-not-boundary`、`def:source-transitive-birth`、`lem:finite-language-criterion`、`thm:transitive-existence`
  - 构造有限历史的逆极限/等价无限历史模型、cylinder 基、紧性、连续 shift、orbit hull、windows 与有限语言；证明 hull=language inclusion 刻画及 dense-history 非空
  - 单独表述 generated-subsource inheritance principle。论文明确它是额外边界原则，有限出生判决不能推出它；把 `Birth∞ := dense orbit` 定义写清楚，不以此冒充从有限规则推出的定理
  - 验收：额外原则/定义与推论依赖清晰可见；存在性有构造或内核检查证明，不能只假设有 dense history

- [ ] **P2.4 全素数谱、边界 descent 与唯一 provenance 类**
  - 建议路径：`lean/Theorems/Thm_PrimeMother_AllPrimeBoundary.lean`
  - 对应论文：`lem:atlas-irreducible`、`thm:all-prime-return`、`prop:boundary-unary-descent`、`cor:boundary-mixed-fibres`、`thm:unique-provenance-class`
  - 依赖路线：无占位 unary theorem → atlas irreducibility → 有限 return birth 与 descent → finite-language criterion + transitive existence → 全谱/windows → boundary descent → provenance 商类唯一性
  - 原始 atlas test 定义的 primitive spectrum，其反向包含部分是定义给出的；仍须证明每个 irreducible type 被窗口实现，再识别其秩恰为全部素数
  - 证明任意 shift tail 仍 dense、任意指定素成员的 descent，以及同一全局 history 中两种 mixed fibres
  - 以有限语言相等定义 provenance 等价，证明 born locus 非空且其商恰一类。**不能把唯一等价类加强成唯一/典范 carrier history**
  - 验收：最终公开 theorem 明列边界原则的范围，无 `sorryAx`；覆盖存在性、两向谱等式、有限窗口与下降塔，不把核心结论藏入参数假设

- [ ] **P2.5 单列 obstruction audits 与外部来源**
  - 路径：论文 `prop:atlas-divisor`、`thm:uniserial-obstruction`、`prop:cover-subgroup`、`prop:cubical-product-divisor`、`thm:one-candidate`、`prop:coprime-splitting`、`prop:pq-obstruction`、`prop:primary-tensor`、`prop:ribbon-count`、`prop:global-boolean-tradeoff`；建议独立 `lean/Theorems/Obstructions/`
  - 把可形式化对象/操作范围与数学前提写完整，分别实现 divisor/cubical/cover/primary/Boolean obstruction；这些否定性结论不能被“正向 final theorem 完成”自动覆盖
  - 论文多处引用 source manuscript 的 Version 0.27/0.29、ribbon 与 A₅ control，但基线仓库没有这些原始文献/代码。补精确来源、引用及需要形式化的输入，不将未检查的外部结论包装成已验证 lemma
  - 验收：coverage 清单分别标注独立实现、导入已证明定理、待验证外部依据及未实现项

## 一元里程碑完成条件

只有同时满足以下条件，才把“一元 prime-birth Lean 证明”标为完成：

1. 锁定依赖下的完整 `lake build` 与测试对同一 commit 成功
2. 两处 `sorry` 和其后所有 elaboration/证明链错误消除
3. 主定理与递归展开的 `#print axioms` 收据不含 `sorryAx` 或偷渡结论的自定义公理
4. 明确该里程碑证明的是秩模型还是已完成源层桥接；不把它等同于论文全部 finite-return / boundary 结论
