# PrimeMother TODO：Lean 状态与完成路线

审计日期：2026-10-08 02:52（UTC）  
审计基线 / 已审计代码游标：`master` @ [f4b778971bfee39bfb007716cddebc040689a23b](https://github.com/cchx0000/primemother/commit/f4b778971bfee39bfb007716cddebc040689a23b)  
首次完整源码与论文审计：[258fb757f4712b18ce45310bbebbd34e9dc9226d](https://github.com/cchx0000/primemother/commit/258fb757f4712b18ce45310bbebbd34e9dc9226d)

<!-- primemother-audit-cursor: f4b778971bfee39bfb007716cddebc040689a23b -->

## 当前结论与验证边界

当前仓库是**一元 prime-birth 的算术模型与未完成证明骨架**，还不是论文全部结论的 Lean 形式化。

- 首次审计已逐个检查全部 3 个证明源模块（不含 `lakefile.lean`）、Lake 配置/锁文件、论文的主要结论及其依赖。本轮检查 `adbeb277` → `f4b77897` 的全部 2 个提交：`c9173846` 是本审计器自身的纯 `todo.md` 同步，跳过重复审计；新增源码提交仅 `f4b77897`，只调整 Atlas 的展开引理注释与脚本。本轮重读全部 3 个证明模块及 Lake 配置/锁文件、工具链，并检查完整文件树；其他源码、论文及配置均无变更
- 源码中仍有 **1 处显式 `sorry`**，位于 `Def_PrimeMother_Atlas.lean:77` 的 `birth_succ_succ`。`birth_E`、`birth_root` 保持 `adbeb277` 提交的无直接占位脚本；`f4b77897` 只增加技术说明并移除 `simp only []`，未消除该占位。Theorems 文件仍无直接 `sorry`，但 `birth_iff_no_earlier_mother` 与主定理仍依赖未完成的 `birth_succ_succ`；注释所称不依赖具体证明技术，不等于不依赖该展开等式的证明，不能称为无 `sorryAx` 的最终定理
- 3 个模块中未见显式 `axiom` / `admit` 声明。出生定义没有调用 `Nat.Prime`，递归依赖严格更小的 `m`，未发现把最终结论作为显式假设输入的循环；但尚未通过内核依赖审计，不能据此称“无公理/无 sorry”
- `Prefix := Nat`、`rk H := H`、`HasRegAtlas H Pi := ∃ r ≥ 2, rk Pi * r = rk H`。这些是秩模型的定义；`clock_reconstruction` 的 `rfl` 不是抽象无标签路径的唯一 order isomorphism 证明，两个 atlas-rank 引理也不是实际分块/路径同构的构造
- `birth_iff_prime` 保留原始声明及仅有的 `2 ≤ n` 前提；证明脚本已补全直接占位，仍依赖 Atlas 的 1 个占位引理且本审计未实编译。论文的有限联合 birth、return source、无限边界与唯一 provenance 等价类仍无对应 Lean 实现
- 本轮**没有运行 Lean/Lake 编译、测试或 `#print axioms`，仅做源码审计**。`f4b778971bfee39bfb007716cddebc040689a23b` 的精确 SHA 查询结果为 Actions runs 0、check-runs 0、commit statuses 空，未见可核验的完整构建或内核依赖收据；空 statuses 的汇总 `pending` 不代表有任务正在运行。本轮没有新增 CI 配置，不能根据技术性注释或静态阅读宣称证明已编译通过
- 已固定 Lean `v4.33.1` 与 mathlib `0df444a360eaa60ab8c11dca51a86af692955474`；已核对该 mathlib 提交的 `lean-toolchain` 也是 `v4.33.1`，未发现版本针本身不匹配
- 首次基线无 README、根目录 `todo.md` 或仓库级操作说明；`6694cbf4` 已新增本文件。本轮只同步审计状态，不改动 Lean 证明或论文

以下行号均指当前已审计代码 `f4b77897`（历史增量记录保留各自提交的行号）。复查后续提交时应重新定位，不能把本快照当作实时构建状态。

## 增量审计记录

- **2026-10-07：[`a18a9599`](https://github.com/cchx0000/primemother/commit/a18a9599b6d9a4f16c3ec28058f84f653b569685)**，标题 `P0.2: birth via Nat.strongRecOn (3 sorries in unfolding lemmas, structure honest)`
  - 变更仅涉及 `lean/Definitions/Def_PrimeMother_Atlas.lean`：将 `WellFounded.fix` 换为 `Nat.strongRecOn`，保留只查询 `m < n+2` 的先前阶段依赖，并去掉旧定义重复的 `<` 见证层
  - `birth_E`、`birth_root` 原证明改为 `sorry`；`birth_succ_succ` 仍为 `sorry`。这是递归结构调整，**P0.2 仍未完成**，占位总数从 2 增至 4
  - Source、PrimeBirth、论文、工具链/依赖、构建配置没有变化，P0.1、P0.3、P0.4 及 P1/P2 没有新的完成证据；所有未完成项继续保留
  - 验证：静态源码与提交差异检查；未运行 build、测试或 `#print axioms`；远端该 SHA 无 Actions/check/status 收据

- **2026-10-07：[`3e9d7d3`](https://github.com/cchx0000/primemother/commit/3e9d7d3cfa713060ac5b8eef4da2040605bb5e60)**，标题 `P0.3: birth_iff_prime proof complete (0 sorry in Theorems; 3 unfolding sorries remain in Atlas)`
  - 只改动 `lean/Theorems/Thm_PrimeMother_PrimeBirth.lean`：0/1 分支改用 `birth_root`/`birth_E`，统一 Bool 等式、改正“有母体”分支的矛盾方向，按固定 API 重建因子见证，归纳改用 `ih (j+2)`，先合成 `p ∣ n` 再取正确商，并修正 `Nat.prime_def_lt` 用法
  - 删除该文件唯一直接 `sorry` 与旧 `termination_by`，章节号改为论文 §5。原始目标未削弱，也未新增结论型假设
  - **P0.3 为“源码修复已提交，待构建及无占位依赖验证”**；主定理传递依赖的 `birth_root`、`birth_E`、`birth_succ_succ` 仍有 `sorry`。没有编译/`#print axioms` 收据，不将标题中的“proof complete”作为验收结果
  - 其他模块、论文与配置未改；该 SHA 的 Actions/check/status 均为空。P0.1/P0.2/P0.4、README/CI 与 P1/P2 剩余目标继续保留

- **2026-10-07：[`adbeb277`](https://github.com/cchx0000/primemother/commit/adbeb27777cd09107ac44aba03da7beb7555cfe7)**，提交时间 15:05:47 UTC，标题 `P0.2: birth_E and birth_root proved via WellFounded.fix_eq; birth_succ_succ remains`
  - 自上次代码游标起，中间的 `9859e4f3` 仅同步本文件；新增代码只有本提交，且只修改 `lean/Definitions/Def_PrimeMother_Atlas.lean`
  - `birth_E` L57–59、`birth_root` L62–64 改为 `unfold birth ... Nat.strongRecOn` 后 `rw [WellFounded.fix_eq]`，移除两处直接 `sorry`；定义和定理声明均未改变，没有新增假设
  - `birth_succ_succ` L67–77 也改用 `WellFounded.fix_eq` 并加入 `simp only []`，但仍以 `sorry` 收尾；递归调用与 `birth m` 的对应及两侧 if 条件等价仍待完成
  - 当前直接占位计数 **3 → 1**；P0.2 有源码进展，仍未验收。P0.3 的脚本未变，仍被该展开引理和实际构建/内核审计阻塞；P0.1/P0.4、P1/P2 均无新的完成证据
  - 验证范围：全量读取 3 个证明模块、检查该提交差异；未运行 Lean/Lake、测试或 `#print axioms`；该 SHA 的 Actions/check/status 查询均为空

- **2026-10-08：[`f4b77897`](https://github.com/cchx0000/primemother/commit/f4b778971bfee39bfb007716cddebc040689a23b)**，提交时间 01:43:24 UTC，标题 `P0.2: document birth_succ_succ as technical unfolding (1 sorry remains)`
  - 自上次代码游标起，先核对 [`c9173846`](https://github.com/cchx0000/primemother/commit/c9173846d27645a665960b538956d5706542e1b5) 仅同步本文件并跳过自触发；新增源码只有本提交，且只修改 `lean/Definitions/Def_PrimeMother_Atlas.lean`
  - `birth_succ_succ` 的说明扩展为 L66–70，声明移至 L71–74；L75–77 仅保留 `unfold birth Nat.strongRecOn`、`rw [WellFounded.fix_eq]`、`sorry`，删除原 `simp only []` 及操作注释
  - 定义、定理目标和前提均未改变；没有新增 `axiom` / `admit` 或结论型假设，严格先前阶段的递归结构未变。直接占位仍为 **1 → 1**；注释不构成展开等式已经证明或主定理绕过占位的证据
  - 主定理经 `birth_iff_no_earlier_mother` L40 的 `rw [birth_succ_succ]` 继续依赖该占位。P0.2/P0.3 均不勾选；P0.1/P0.4、P1/P2 无新的完成证据
  - 验证范围：该区间两个提交逐个核对、全量读取 3 个证明模块与构建配置；未运行 Lean/Lake、测试或 `#print axioms`。新增源码 SHA 的 Actions runs/check-runs 均为 0，commit statuses 为空，未见新增构建日志

后续审计从上述代码游标之后按提交顺序处理；本审计器自身仅修改 `todo.md` 的提交不触发重复写入。若出现历史分叉、缺失提交或并发修改，先重新比较 HEAD 和最新文件，不覆盖他人变更。

## P0：先让一元模型成为可复现、无占位的内核检查结果

- [ ] **P0.1 建立完整构建基线，而非只检查 Atlas**
  - 路径：`lean/lean-toolchain`、`lean/lakefile.lean`、`lean/lake-manifest.json`；默认 Lake target 是 `Theorems`
  - 在有对应工具链的干净 checkout 中运行 `cd lean && lake build`，并运行 `lake build Definitions Theorems` 显式覆盖两个库；必要时先取固定依赖及 mathlib cache。保存实际命令、commit SHA、Lean/Lake 版本、退出码与完整错误日志
  - 逐模块定位失败：Source → Atlas → PrimeBirth。缓存或单模块成功不能代替默认目标成功；不要为凑通过而移除 `Theorems` 默认目标
  - 验收：精确到提交的完整默认构建退出 0，全部项目模块包含在构建中；记录 warning 和未完成声明，不把“含 sorry 能编译”写成“证明完成”

- [ ] **P0.2 完成良基递归展开与基础出生规则**
  - 路径：`lean/Definitions/Def_PrimeMother_Atlas.lean:47–77`
  - 声明：`PrimeMother.birth`、`birth_succ_succ`、`birth_root`、`birth_E`
  - 当前状态：递归主体保持 `Nat.strongRecOn`；`birth_E` L57–59、`birth_root` L62–64 已提交无直接占位的证明脚本，待实际构建确认；`birth_succ_succ` L71–77 仍有唯一直接 `sorry`
  - 当前 n+2 展开脚本为 L75 的 `unfold birth Nat.strongRecOn`、L76 的 `rw [WellFounded.fix_eq]`，随后 L77 仍留占位；`f4b77897` 已移除 `simp only []`，技术说明未完成该证明。完成递归值与 `birth m` 的一致性及存在见证/if 条件的命题等价，保留严格先前阶段依赖；同时对 0/1 边界脚本做固定版本编译与公理核查
  - 验收：三个边界/展开引理在固定工具链下编译且均不依赖 `sorryAx`；定义本身不引入素数判定或最终定理作为假设

- [ ] **P0.3 验证已提交的主定理证明链**
  - 路径：`lean/Theorems/Thm_PrimeMother_PrimeBirth.lean:19–116`
  - 声明：`birth_ge_two`、`birth_iff_no_earlier_mother`、`birth_iff_prime`
  - 当前状态：`3e9d7d3` 已在源码层修复此前逐项列出的接线并删除本文件直接占位；保持未勾选，等待完整构建与 P0.2 的无占位依赖
  - L21–32：0/1 分支使用 `birth_root` 与 `birth_E`；这两个 Atlas 引理已在 `adbeb277` 去除直接占位，仍需实际编译及依赖审计确认。主定理经 L40 的展开规则仍依赖 `birth_succ_succ` 的占位
  - L37–56：统一使用 `birth m = true`，有母体分支改为从 `h` 与 `hno` 导出矛盾；实际编译验证各 if 分支目标
  - L72–83：改用 `Nat.exists_dvd_of_not_prime2 h2 hnp` 与 `Nat.exists_prime_and_dvd hd1`；已通过 `dvd_trans hpdvd hdvd` 得到 `p ∣ k+2`
  - L86–105：归纳调用已改为 `ih (j+2)`；商见证取自 `p ∣ k+2`，分别排除商为 0/1。需编译核实 tactic、等式方向及 `HasRegAtlas` 构造
  - L108–116：改用 `(Nat.prime_def_lt.mp hp).2 m hmlt hdvd` 得到 `m=1` 后矛盾；旧 `termination_by` 已删除
  - API 依据：[固定版本 Basic.lean L68–77](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Nat/Prime/Basic.lean#L68-L77)、[Defs.lean L107–120](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Nat/Prime/Defs.lean#L107-L120)、[Defs.lean L407–408](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Nat/Prime/Defs.lean#L407-L408)
  - 验收：原始目标 `∀ n, 2 ≤ n → (birth n = true ↔ Nat.Prime n)` 不削弱、不添加“结论已成立”类假设；整个文件编译且没有 `sorry`/`admit`

- [ ] **P0.4 生成内核依赖收据与回归测试**
  - 路径：上述 3 个 Lean 模块；建议新增专门测试/审计模块（后续实现任务）
  - 对 `birth_E`、`birth_root`、`birth_succ_succ`、`birth_iff_no_earlier_mother`、`birth_iff_prime` 执行 `#print axioms`，记录完整传递依赖。允许标准 Lean/mathlib 基础公理时应明确列出；拒绝 `sorryAx` 与未声明用途的自定义公理
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
  - README 给出从 `lean/` 构建的命令、固定依赖、已验证提交与范围；PrimeBirth 文件头章节号已在 `3e9d7d3` 修正为论文 §5，该局部修正不等于 README/CI 完成
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
2. 当前唯一的 `birth_succ_succ` 占位及所有剩余 elaboration/证明链错误消除，主定理的传递依赖也无占位
3. 主定理与递归展开的 `#print axioms` 收据不含 `sorryAx` 或偷渡结论的自定义公理
4. 明确该里程碑证明的是秩模型还是已完成源层桥接；不把它等同于论文全部 finite-return / boundary 结论
