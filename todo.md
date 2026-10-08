# PrimeMother TODO：Lean 状态与完成路线

审计日期：2026-10-08 10:02（UTC）  
已审计提交游标：`master` @ [e656bc1939cb6bb30f17aa7f45405c9f6bd88256](https://github.com/cchx0000/primemother/commit/e656bc1939cb6bb30f17aa7f45405c9f6bd88256)  
当前 Lean 源码基线：[63875fea93c35cbe6dd4b66183aaf2212a91e66b](https://github.com/cchx0000/primemother/commit/63875fea93c35cbe6dd4b66183aaf2212a91e66b)（其后仅 TODO / 收据文档变更）  
首次完整源码与论文审计：[258fb757f4712b18ce45310bbebbd34e9dc9226d](https://github.com/cchx0000/primemother/commit/258fb757f4712b18ce45310bbebbd34e9dc9226d)

<!-- primemother-audit-cursor: e656bc1939cb6bb30f17aa7f45405c9f6bd88256 -->

## 当前结论与验证边界

当前仓库已有**一元 prime-birth 秩模型的无直接占位证明脚本、8 个回归样例、部分无标签源层定义与定理，以及对应相同源码的维护者构建摘要和 7 个声明的公理输出**。本轮只审查源码与已有证据，未独立运行 Lean；完整可复现验证记录仍待补齐，也不是论文全部结论的 Lean 形式化。

- 本轮从 `63875fea` 游标继续，逐个核对两个后续提交：`85df6c0e9d11b522f77efb99b50ab565030ad275` 仅同步本文件，跳过自触发；`e656bc1939cb6bb30f17aa7f45405c9f6bd88256` 仅新增构建收据。重读当前 4 个证明模块、README、工具链与 Lake 配置/锁文件及完整文件树。源码、依赖、论文、README 与模型假设均未改变
- 新增 [构建收据](https://github.com/cchx0000/primemother/blob/e656bc1939cb6bb30f17aa7f45405c9f6bd88256/docs/receipts/build-85df6c0e9d11b522f77efb99b50ab565030ad275.md) 明确覆盖 `85df6c0e9d11b522f77efb99b50ab565030ad275`，记录时间 09:21:26 UTC、Lean `v4.33.1`、`cd lean && lake build`、退出码 0、614 jobs / 0 errors。这比此前 README / 提交标题的无 SHA 断言更具体；对比确认该 SHA 的 Lean 源码与配置和当前 HEAD 一致，不能仅因 HEAD 是后续文档提交就把收据视为源码过期
- 收据 L14–20 提供 `birth_E`、`birth_root`、`birth_succ_succ`、`birth_iff_no_earlier_mother`、`birth_iff_prime`、`clock_iso`、`crk_injective` 共 7 个声明的逐项文本，每项列出 `[propext, Classical.choice, Quot.sound]`，并报告 `lake env lean` 退出 0。可确认这些文字已提交，不能写成审计器亲自重跑通过；也不能把末行“any dependency closure”扩张为所有未列声明都已审计
- 收据仍缺完整原始构建日志、warning / 项目模块实际覆盖记录、执行时 checkout 清洁状态与版本输出，以及公理审计输入文件 / 完整调用参数；树中没有已提交审计入口。`crk_mono`、`crk_strict_mono` 不在 7 项输出中。保留 P0 的完整可复现验收，新增已收到构建摘要和具名公理输出的完成子项，不再把现状描述为“没有 SHA / 退出码 / 逐声明输出”
- 当前 4 个证明模块直接 `sorry` / `admit` / `axiom` 声明均为 **0**。`birth` 仍只递归查询严格更小的 `m`，不调用 `Nat.Prime`；`birth_iff_prime` 仍是 `∀ n, 2 ≤ n → (birth n = true ↔ Nat.Prime n)`，无新增结论型假设。8 个回归样例均在 `Theorems` 子模块 glob 内；25 的样例使用主定理证明 `birth 5`，属于回归覆盖，不是独立验证
- 源层 `clock_iso` L93–94 仍仅声明 `Function.Injective crk ∧ Function.Surjective crk`，缺序反映、完整 order isomorphism、保根/后继映射唯一性和 atlas/birth 正式传输。实际 birth 仍用 `Prefix := Nat`、`rk H := H` 与乘法存在式 `HasRegAtlas`；实际分块、chronological provenance、finite-return / boundary / 唯一 provenance 类仍未实现，P1/P2 没有新增完成证据
- 本轮**未运行 Lean/Lake 编译、测试或 `#print axioms`**。对收据目标 `85df6c0e` 和当前 `e656bc19` 逐一查询：Actions runs 0、check-runs 0、commit statuses 空、commit comments 空；汇总 `pending` 不表示构建运行中。无 CI workflow，根 `.gitignore` 仍含 `.github/`。收据是维护者提交的证据摘要，不是已访问的 CI run / 完整执行日志
- Lean `v4.33.1` 与 mathlib `0df444a360eaa60ab8c11dca51a86af692955474` 固定针未改。README 的“源层尚未实现”说明及 P0 完成断言仍需与当前证据范围对齐；本轮只同步 `todo.md`，不改证明、论文、README、CI 或设置

以下源码行号仍指 `63875fea`（与当前 HEAD 的 Lean 文件一致）；收据行号指 `e656bc19`。历史增量记录保留当时的证据状态，后续新增收据不会改写历史事实。

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

- **2026-10-08：[`36add88e`](https://github.com/cchx0000/primemother/commit/36add88e6a1a82a11f97044347ce808d2289bacb)**，提交时间 04:00:16 UTC，标题 `P0.2 complete: birth_succ_succ proved via fix_eq + propext; 0 sorry in library`
  - 在核对 `a643b8162879869c204fab42263ce285e9baa996` 仅同步本文件后，逐个审计新增提交。本提交修改 Atlas 的 `birth_succ_succ` L77–90，并删除 PrimeBirth 中“currently sorry”的过期注释；主定理脚本与所有声明/前提不变
  - 通过 `show` 指出递归值的定义等价，再以 `congr 1`、`propext` 与两向见证重组消除最后占位。源码显式 `sorry` 总数 **1 → 0**；P0.2 的源码修复已完成，实际编译及传递公理验收仍待收据
  - 没有新增素数判定输入、显式自定义公理或结论型假设；未运行编译。本 SHA 的 Actions/check-runs/statuses/comments 均空

- **2026-10-08：[`9473ec06`](https://github.com/cchx0000/primemother/commit/9473ec06c79810d2f79679f85f3bea6196ba761c)**，提交时间 04:03:02 UTC，标题 `P0.4: regression tests (0/1/2/3/4/6/9/25) + axiom audit clean (propext/choice/Quot.sound only)`
  - 仅新增 `lean/Theorems/Thm_PrimeMother_Regression.lean`（109 行），导入 PrimeBirth；0/1 使用边界引理，2/3/4/6/9 使用递归规则和 atlas 见证，25 借用主定理在 5 上的实例后构造 r=5 的 atlas
  - 8 个证明式样例均无直接占位，现有 Lake glob 配置覆盖新模块。未新增任何已保存的 `#print axioms` 审计模块或输出；标题中的公理列表不作为已核验结果。P0.4 从“待添加样例”更新为“样例已提交，执行及内核收据待验收”
  - 未运行编译/样例/公理检查；本 SHA 的 Actions/check-runs/statuses/comments 均空

- **2026-10-08：[`300036da`](https://github.com/cchx0000/primemother/commit/300036da9c01d2c10ace1ddb5398c9f55532fd37)**，提交时间 04:07:31 UTC，标题 `P1.4: README (build instructions, scope, axiom audit)`
  - 仅新增根 `README.md`（51 行），给出固定版本、`cd lean && lake build`、主定理范围、后续有限/边界工作说明与本 TODO 链接
  - L39、L43–45、L50 的 build 成功、无 `sorryAx`、P0 完成是文字断言；没有精确 SHA 的完整日志或可访问 run。README 已存在的事实记为完成，P0 验收及 CI 不据此勾选
  - 本 SHA 的 Actions/check-runs/statuses/comments 均空；后续 Source 变更需要重新验证当前提交，并同步 README 源层范围文字

- **2026-10-08：[`63875fea`](https://github.com/cchx0000/primemother/commit/63875fea93c35cbe6dd4b66183aaf2212a91e66b)**，提交时间 04:13:04 UTC，标题 `P1.1: abstract unlabelled source (Chain/ChainLE/crk) + clock_iso; rank model marked as transport`
  - 改动 `Def_PrimeMother_Source.lean` 并新增根 `.gitignore`，后者唯一规则为 `.github/`。全树仍无 CI workflow；不推断添加该规则的动机
  - Source L27–97 新增自由归纳链、前缀关系、秩、秩单调/严格单调、任意秩的 `chainOf` 实现及秩双射；无直接 `sorry`/`admit`/`axiom`。L104–122 保留原有 Nat 秩模型并澄清旧 `clock_reconstruction` 只是恒等式
  - `clock_iso` 仅是指定映射 `crk` 的 injective/surjective 合取。序反映、打包的序同构、保根/后继映射的唯一性，以及一般论文源与该规范 Chain 模型的对应尚未形式化；Source 到 atlas/birth 的 transport 也没有对应声明。P1.1 有实质进展但未完成
  - 验证范围：4 个新增提交逐个差异、4 个完整证明模块、README、依赖/工具链、全树与相关论文段落；未运行 Lean/Lake、测试或公理审计。本 SHA 的 Actions/check-runs/statuses/comments 均空；论文、Atlas/PrimeBirth/Regression 和 Lake 配置在此提交未改

- **2026-10-08：[`e656bc19`](https://github.com/cchx0000/primemother/commit/e656bc1939cb6bb30f17aa7f45405c9f6bd88256)**，提交时间 09:21:26 UTC，标题 `docs: build receipt for 85df6c0e9d11b522f77efb99b50ab565030ad275 (614 jobs, 0 errors, 0 sorry, axioms clean)`
  - 先核对父提交 [`85df6c0e`](https://github.com/cchx0000/primemother/commit/85df6c0e9d11b522f77efb99b50ab565030ad275) 仅同步 `todo.md`，跳过自触发；本提交只新增 `docs/receipts/build-85df6c0e9d11b522f77efb99b50ab565030ad275.md`（23 行）。从 `63875fea` 到本 SHA 的全部差异只有 TODO 与收据，Lean / 依赖 / 论文均未改变
  - 收据 L3–9 给出精确被构建 SHA、日期、固定工具链、默认 `lake build` 命令、退出码 0、614 jobs / 0 errors 与源码占位计数 0；L11–20 提供 `lake env lean` 退出 0 的报告和 7 项具名公理输出。报告覆盖最新 Source 变更后的相同源码，不再沿用“README 早于 Source，所以最新源码完全无收据”的判断
  - 所列 7 项为 `birth_E`、`birth_root`、`birth_succ_succ`、`birth_iff_no_earlier_mother`、`birth_iff_prime`、`clock_iso`、`crk_injective`；均列出 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx`。这是已提交文本的检查结果，不是审计器独立运行所得
  - 完整构建日志、warning / 模块覆盖、checkout 清洁状态、审计输入与完整命令仍未提交；`crk_mono` / `crk_strict_mono` 未列出。P0 新增“收到精确 SHA 的摘要 / 7 项输出”子项，完整可复现验收继续开放；P1/P2 实现差距不变
  - 验证范围：两个后续提交逐一差异、4 个证明模块、工具链 / 配置 / 锁文件、README、完整树与收据；未运行 Lean/Lake / 样例 / 公理审计。收据目标 SHA 与本 SHA 的 Actions/check-runs/statuses/comments 均空

后续审计从上述提交游标之后按提交顺序处理；本审计器自身仅修改 `todo.md` 的提交不触发重复写入。若出现历史分叉、缺失提交或并发修改，先重新比较 HEAD 和最新文件，不覆盖他人变更。

## P0：先让一元模型成为可复现、无占位的内核检查结果

- [ ] **P0.1 建立当前完整构建基线**
  - 路径：`lean/lean-toolchain`、`lean/lakefile.lean`、`lean/lake-manifest.json`；默认 target `Theorems` 的子模块 glob 在配置上包含 PrimeBirth 和新增 Regression
  - [x] 已收到精确 SHA 构建摘要：`docs/receipts/build-85df6c0e9d11b522f77efb99b50ab565030ad275.md:3–9` 记录 `cd lean && lake build`、退出码 0、614 jobs / 0 errors；目标 SHA 与当前 HEAD 的 Lean 源码和配置一致
  - 剩余证据：完整原始 build 日志、warning / 4 个项目模块覆盖、实际 Lean/Lake 版本输出和 checkout 清洁状态；当前只核验了维护者提交的摘要，远端 Actions/check/status 仍空。无需仅因后续 TODO / 收据文档提交而重跑相同源码，但须使现有构建可复查、可重现
  - 在固定工具链的干净 checkout 中运行 `cd lean && lake build` 及 `lake build Definitions Theorems`，覆盖 Source → Atlas → PrimeBirth → Regression。必要时先取固定依赖及 mathlib cache；保存 commit SHA、Lean/Lake 版本、命令、退出码和日志
  - 验收：同一精确提交上完整默认构建退出 0，4 个项目模块与新增审计模块均实际包含；说明所有 warning。缓存、单模块或文字“Verified”不替代该收据，不通过移除默认 target 凑通过

- [ ] **P0.2 验证已补完的良基递归展开与基础出生规则**
  - 路径：`lean/Definitions/Def_PrimeMother_Atlas.lean:47–90`
  - 声明：`PrimeMother.birth`、`birth_succ_succ`、`birth_root`、`birth_E`
  - [x] 源码修复：`36add88e` 已消除 `birth_succ_succ` 的最后直接占位；`birth_E` L57–59、`birth_root` L62–64 和 `birth_succ_succ` L71–90 均为无直接占位脚本
  - [x] 已收到 `birth_E`、`birth_root`、`birth_succ_succ` 的具名公理输出文本（收据 L14–16），均列出三项标准公理且无 `sorryAx`；收据报告对应相同源码的构建与审计退出 0
  - 剩余工作：补齐可重现的审计输入、完整调用和 P0.1 日志，复核 `WellFounded.fix_eq` 展开、`show` / `congr 1 / propext`、见证重组与 0/1 边界；保持 `Nat.strongRecOn` 严格先前阶段依赖。本轮未独立执行，不能把收到文本等同于独立核验
  - 验收：三个引理在固定工具链编译成功，完整传递公理输出无 `sorryAx`；定义没有素数判定或最终结论型输入。源码子项完成不等于本项已验收

- [ ] **P0.3 验证已提交的主定理证明链**
  - 路径：`lean/Theorems/Thm_PrimeMother_PrimeBirth.lean:19–115`
  - 声明：`birth_ge_two` L21、`birth_iff_no_earlier_mother` L36、`birth_iff_prime` L58
  - 当前状态：主定理自 `3e9d7d3` 已无直接占位；`36add88e` 补齐其依赖的 Atlas 展开脚本。原始目标、严格更小阶段递归与模型假设均未改变
  - [x] 已收到 `birth_iff_no_earlier_mother`、`birth_iff_prime` 的具名公理输出文本（收据 L17–18），均列出三项标准公理且无 `sorryAx`；所指 SHA 包含当前相同证明链
  - 剩余：P0.1 完整日志及公理审计输入 / 完整命令尚缺，未独立重现该报告；不宣称已完成独立内核依赖验收
  - L21–32：确认 0/1 边界使用 `birth_root`、`birth_E`；L36–55：检查 L39 的 `rw [birth_succ_succ]` 和 if 两分支
  - L71–82：核对 `Nat.exists_dvd_of_not_prime2`、`Nat.exists_prime_and_dvd`、`dvd_trans` 与非平凡素因子范围；L85–104：确认 `ih (j+2)`、商见证、排除商 0/1 和 atlas 构造；L107–115：验证 `Nat.prime_def_lt` 方向
  - API 依据：[固定版本 Basic.lean L68–77](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Nat/Prime/Basic.lean#L68-L77)、[Defs.lean L107–120](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Nat/Prime/Defs.lean#L107-L120)、[Defs.lean L407–408](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Nat/Prime/Defs.lean#L407-L408)
  - 验收：原始目标 `∀ n, 2 ≤ n → (birth n = true ↔ Nat.Prime n)` 不削弱、不添加结论型假设；完整文件编译且整个证明链不依赖占位

- [ ] **P0.4 执行已添加的回归测试并保存内核依赖收据**
  - 路径：`lean/Theorems/Thm_PrimeMother_Regression.lean:14–107`；4 个证明模块；建议增加可复现公理审计入口及日志
  - [x] `9473ec06` 已添加 0、1、2、3、4、6、9、25 的证明式 examples，覆盖边界、首批素数、合数与平方数；新模块在现有 Theorems glob 范围内
  - 当前默认 `lake build` 的成功摘要在配置上覆盖 Regression，但缺完整日志来逐项核对样例实际检查。补齐模块覆盖与执行记录；`birth` 为 `noncomputable`，样例是等式证明而非可执行枚举；25 借用主定理的 5 实例，不能作为主定理独立正确性证据
  - [x] 收据 L14–20 已提供 `birth_E`、`birth_root`、`birth_succ_succ`、`birth_iff_no_earlier_mother`、`birth_iff_prime`、`crk_injective`、`clock_iso` 共 7 项逐声明输出文本，所列仅 `propext`、`Classical.choice`、`Quot.sound`
  - 补交可复现 `#print axioms` 输入文件、完整执行命令与原始输出；`crk_mono`、`crk_strict_mono` 仍需具名输出。收据的“any dependency closure”不能替代未列声明的检查；拒绝 `sorryAx` 与偷渡结论的自定义公理
  - 验收：相同 SHA 的完整 build、全部样例与依赖审计共同通过，审计入口实际被执行且日志可访问；源码 grep 不代替内核检查

## P1：补齐论文的一元语义与可维护性

- [ ] **P1.1 补完无标签源的序同构、唯一性与传输**
  - 路径：`lean/Definitions/Def_PrimeMother_Source.lean:27–122`；论文 “Atomic successor source / Clock reconstruction”
  - [x] `63875fea` 已添加规范归纳源 `Chain`、前缀关系 `ChainLE`、秩 `crk`、`crk_mono`、`crk_strict_mono`、`chainOf`、`crk_chainOf`、`crk_injective`、`clock_iso` / `clock_surjective` 的无直接占位脚本，并标出 Nat 部分属于秩模型
  - `clock_iso` L93–94 当前仅为 `crk` 的双射断言。补 `ChainLE a b ↔ crk a ≤ crk b`（目前只有正向）、所需偏序结构与实际 order isomorphism；保根/后继等式虽由 `crk` 定义给出，仍需在桥接定理中明确相容性
  - 补对任意满足保根/后继条件的候选映射 `f : Chain → Nat` 的唯一性证明（例如证明 `f = crk`）；指定 `crk` 的 injectivity 只给出同秩前缀唯一，不能替代候选映射唯一性
  - 说明规范 Chain 与论文一般 rooted directed source 的建模关系；若声称对一般源形式化，给出其结构/假设及到 Chain 的等价。当前模型是自由的一元归纳链，不能仅凭名字宣称任意论文源都已覆盖
  - Source 注释称 `Prefix := Nat` 是 transport，但 Atlas/出生仍只在 Nat 上定义。补源层 atlas/birth 与秩模型的正式对应或明确保留“仅秩模型”的结论范围；同步 README 的旧源层范围说明
  - 验收：真正的源→Nat 序同构、符合条件的唯一性与所宣称的传输各有准确声明并经内核检查；注释不超出声明

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

- [ ] **P1.4 补齐 README 验证依据与 CI**
  - 路径：`README.md:13–50`、根 `.gitignore:1`；建议 `.github/workflows/lean.yml`
  - [x] `300036da` 已新增 README，列出固定版本、`cd lean && lake build`、主定理与尚缺的 finite-return / boundary 范围
  - [x] `e656bc19` 已新增精确 SHA 的构建摘要与 7 项公理输出文件，补上此前缺少的具名证据；README 本身尚未链接该收据
  - 剩余文档：链接现有收据及待补的完整日志 / 审计入口，明确维护者报告与独立核验的区别；不把 L50 的 P0 完成断言当作完整可复现验收。L23–25 的“源层尚未实现”也应更新为当前部分源层实现及 P1.1 剩余差距
  - CI 仍未提交；根 `.gitignore` 新增 `.github/`，后续添加 workflow 时需保证其实际进入版本控制。本审计不修改 ignore 规则或任何 CI 设置
  - CI 覆盖 push/PR、固定工具链、完整 `lake build`、4 个模块与公理审计入口、占位/依赖门禁；不能仅 grep 无 `sorry` 就声称证明可信
  - 验收：当前新提交有可访问的成功 run，失败/缺失/未运行状态分开记录；README 每项标明“已实现且检查 / 实现待检查 / 未完成 / 未实现”

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
2. 已提交的无直接占位脚本通过 elaboration 与内核检查，主定理的完整传递依赖也无占位；不再把源码移除占位当作编译收据
3. 主定理与递归展开的 `#print axioms` 收据不含 `sorryAx` 或偷渡结论的自定义公理
4. 明确该里程碑证明的是秩模型还是已完成源层桥接；不把它等同于论文全部 finite-return / boundary 结论
