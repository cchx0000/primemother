# PrimeMother TODO：Lean 状态与完成路线

审计日期：2026-10-10 15:25（UTC）  
已审计提交游标：`master` @ [3526d4e136727a0bca088c952fc9b161c05ef89a](https://github.com/cchx0000/primemother/commit/3526d4e136727a0bca088c952fc9b161c05ef89a)  
当前 Lean 源码基线：[8d2a7c65aa323a5d27ed0b94acefa1db02b079f7](https://github.com/cchx0000/primemother/commit/8d2a7c65aa323a5d27ed0b94acefa1db02b079f7)（新增 4 个 theorem：递增且每项 ≥2 的输入给记录类严格递增，递增输入给记录支持长度严格递增。8 个库模块、98 个公开 theorem 与 98 个唯一审计输入逐项匹配。新 3019-job / 98 项 clean 收据展示 4 项输出，但所写目标 c0f8ab25… 当前无法解析，尚不能绑定到此源码；旧可解析 90/94 项报告各自保留。未运行 Lean/Lake）  
首次完整源码与论文审计：[258fb757f4712b18ce45310bbebbd34e9dc9226d](https://github.com/cchx0000/primemother/commit/258fb757f4712b18ce45310bbebbd34e9dc9226d)

<!-- primemother-audit-cursor: 3526d4e136727a0bca088c952fc9b161c05ef89a -->

## 当前结论与验证边界

当前仓库已有一元 prime-birth 秩模型、8 个匿名回归样例、部分无标签源层、秩区间 tiling/provenance 和 Nat 分布结果，以及 return-word、packet、单返回与多块合法词构造。**本轮关闭递增且每项 ≥2 输入下“记录类互异”的源码缺口，并新增记录支持长度有序的公开 theorem。** 上轮每条记录接入最终词、有序长度表等于输入、singleton/[2,3] 完整 packet 继续保留；全词次数、一般完整 packet、正确 cut-open sector、路径图和 return birth 正反分类仍未完成。新收据的目标来源待修复，不能把源码静态进展或 98 项报告当作当前内核验收。

- 从上次游标 `dfbe1671e5d66e24afff7c1f48737dc7906bd9dc` 继续，核对 `23c77d47527e619ba70fa8a6f10237321e3b46b1` 仅同步本 TODO 并跳过自触发；随后逐个审计 `8d2a7c65aa323a5d27ed0b94acefa1db02b079f7` 与 `3526d4e136727a0bca088c952fc9b161c05ef89a`。父链连续；除自身 TODO 外净变更为 ReturnCombination +165、AxiomAudit +5/−1 和 41 行新收据。审计前 TODO blob 为 `563dcd362d3920789b536de54978241c0d4179be`
- 新 `blockRecordsAux_classes_lb` L989–1033 与 `blockRecordsAux_classes_sorted` L1041–1094 要求 `ps.SortedLT`、每项 ≥2、`PacketInv`，以及头为 2 时 `lprev < llast`。p=2 分支靠此条件处理交换；递增性排除尾部再次出现 2。公共 `packetWord_classes_sorted` L1099–1125 在初态消去后两项，只要求递增和每项 ≥2；没有 `Nat.Prime` 假设，递增合数输入也适用
- `packetWord_blocks_support_sorted` L1129–1134 只要求 `ps.SortedLT`，以既有 `blockRecordsAux_support` 的有序 map 等式直接重写；不要求每项 ≥2、素性或 PacketInv。它量化的是记录的边数列表，不是最终词全部 elementary returns。不能仅凭记录类/长度互异就调用 sector bridge：还需全词 count-only simple-return 和任意实际 return 对记录的反向分类，且 bridge 的顶点数 `b+1−a` 与这里边数 `b−a` 要在合法端点域对齐
- 既有 singleton p≥2 的完整 packet/次数、[2,3] 完整分类/邻接及 `packetWord_blocks_elementary` 未改。空记录上的有序结论为真空情形；[3,2,5] 重用类 0 三次、[2,2,2] 重复类等历史对照仍说明不可删去适用条件。新四声明没有证明全词恰两次出现、无额外返回/两次类或历史双射
- ReturnWord/ReturnPacket 与论文未改：`SupportIso` L131–132 仍比较 raw 子词相等模式，论文 L994–997 的 `N(J):=J` 是 cut-open 有序路径，L1220–1224 将非同构等价为 ranks 互异。合法词 [0,1,2,3,1,0,4,2] 的 5、3、5 对照及 [2,3] raw slice [1,0,2,1] 的首次编号问题继续成立；仅重编号不足以修正该语义差距
- 全量读取 8 库模块并去注释静态扫描，直接 `sorry` / `admit` / `axiom` 均为 **0**；公开 theorem 为旧 34 + ReturnWord 9 + ReturnPacket 7 + ReturnCombination 48 = **98**，匿名 examples 仍为 8，私有辅助仍为 1。[当前 AxiomAudit](https://github.com/cchx0000/primemother/blob/8d2a7c65aa323a5d27ed0b94acefa1db02b079f7/lean/AxiomAudit.lean) 的 **98 个唯一具名命令逐项匹配，无遗漏/重复/多余**；分节 (44) → (48)。这仅确认输入覆盖，不等于执行或传递依赖检查
- 新 [3019-job / 98 项收据](https://github.com/cchx0000/primemother/blob/3526d4e136727a0bca088c952fc9b161c05ef89a/docs/receipts/build-c0f8ab25db3ccefbb59d80d45519628855677f10.md) 报告固定 Lean/Lake、默认 build 退出 0、0 errors/0 warnings 和公理审计退出 0/98 项 clean，展示新增 4 项标准公理输出。但目标 `c0f8ab25db3ccefbb59d80d45519628855677f10` 的 commit API 返回 422 “No commit found”，Git commit/目标入口读取也返回 404；无法核对其 checkout/tree/98 项输入与当前源码。实际源码与 HEAD 的 Lean tree 同为 `9bcc7732b529a31d9e150bb7d8a1eb51f6d7e927`，不能据此替换收据目标
- 当前先补可解析精确目标，或可核验的内容等价及执行来源，再补 clean checkout、完整 build/audit 原始日志和全部 98 项当次输出并独立重现。新收据没有 clean working tree 字段。旧 90 项的 clean 状态/8 项输出、可解析 94 项的 4 项输出及正确源码/输入对应均保留各自范围，不转移为新四声明的验证；旧 34/68/82 项历史证据也不改写
- 原 birth 的严格先前阶段递归、0/1 边界、主定理目标/脚本和模型假设未改；固定 Lean `v4.33.1`、mathlib `0df444a360eaa60ab8c11dca51a86af692955474`、锁文件/Lake 配置未改。默认 Theorems glob 覆盖 8 模块导入闭包，根 AxiomAudit 须单独运行。两个新增 SHA 的 Actions/check-runs 均为 0，statuses/comments 均空；无 CI workflow，根 `.gitignore` 仍为 `.github/`。本轮未运行 Lean/Lake，没有编译成功或失败的实测记录
- P1 的正式序同构/一般源传输、实际路径 atlas/完整 chronological provenance、实数/测度版本，及 P2.2–P2.5 均未补。P2.1 已有记录块最终词几何及有条件的类/长度互异；正确语义、一般分类及当前内核验收继续开放。README/论文未改，本轮仅同步 `todo.md`

以下当前源码行号以 `8d2a7c65aa323a5d27ed0b94acefa1db02b079f7` 为准，与本轮 HEAD `3526d4e136727a0bca088c952fc9b161c05ef89a` 的 Lean 源码相同；新增部分为 L971–1134，旧 ReturnCombination L1–969 和其余 7 库模块未变。历史增量记录保留当时证据状态，后续收据和实现不改写历史事实。

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


- **2026-10-09：[`6002ab48`](https://github.com/cchx0000/primemother/commit/6002ab48177df54ff2a369c47ddcf5bd7a8fdbe8)**，提交时间 02:17:56 UTC，标题 `docs: full build receipt for 6c774e1a649c3cbb4d5aa1ed1128c612ba862875 (clean build, 17/17 axioms, 0 warnings)`
  - 先核对父提交 `6c774e1a649c3cbb4d5aa1ed1128c612ba862875` 仅同步本文件，跳过自触发；本提交只新增 `docs/receipts/build-6c774e1a649c3cbb4d5aa1ed1128c612ba862875.md`，不改变 Lean/依赖/论文
  - 收据 L3–14 明确目标 SHA、默认 build 退出 0、614 jobs / 0 errors、0 warnings 和干净工作树；此版本 Lean/Lake 字段仍为空。L22–38 给出基线 17 个公开 theorem 的逐项输出，新增覆盖 `crk_mono` / `crk_strict_mono`、`crk_chainOf`、`clock_surjective`、秩/atlas 基础引理与 `birth_ge_two`
  - 各项仅列标准公理子集或无公理。审计输入被描述为临时文件、导入 4 模块、逐项 `#print axioms`，但文件本身/完整调用和原始 build 日志未提交；“full build receipt”标题不消除这些可复现性缺口。未独立运行

- **2026-10-09：[`b98a8e83`](https://github.com/cchx0000/primemother/commit/b98a8e839b95e8ca5415b46e44ac268fe83a9c34)**，提交时间 02:18:01 UTC，标题 `docs: fill Lean/Lake versions in build receipt`
  - 仅修改上述收据 L5–6：补 Lean 4.33.1（x86_64-unknown-linux-gnu，commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`，Release）及 Lake `5.0.0-src+819816b` 版本文字
  - 源码、依赖、目标 SHA、17 项公理文本均未变。版本文字已收到，不再列为缺失；仍不能等同独立重现或最新后续源码的验证

- **2026-10-09：[`b72a0b1f`](https://github.com/cchx0000/primemother/commit/b72a0b1f2e38a1206b5f05889ba279014cb08f18)**，提交时间 03:01:15 UTC，标题 `P1.2: actual block tilings (i)-(iv), QualifiedMother, BirthLedger/Provenance; 0 sorry`
  - 仅修改 Atlas，新增 `Mathlib.Tactic` 导入。L61–123 构造规范秩区间切点并给出块长、相邻端点相等、先后端点不交不等式、正块长条件下覆盖与 `tiling_exists_iff`；`AtlasTiling` 自身仍只存 `r` / `hr` / `tile_eq`，不含实际路径/路径同构字段。未给唯一性定理；零块长退化情形不能无条件宣称唯一
  - L176–201 新增 `QualifiedMother := Pi < H ∧ birth Pi=true ∧ HasRegAtlas H Pi`、到裸 Mother 的蕴含和 0/1 区分定理。此前 TODO 的资格层/边界源码子项已有明确实现
  - L205–245 新增 ledger 集合、两分支 provenance Prop、所有 H≥2 的 `provenance_complete` 与由给定合格母体得到 tiling 非空的 `provenance_witness`。尚不保存论文 `Prov(H)` 所要求的有序 ledger 及每一成员的完整 atlas 结果族；该 witness 定理的输入是 `QualifiedMother`，不是直接解构整份 provenance
  - 原 birth/展开脚本/主定理和模型前提未改。P1.2 记为部分源码完成，构建/新声明公理输出未收到，不能由旧收据验收

- **2026-10-09：[`67b8f50f`](https://github.com/cchx0000/primemother/commit/67b8f50f92b5f755c708f7cfd79fbaddaf3d664b)**，提交时间 03:05:51 UTC，标题 `P1.3: relabelling invariance, path-sieve identity, B_M(x)=pi(x) (Nat form); 0 sorry`
  - 仅新增 `lean/Theorems/Thm_PrimeMother_Distribution.lean`（131 行），导入 PrimeBirth 与固定版本 Mathlib PrimeCounting；默认 Theorems glob 在配置上涵盖该模块
  - L25–37 给出保根/后继的 `IsChainIso` 和 `chainIso_preserves_crk`，仅涉及规范 Chain 的秩保持。L43–91 给出裸母锥、乘法刻画和 n≥2 时“较早 birth 的母锥包含 n ↔ 非素数”；L97–129 给出 Nat 范围的出生数等于 `Nat.primeCounting` 及出生集合等于素数集合
  - 无直接占位、无新增结论型假设；出生计数由 birth 过滤定义，并未把 primeCounting 直接放入定义。脚本使用既有主定理识别素数。没有实数参数/测度恒等式，也没有 provenance/mother/birth 的一般源传输定理；不将注释中的支持集类比视为测度形式化
  - 四个新增提交及收据目标 SHA 的 Actions/check-runs/statuses/comments 均空。当前 5 模块直接占位为 0，但本轮没有运行构建/测试/公理审计；旧收据不覆盖新增 Atlas/Distribution。P0 当前验证与 P1 剩余目标保持开放，P2 未变

- **2026-10-09：[`40fb96b3`](https://github.com/cchx0000/primemother/commit/40fb96b3a659dcf50bad8d55af7de564461fd5bc)**，提交时间 12:10:33 UTC，标题 `docs: AxiomAudit entry + build receipt for 5b13173eecd3863ed99fb0633d18499521a843c7 (3016 jobs, 34/34 axioms clean)`
  - 先核对父提交 `5b13173eecd3863ed99fb0633d18499521a843c7` 仅为上轮 TODO 同步，跳过自触发。新增内容仅为 60 行构建收据和 55 行 `lean/AxiomAudit.lean`；5 个证明模块、README、论文、工具链/依赖和 Lake 配置均未变
  - 收据 L3–14 指定 `5b13173e`，报告默认 build 退出 0、3016 jobs、0 errors、0 warnings、clean working tree、Lean/Lake 版本和全部 5 模块。该目标与 `67b8f50f`/当前 HEAD 的证明源码和依赖相同，故覆盖当前 Atlas/Distribution；不再沿用“只有旧 4 模块收据”的状态
  - 收据 L16–56 给出完整 34 项公开 theorem 的标准公理输出文本与命令/退出码；审计入口 34 条 `#print axioms` 与源码 34 个公开 theorem 一一对应，无缺漏/多余。4 个直接 import 经 Source 传递导入覆盖 5 模块，包括 Regression；没有给 8 个匿名 examples 和私有 `no_birth_lt_two` 逐项具名输出
  - 输入和完整调用已保存，不再列为完全缺失；但入口首次入库晚于收据目标，默认 Lake target 也不包含根入口，需单独执行。完整原始 build 日志、逐模块/样例执行记录及 exact-checkout 的审计输入来源/执行记录仍需补齐；保留维护者报告与独立重现的区分
  - 本轮只检查源码和已提交证据，未运行 Lean/Lake 或公理审计。目标 SHA 与 HEAD 的 Actions/check-runs 为 0，statuses/comments 为空，树中仍无 CI。P0 更新已收到证据子项；P1 源层/路径/provenance/测度与 P2 的实现缺口未改变

- **2026-10-10：[`82e6eb941ee4b6f1a522e471fc5607b9f836cec4`](https://github.com/cchx0000/primemother/commit/82e6eb941ee4b6f1a522e471fc5607b9f836cec4)**，提交时间 03:41:49 UTC，标题 `P2.1a: return words (normal form) - inductive IsReturnWord + basic theory; 0 sorry`
  - 父提交 `03828712f3c8ca29f0956acad5e0f31566e8c5df` 仅为前次 TODO 同步。此提交只新增 `lean/Definitions/Def_PrimeMother_ReturnWord.lean`（107 行）：`listMax` L21、`IsReturnWord` L54–59 与 9 个公开 theorem；无直接占位
  - 已有词的归纳扩张及非空/首项/max/标签界脚本；没有有限顶点等价关系、无标签同构、规范化逆映射或 `prop:return-normal-form` 所需双射。P2.1a 只记源码基础进展，标题不作为构建验收

- **2026-10-10：[`e2ee630bf8ce95c41e674d6edb48efaa38277e08`](https://github.com/cchx0000/primemother/commit/e2ee630bf8ce95c41e674d6edb48efaa38277e08)**，提交时间 03:44:41 UTC，标题 `P2.1b: elementary returns, simple-return sector, packet, overlap graph; 0 sorry`
  - 只新增 `lean/Definitions/Def_PrimeMother_ReturnPacket.lean`（97 行）。L26–63 定义次数、recurrent、simple-return 的次数部分、elementary return、完整两次类集合及区间交叠/邻接；L65–95 给出 4 个公开 theorem
  - `IsSimpleReturn` 缺论文要求的 pairwise nonisomorphic normalized supports；[0,1,0,1] 提供同长度两个支持的源码层反例。`simpleReturn_packet_card` L74–78 的结论只是 packet 成员次数为 2，`_hs` 未使用，尚不证明注释所说的唯一 endpoints/elementary-return 对应。词/历史双射、受 packet 顶点域约束的图及连通/出生判据仍缺

- **2026-10-10：[`b3953f68d9f6f0fe4406f311802b7b33251711ad`](https://github.com/cchx0000/primemother/commit/b3953f68d9f6f0fe4406f311802b7b33251711ad)**，提交时间 03:50:13 UTC，标题 `P2.1c(i): spine + single-prime return word infrastructure; 0 sorry`
  - 只新增 `lean/Theorems/Thm_PrimeMother_ReturnCombination.lean`（该提交 99 行）：递归 `spine`、`singlePrimeWord` 和 7 个公开 theorem，证明 spine 的 max/长度/末项/合法词，以及 p≥2 时单返回词合法和位置 1 的标签
  - 默认 Theorems glob 在配置上包含此文件；其导入新 Packet → Word，不导入 unary PrimeBirth。尚无 `Nat.Prime` 假设、packet birth、一般有限素数族或反向分类

- **2026-10-10：[`a6a41e3548f54a1288e99fe480249b2bb4c9295a`](https://github.com/cchx0000/primemother/commit/a6a41e3548f54a1288e99fe480249b2bb4c9295a)**，提交时间 03:51:22 UTC，标题 `P2.1c(ii): single-prime elementary return (support length p); 0 sorry`
  - 只扩展 ReturnCombination 至 154 行，新增 4 个 theorem：`singlePrimeWord_length` L63、`singlePrimeWord_one_at_end` L106、`spine_get` L114、`singlePrimeWord_elementary` L135–152
  - 最后声明以 `2 ≤ p` 得到标签 1 在位置 1 和 p+1 的 elementary return，无中间同类；长度 p 的单个支持已构造，但合数也适用，不包含 prime/birth 或完整 singleton packet 结论。全体非空互异素数族的构造、端点互异/完整 packet/路径图和反向分类仍未提交
  - 四提交父链连续，累计仅新增这 3 模块；全读当前 8 模块、审计入口、工具链/锁文件/配置、README 和论文相关段落。旧 5 模块/依赖不变，0 直接占位，公开 theorem 34 → 58；旧收据与入口仍仅覆盖 34 项
  - 四个 SHA 的 Actions/check-runs 均为 0，statuses/comments 均空，无新收据/CI。本轮未运行 Lean/Lake、样例或公理审计；P0 当前覆盖扩至 8 模块/58 项待验证，P2.1 记部分实现，其余优先级保持

- **2026-10-10：[`4cd15d0d691432f45b80f8add8b990d4ab5db536`](https://github.com/cchx0000/primemother/commit/4cd15d0d691432f45b80f8add8b990d4ab5db536)**，提交时间 06:19:51 UTC，标题 `P2.1c(iii): multi-prime packet word; IsReturnWord; 0 sorry`
  - 父提交 `6811a9037adc9d7dcc3a189863026f63049a46dc` 仅同步 TODO；本提交只给 ReturnCombination 增加 195 行，文件由 154 行增至 349 行。其他 7 个库模块、审计入口、收据、论文、README、工具链/锁文件/配置均未变
  - 新定义：`packetWordAux` L176–181、`packetWord` L184–186、`PacketInv` L189–191；依次追加 p−2 个新标签和旧标签 lprev，按 p=2 分支更新尾部状态。初态 [0,1]、空列表输出 [0]；定义不输入素数判定或 birth 结论
  - 6 个新 theorem：`last_le_listMax` L194、`isReturnWord_append_fresh` L200、`getLast?_append_fresh` L228、`packetStep_invariant` L248、`packetWordAux_invariant` L309、`isReturnWord_packetWord` L326。归纳不变量给合法词、长度/最大标签、尾标签与界；最终仅提取 IsReturnWord。输入只要求每项 ≥2，包括合数、重复长度和空列表
  - `PacketInv` 未断言 `w[b - 1]? = some lprev`，也无各返回的两次出现/完整 packet/支持长度记录；仍需位置语义与几何不变量。源码展开可见 `packetWord [2,2] = [0,1,0,1]`（重复支持长度），`packetWord [2,2,2] = [0,1,0,1,0]`（标签 0 三次）；这些不反驳合法词定理，但说明不能把所有 ≥2 列表升级为论文 simple-return/born packet，且不是已执行的 Lean 回归
  - 对照论文 L1257–1297：本提交是多块规范词构造进展；递增互异素数范围内的端点互异、不相邻、完整返回集合、秩准确、路径交叠图与 born 尚无定理，反向分类、历史双射和完整 simple-return 条件亦未补齐
  - 全读当前 8 模块、配置、入口和已提交收据；去注释后直接 sorry/admit/axiom 仍为 0，公开 theorem 58 → 64，匿名 examples 仍为 8。旧收据及 AxiomAudit 只覆盖旧 34 项，新 3 模块缺 30 项输出
  - 本 SHA 的 Actions/check-runs 均为 0，statuses/comments 为空，无新构建收据。提交信息中的 3019 jobs/标准公理声明仅是未附日志的报告；本轮未运行 Lean/Lake、样例或公理审计。仅更新 P0 验证范围和 P2.1 部分进展，不勾选最终验收

- **2026-10-10：[`ade6c9ee16f4ec671077b9f22c42f0738b76e56b`](https://github.com/cchx0000/primemother/commit/ade6c9ee16f4ec671077b9f22c42f0738b76e56b)**，提交时间 07:40:34 UTC，标题 `P2.1 semantic condition: IsSimpleReturnSector + distinct-length bridge; audit covers 65 thms; 0 sorry`
  - 父提交 `728d2a1a70972c891c4a57e4cb133d79b5b032e6` 仅同步 TODO；本提交只改 `Def_PrimeMother_ReturnPacket.lean` 与 `AxiomAudit.lean`。其余 7 个库模块、8 个 examples、论文、README、收据、工具链/锁文件/构建配置均未变
  - 新增 raw slice `returnSupport` L115、`returnSupport_length` L119、相等模式关系 `SupportIso` L131、`not_supportIso_of_length_ne` L137、`IsSimpleReturnSector` L146 与 `sector_of_distinct_support_lengths` L156。`IsSimpleReturn` 的次数限定已明确；长度为 b+1−a 个顶点，而论文 rank 是 b−a 条边，在 elementary-return 范围内两者的互异性等价。桥接以 `hs`（次数条件）和 `hd`（所有不同类的长度互异）为前提；没有把该前提证明为 packetWord 的性质
  - **规范化模型须继续修正**：论文 [L994–997](https://github.com/cchx0000/primemother/blob/ade6c9ee16f4ec671077b9f22c42f0738b76e56b/paper/prime_distribution_birth_mother_provenance.tex#L994-L997) 明定 unary normalization 为 cut-open path `N(J):=J`；[L1220–1224](https://github.com/cchx0000/primemother/blob/ade6c9ee16f4ec671077b9f22c42f0738b76e56b/paper/prime_distribution_birth_mother_provenance.tex#L1220-L1224) 明确该路径非同构后验上就是 ranks 互异。源码 [L127–149](https://github.com/cchx0000/primemother/blob/ade6c9ee16f4ec671077b9f22c42f0738b76e56b/lean/Definitions/Def_PrimeMother_ReturnPacket.lean#L127-L149) 比较 raw 子词的完整相等模式，保留了 cut-open 路径不携带的顶点识别数据；这不是论文所需的归一化路径同构
  - 有限对照：w=[0,1,2,3,1,0,4,2] 从 [0] 依次追加 1,2,3,1,0,4,2；各步不同于末项，且分别不超过当时 max+1=1,2,3,4,4,4,5，满足实际 `IsReturnWord` 扩张条件。0 出现在 {0,5}，1 出现在 {1,4}，2 出现在 {2,7}，3/4 各出现一次；故所有 recurrent 类恰两次，且这三对都是无中间同类的 elementary returns
  - 三个 raw supports 分别为 [0,1,2,3,1,0]、[1,2,3,1]、[2,3,1,0,4,2]。中间支持长度 4，其余长度 6；两个长度 6 的支持在局部位置 1、4 的相等关系分别为 1=1 与 3≠4，所以也不满足 `SupportIso`。因此当前 `IsSimpleReturnSector` 接纳此词，尽管支持边数为 5、3、5，违反论文 distinct ranks 条件；三支持也两两共享原子边，不能仅以连通性排除此例。此分析只指出谓词语义过宽，不否定已写的 `sector_of_distinct_support_lengths` 充分条件，也不声称尚未定义的 Lean return birth 已被反驳
  - 另核对 L110–114 的 raw slice 规范化注释：合法词 [0,1,0,2,1] 的 [1,4] 子词 [1,0,2,1] 不是首次出现编号 [0,1,2,0]。`SupportIso` 对一致标签重命名不敏感，所以该注释错误与上述 cut-open 建模差距分开记录；只修标签编号不足以证明路径非同构等价于秩互异
  - AxiomAudit 增加 3 个 return 导入与 31 个 `#print axioms`，共 65 个；覆盖全部 8 模块的导入闭包，但 67 个公开 theorem 中仍缺 `listMax_nil`、`listMax_cons` 的具名命令。文件头“all 5”与 Packet 注释“(6)”分别应按当前覆盖及实际 7 项同步。没有新增执行输出；已有 34 项收据继续只覆盖旧模块
  - 全读 8 模块、配置、入口和最新已提交收据，对照上述论文定义；去注释后直接 sorry/admit/axiom 仍为 0，公开 theorem 64 → 67。未发现原主定理削弱、结论型假设或新增依赖。历史双射、正确 cut-open sector/秩等价、精确 packet、支持几何、birth 和正反分类仍待完成
  - 本 SHA 的 Actions/check-runs 均为 0，statuses/comments 空，无新构建日志。有限词检查在审计器中按源码定义求值，不是 Lean/Lake 编译或内核验收；本轮未运行 Lean、样例或公理审计。P0 扩至 67 项待验收，P2.1 只勾选新增定义/条件桥接的源码子项

- **2026-10-10：[`3d0c1e9b6ba6307a59d8a66d46af05c6a43e4ae5`](https://github.com/cchx0000/primemother/commit/3d0c1e9b6ba6307a59d8a66d46af05c6a43e4ae5)**，提交时间 09:12:34 UTC，标题 `P2.1 packet geometry: PacketInv tracks left-endpoint label + per-step elementary return; audit covers 67 thms; 0 sorry`
  - 父提交 `ecc6b7586a5a6632f1435fb6eedb4a4c4aeb6d49` 仅同步 TODO。此提交只改 ReturnCombination 与 AxiomAudit；其余 7 模块、论文、README、工具链/锁文件/构建配置未变
  - `PacketInv` L192–195 新增 `w[b - 1]? = some lprev`。单步保持证明在 p=2 时利用原末项，在 p≥3 时利用末个 fresh label；`isReturnWord_packetWord` 初态 [0,1] 已补第 9 个条件。这关闭了上轮指出的左端点标签对应源码缺口
  - 新 `packetStep_elementary` L348–391 从 p≥2 和 PacketInv 得到单步扩张词的 elementary return，标签 lprev、端点 b−1 与 b−1+p；内部位置 b 用末标签不等，其余位置用 fresh labels 的下界排除同类。没有把待证素数性或最终 birth 放入假设，也没有削弱原合法词定理
  - 该结论只针对单步扩张词；`packetWordAux_invariant` L328–340 未收集每项端点记录，尚无旧 elementary returns 沿后续追加保留到最终词的统一定理。两次出现、不同类/端点、无额外返回、最终完整 packet/支持秩/路径图、cut-open sector 和 birth 分类继续开放
  - 静态展开 [2,2,2] 得 [0,1,0,1,0]：三步分别产生 [0,2]、[1,3]、[2,4]，均为 elementary returns，但标签 0 出现三次。此对照与新定理兼容，说明不能由 p≥2 或逐步 elementary 直接推出简单完整 packet；未作为 Lean 回归执行
  - 全读 8 模块并对照论文 L994–997、L1220–1226、L1257–1297。公开 theorem 67 → 68，ReturnCombination 17 → 18；直接 sorry/admit/axiom 仍为 0，examples 仍为 8。AxiomAudit 仅增 `packetStep_elementary` 一条，命令 65 → 66，仍漏 `listMax_nil`/`listMax_cons`。标题“67 thms”不等于实际数量；入口“all 5”/Packet“(6)”/ReturnCombination“(17)”均需同步

- **2026-10-10：[`05fc37709ac55b9fbbf63a428b0a1374ac9e6bd2`](https://github.com/cchx0000/primemother/commit/05fc37709ac55b9fbbf63a428b0a1374ac9e6bd2)**，提交时间 09:12:34 UTC，标题 `docs: build receipt for 951ff94519b8b17dc8119c5e0bee45edc5f4577a (3019 jobs, 67/67 axioms clean, 0 sorry)`
  - 只新增 `docs/receipts/build-951ff94519b8b17dc8119c5e0bee45edc5f4577a.md`（33 行），不改变代码/依赖。正文报告固定工具链下默认 build 退出 0、3019 jobs、0 errors/0 warnings；另报告公理检查退出 0、标准公理且无 sorryAx。它是新增维护者证据，不能继续笼统写“没有新构建收据”
  - 收据目标 `951ff94519b8b17dc8119c5e0bee45edc5f4577a` 不在本轮可见父链，直接 GitHub commit API 返回 422 “No commit found for SHA”。暂无法确认目标 checkout/tree 与 `3d0c1e9b…` 的对应；须补可解析精确 SHA 或明确内容等价/执行来源，不能只按描述相似替换目标
  - 收据声称 67 条 `#print axioms`，提交入口实际 66 条、公开 theorem 实际 68 条。正文仅列 `packetStep_invariant`、`packetStep_elementary` 两条 [propext, Quot.sound] 输出；这两条已收到，但不是全量输出。补齐遗漏命令、修正数量并提交同一可解析 SHA 的完整执行记录后再验收
  - 本轮两个 SHA 的 Actions/check-runs 均为 0，statuses/comments 均空；无 CI workflow。未独立运行 Lean/Lake/样例/公理审计，未把收据目标不可解析解释为构建失败。旧 34 项报告继续覆盖不变的一元源码；P0 当前全量验收及 P1/P2 剩余目标仍开放

- **2026-10-10：[`fbaca622`](https://github.com/cchx0000/primemother/commit/fbaca6225b108cd54364cf56964ec2c1c81e540c)**，提交时间 10:13:42 UTC，标题 `audit: AxiomAudit gains listMax_nil + listMax_cons (68/68 inputs clean); fix stale section counts`
  - 核对父提交 `7659dc97` 仅同步 TODO 后，本提交只改 AxiomAudit：补 `listMax_nil`、`listMax_cons`，输入 66 → 68，和此时 68 个公开 theorem 逐项匹配。库源码、依赖、论文均未变；不再列两项输入缺失
  - “all 5”→“all 8”、ReturnWord“(7)”→“(9)”、ReturnPacket“(6)”→“(7)”已修。ReturnCombination“(17)”未修，当时实际 18 项、当前后续新增后为 22 项；标题不作为输入已执行的证据

- **2026-10-10：[`f63b59db`](https://github.com/cchx0000/primemother/commit/f63b59db874d16da97250caede5ee6c062e4a90b)**，提交时间 10:14:57 UTC，标题 `docs: build receipt for fbaca6225b108cd54364cf56964ec2c1c81e540c (3019 jobs, 68/68 axioms clean, 0 sorry)`
  - 只新增 40 行收据。目标 `fbaca622` 可解析且是其直接父提交；对 `3d0c1e9b` 的比较确认库源码/依赖相同，变化只有 TODO、旧收据与审计入口。这关闭了新证据无法对应已发布 SHA 的缺口，不将收据末尾“将重试 push”的历史文字当作当前仍未推送
  - L3–9 报告 SHA、Lean 4.33.1 / Lake 5.0.0-src+819816b、`cd lean && lake build`、退出 0、3019 jobs、0 errors/0 warnings。L20–31 报告通过已提交入口执行 68 项公理审计且无 sorryAx，只展示 listMax 两项无公理输出；原始完整日志、逐模块/回归记录与 clean checkout 声明尚缺
  - L35–40 说明旧 `951ff945…` 目标因重提交脱离 master，并以此收据替代。此为维护者说明，不替旧目标建立 tree 等价。新目标的输入数量已正确；全量逐项输出仍缺，且收据不覆盖随后新增四个 theorem

- **2026-10-10：[`fd00c30c`](https://github.com/cchx0000/primemother/commit/fd00c30c72c8d76aee4eab95b5f07928f41702e1)**，提交时间 11:16:43 UTC，标题 `P2.1: elementaryReturn_append_preserved (old returns survive extension); 0 sorry`
  - 只在 ReturnCombination L423–441 新增通用保持引理，并增加一条公理输入。原 elementary-return 的端点都在旧 w 范围内，追加后用 `getElem?_append_left` 保持端点与中间位置；声明无额外合法词、素性或互异前提
  - 该源码确实关闭了“缺通用 append 保持定理”的任务；但未把它接入 `packetWordAux_invariant`，未保存每步到最终词的完整记录。尾部可以再次加入同类，故不推出全词次数仍为 2 或完整 packet 保持。公开 theorem / 审计输入均 68 → 69

- **2026-10-10：[`5b77fc70`](https://github.com/cchx0000/primemother/commit/5b77fc70e1afe7dce035ba4810a88f7e1e7de46b)**，提交时间 11:17:54 UTC，标题 `P2.1: packetWord_singleton unfolds to explicit block; 0 sorry`
  - 只新增 `packetWord_singleton` L444–447 与一条输入，69 → 70。对任意 p，展开 builder 后由 rfl 得 `[0,1] ++ (range' 2 (p−2) ++ [0])`；只是词等式，未声明 exact singleton packet、simple-return、支持长度或 birth

- **2026-10-10：[`d6f3c609`](https://github.com/cchx0000/primemother/commit/d6f3c6096befe892cfdd4b334f00d6206ee719cd)**，提交时间 11:18:59 UTC，标题 `P2.1: packetWord_singleton_length; 0 sorry`
  - 只新增 L450–455 的 singleton 长度 p+1 与一条输入，70 → 71。正确保留 p≥2 前提，按前条等式及 range 长度化简；该前提允许合数，不能当作 prime birth 或完整 packet 结论

- **2026-10-10：[`eca92183`](https://github.com/cchx0000/primemother/commit/eca9218350a110317f045c0b6a880dc896575dfa)**，提交时间 11:20:08 UTC，标题 `P2.1: packetWord_two_two regression (repeated prime gives repeated support); 0 sorry`
  - 只新增 L460–462 的 `packetWord [2,2] = [0,1,0,1]` 具名回归脚本与一条输入，71 → 72。注释中的重复支持长度由该词可作静态核对，但 theorem 自身没有次数、elementary-return/长度或 sector 判决结论；这些验收不能随注释自动勾选
  - 本轮完整静态扫描 8 模块：72 个公开 theorem / 72 个唯一输入，直接 sorry/admit/axiom 均 0，8 个匿名 examples 未改。[]、[2]、[4]、[2,3,5]、[2,2]、[2,2,2] 的有限源码模型展开与既有几何对照一致；这是静态模型检查，未执行 Lean/Lake 或公理审计
  - 六个非 TODO 提交逐项查得 Actions/check-runs 均 0、statuses/comments 均空，无新 workflow。最后四个 theorem 晚于可解析的 68 项维护者收据，缺当前 SHA 的完整构建/输出；旧模型前提、主定理及其依赖、SupportIso 差距、README/论文/配置均未改。P0/P1/P2 未完成总项保留

- **2026-10-10：[`f0ae0fa7`](https://github.com/cchx0000/primemother/commit/f0ae0fa7a51fb2b6f9b99d5d97eb3d9f18788a3d)**，作者时间 12:07:16 UTC / 提交时间 12:07:41 UTC，标题 `P2.1: packetWord two-three distinct-prime packet regression; 0 sorry`
  - 父提交 `6337c823` 仅同步 TODO；本提交只追加 ReturnCombination 134 行、AxiomAudit +11/−1。10 个新 theorem 把公开数与审计输入 72 → 82；ReturnCombination 标题“(17)”改为正确的“(32)”
  - L477–518 明确 [2,3] 的词、类 0/1 的两组端点、恰两次出现和完整 packet={0,1}。L521–573 证明 count-only simple-return 及所有 elementary returns 恰为两组，不再把这个具体案例的次数/完整 packet/无额外返回列作缺失
  - L578–588 给类 0/1 的边数互异，未直接调用任意不同类/顶点数版本的 sector 桥接；L593–596 给邻接见证，不是正式图同构声明。一般 builder 记录、任意非空互异素数族、singleton 完整 packet、cut-open 语义与 birth 正反分类未改
  - 全量静态扫描：8 模块、82 个公开 theorem、82 个唯一具名输入逐项相等、8 个匿名 examples、直接 sorry/admit/axiom 为 0。按源码作有限模型展开，[]/[2]/[4]/[2,3]/[2,3,5]/[2,2]/[2,2,2] 的词与几何符合当前声明；[2,3] 得两组端点 (0,2)/(1,4)、支持边数 2/3、packet {0,1} 与一条边。这不是已执行 Lean 回归
  - 原一元主定理、递归依赖、全部配置、论文和 README 未变；本提交无 Actions/check/status/comment 验证记录

- **2026-10-10：[`15670425`](https://github.com/cchx0000/primemother/commit/1567042595586539a14a7c4b4f002871d348f151)**，作者时间 12:07:29 UTC / 提交时间 12:07:41 UTC，标题 `docs: build receipt for a518361683ca53381346932721bf9b73cc1b754f (3019 jobs, 82/82 axioms clean, 0 sorry)`
  - 只新增 56 行维护者收据，报告 3019-job 默认 build 与 82 项公理审计退出 0、0 errors/0 warnings，并给 Lean/Lake 版本及本轮 10 项标准公理文本。其 82 项输入数量与当前文件相符；展示数量为 10，不能称为全部 82 项输出
  - 目标 `a518361683ca53381346932721bf9b73cc1b754f` 返回 422 “No commit found”，未建立与直接父源码 `f0ae0fa7` 的 tree 对应。原始完整日志、逐模块/回归记录和 clean checkout 声明缺失；未独立运行 Lean，不能据缺证据断言实际构建失败

- **2026-10-10：[`d0041c5d`](https://github.com/cchx0000/primemother/commit/d0041c5d2f019ea7b040c5025e9aa6210ce711bc)**，提交时间 12:08:01 UTC，标题 `docs: build receipt for f0ae0fa994ea3e7e1d19ff0bda4dc6eb3a6eb18 (3019 jobs, 82/82 axioms clean, 0 sorry)`
  - 仅改收据文件名与 L3 的目标字段，其余 55 行内容未变，Lean 源码未改。更正值 `f0ae0fa994ea3e7e1d19ff0bda4dc6eb3a6eb18` 为 39 字符，API 仍返回 422；实际发布源码是 `f0ae0fa7a51fb2b6f9b99d5d97eb3d9f18788a3d`，不能擅自替换目标并验收
  - 当前收到新 10 项文本与 82-clean 摘要，但来源对应、完整 82 项输出及独立重现未完成；旧可解析 68 项收据的历史有效范围保留。三个新增 SHA 均无 Actions/check-runs，statuses/comments 均空，无 CI workflow；P0/P1/P2 总项仍开放

- **2026-10-10：[`23b93b81`](https://github.com/cchx0000/primemother/commit/23b93b81baac87ab07bd85c70bde5a010f8d329d)**，提交时间 12:55:56 UTC，标题 `P2.1: packetWord singleton complete classification (elementary/packet/simpleReturn); 0 sorry`
  - 父提交 `00ff14f7` 仅同步 TODO；本提交只给 ReturnCombination 追加 238 行，AxiomAudit 增 8 条命令并将分节 (32) 改为 (40)。8 个新公开 theorem 与输入使 82 → 90；旧证明、定义与全部配置未改
  - L611–660 的三个位置引理覆盖展开词 [0,1,…,p−1,0] 的 0/1/p/内部四种位置；L664–721 的非零类出现唯一性只声称至多一次。L725–834 的四个声明给 elementary return (0,p)、零类精确位置 {0,p}、完整 packet={0} 和 count-only simple-return。所有结果假设 p≥2，允许合数，未偷渡素性或 birth 结论
  - 此处是 `packetWord [p]`，不是旧 `singlePrimeWord p`；不能继续把前者的完整 singleton packet/次数性质列作缺失，也不能把进展记为后者已有完整 packet 定理。尚无显式 singleton sector、所有 elementary returns 的 iff 分类、图/连通性或 born 结论；现有位置/次数事实可支持后续桥接
  - 有限静态模型核对 p=2…1000 全部通过上述几何/次数性质；p=0/1 输出 [0,1,0]，体现长度/端点定理中 p≥2 前提的必要性。旧 []/[2,3]/[2,3,5]/重复长度及 5、3、5 sector 对照继续成立。这是审计器按源码求值，不是 Lean/Lake 执行
  - 全读 8 模块，直接 sorry/admit/axiom 为 0；90 个公开 theorem 与 90 个唯一 #print 输入逐项相等，8 个 examples/1 个私有辅助未改。一般递归几何记录、cut-open 语义、历史双射、任意非空互异素数族及 birth 正反分类未完成；本 SHA 无 Actions/check/status/comment 记录

- **2026-10-10：[`23a3dcc3`](https://github.com/cchx0000/primemother/commit/23a3dcc3b3eba06d623a3edd0a2bf9758946dec1)**，提交时间 12:56:27 UTC，标题 `docs: build receipt for 23b93b81baac87ab07bd85c70bde5a010f8d329d (3019 jobs, 90/90 axioms clean, 0 sorry)`
  - 只新增 55 行收据。L3 的完整 40 字符目标可解析，恰为直接父源码 `23b93b81`；目标与 HEAD 的 Lean tree 均为 `06a2b0a6c01ffd98ee3f832df29bd5542a465ff9`，90 项入口 blob 均为 `37307d85601c5cb33fcf53b9680e8339be1a5e70`。源码与审计输入对应已核实，旧 82 项失联目标缺陷不适用于此收据
  - 维护者报告固定 Lean/Lake 版本、默认 build 退出 0/3019 jobs/0 errors/0 warnings、clean working tree、公理审计退出 0 和 90 项均只含标准公理。L45–52 展示新增 8 项：前两项为 propext/Quot.sound，其余六项另含 Classical.choice；未展示完整 90 项输出或原始 build/audit 日志
  - 新报告已覆盖当前源码的声明范围且补上 clean 状态文字，不能写成无收据/目标不明；也不能把 8 行输出扩张成全部 90 行、把维护者报告当作本审计器独立重现。逐模块/回归执行记录及当前完整依赖输出仍待补
  - 本 SHA 以及自身 TODO 提交 `00ff14f7` 的 Actions/check-runs 均为 0，statuses/comments 均空，树中无 workflow。没有运行 Lean/Lake；P0 当前证据来源子项推进，P0/P1/P2 总项保持开放

- **2026-10-10：[`fbc8fb7ec89ccd20b5da86ba9e4e9f1315eabc37`](https://github.com/cchx0000/primemother/commit/fbc8fb7ec89ccd20b5da86ba9e4e9f1315eabc37)**，提交时间 13:47:10 UTC，标题 `P2.1: packetWord block records接入最终词 (0 sorry)`
  - 父提交 `ed9e6e564e51939045b122df04c4a49c03681fbf` 仅同步 TODO，已跳过自触发。本提交只追加 ReturnCombination 135 行、AxiomAudit 增 4 条命令并将分节 (40) 改为 (44)，公开 theorem/唯一审计输入均 90 → 94；旧定义/证明、其余 7 模块、配置/依赖和论文未改
  - `blockRecordsAux` L855–860 与 packetWordAux 采用相同状态递归；`packetWordAux_append_suffix` L865–879 对任意输入给输出=input++suffix。L889–919 的逐记录 theorem 用单步 elementary-return、suffix append 保持和 PacketInv 归纳，将每个记录 `(c,a,b)` 接入最终词；L947–969 专门化到 packetWord 初态，空列表显式分支只证明空记录上的量化
  - `blockRecordsAux_support` L926–940 无素性/互异/≥2 或 invariant 前提，给 `map (b−a) records = ps` 的有序列表等式。几何两条 theorem 才需要每项 ≥2，aux 版另需 PacketInv；没有把完整 packet/次数或 birth 结论放进假设。源码关闭“逐块记录保留至最终词”的缺口，但尚无所有 elementary returns 的反向覆盖、类/端点互异、恰两次出现、无额外两次类、完整 packet/路径图/sector 或 birth 分类
  - 静态按定义展开 [3,2,5] 得 [0,1,2,0,2,3,4,5,0] 与 [(0,0,3),(2,2,4),(0,3,8)]，类 0 三次而记录支持边数仍为 [3,2,5]。此例输入互异但未递增，说明不能省略论文递增排列所提供的端点/类条件；不反驳本轮每项 ≥2 的逐记录定理。合数、重复长度及空列表也均在适用范围，不能据“prime block”注释推出 born 结论
  - 去注释全库扫描直接 sorry/admit/axiom 为 0；94 个公开 theorem 与 94 个唯一输入逐项匹配，8 个 examples/1 个私有辅助未改。SupportIso 的 raw-pattern/cut-open 差距、历史双射、一般 packet 分类和源层对应未改；未运行 Lean/Lake

- **2026-10-10：[`dfbe1671e5d66e24afff7c1f48737dc7906bd9dc`](https://github.com/cchx0000/primemother/commit/dfbe1671e5d66e24afff7c1f48737dc7906bd9dc)**，提交时间 13:47:51 UTC，标题 `docs: build receipt for fbc8fb7ec89ccd20b5da86ba9e4e9f1315eabc37 (3019 jobs, 94/94 axioms clean, 0 sorry)`
  - 只新增 41 行收据；完整目标可解析且为直接父源码 `fbc8fb7ec89ccd20b5da86ba9e4e9f1315eabc37`。目标与本提交 Lean tree 同为 `21f715273c013aa689bb6282e8b7dc13c537b148`，入口 blob 同为 `a081e8f2e20000e08e0739db04a9b4c87de79f4f`，均已含本轮四条新命令。源码与审计输入对应明确，不继承旧 82 项失联目标缺陷
  - 收据报告固定 Lean/Lake 版本、默认 build 退出 0/3019 jobs/0 errors/0 warnings，公理审计退出 0/94 项仅标准公理且无 sorryAx。L35–38 实际展示 4 项：append_suffix 为 [propext]，其余三项为 [propext, Quot.sound]；不是全部 94 项输出，也不是本审计器独立内核重现
  - 本次未写 clean working tree，缺完整 build/audit 原始日志、全部 94 项当次输出和逐模块/回归记录；上一份 90 项的 clean 声明只适用于它自己的执行报告，不转移到本轮。两个新增 SHA 的 Actions/check-runs 均为 0，statuses/comments 均空，树中无 workflow。没有运行 Lean/Lake，不把未独立验收解释为实际构建失败；P0/P1/P2 总项继续开放

后续审计从上述提交游标之后按提交顺序处理；本审计器自身仅修改 `todo.md` 的提交不触发重复写入。若出现历史分叉、缺失提交或并发修改，先重新比较 HEAD 和最新文件，不覆盖他人变更。

- **2026-10-10：[`8d2a7c65`](https://github.com/cchx0000/primemother/commit/8d2a7c65aa323a5d27ed0b94acefa1db02b079f7)**，标题 `P2.1: block-record classes strictly increase for sorted input (0 sorry)`
  - 父提交 `23c77d47` 仅同步 TODO，已跳过自触发。本提交只追加 ReturnCombination 165 行、AxiomAudit 增 4 条命令并将分节 (44) 改为 (48)，公开 theorem/唯一审计输入均 94 → 98；旧定义/证明、其余 7 模块、配置/依赖和论文未改
  - `blockRecordsAux_classes_lb` L989–1033 与 `blockRecordsAux_classes_sorted` L1041–1094 的准确前提为 SortedLT、每项 ≥2、PacketInv 和头为 2 时 lprev<llast。递增输入排除尾部 2，p>2 分支用新标签下界；公共 `packetWord_classes_sorted` L1099–1125 专门化到 [0,1]，只留 SortedLT 与每项 ≥2。无素性或结论型假设，关闭相应域内的记录类互异缺口
  - `packetWord_blocks_support_sorted` L1129–1134 仅需 SortedLT，由既有有序支持列表等式直接推出；无 ≥2/素性前提。仍只是记录层，不含任意 actual return 的反向覆盖、恰两次出现、完整 packet、sector、路径图、birth 或历史双射。旧逐记录最终词接入、singleton/[2,3] 完整 packet 保留
  - 去注释静态扫描 8 模块直接 sorry/admit/axiom 为 0，98 个公开 theorem 与 98 个唯一输入逐项匹配；8 个 examples/1 个私有辅助未改。未运行 Lean/Lake，静态脚本不作编译验收

- **2026-10-10：[`3526d4e1`](https://github.com/cchx0000/primemother/commit/3526d4e136727a0bca088c952fc9b161c05ef89a)**，标题 `docs: build receipt for c0f8ab25db3ccefbb59d80d45519628855677f10 (3019 jobs, 98/98 axioms clean, 0 sorry)`
  - 仅新增 41 行收据；报告固定 Lean/Lake、默认 build 退出 0/3019 jobs/0 errors/0 warnings，以及公理审计退出 0/98 项仅标准公理且无 sorryAx。L35–38 展示新增四条：前三条为 [propext, Classical.choice, Quot.sound]，支持有序条为 [propext, Quot.sound]；已收到输出文本，不等于独立检查
  - 所写 40 字符目标 `c0f8ab25db3ccefbb59d80d45519628855677f10` 不在本轮父链；commit API 独立返回 422 “No commit found”，Git commit 和该 ref 下入口均返回 404。实际直接父源码是 `8d2a7c65…`，其与本提交 Lean tree 同为 `9bcc7732b529a31d9e150bb7d8a1eb51f6d7e927`、入口 blob 同为 `7a8ac2f6ebb4f4bb7e0322889f10e4cc92ea8e25`；不能只按四条名字相同便把收据归到此源码
  - 尚缺目标对应、clean checkout、完整 build/audit 原始日志及全部 98 项当次输出。旧 90/94 项可解析目标与来源对应继续有效，90 项 clean 字段不转移，本次问题不改写其历史。两个新增 SHA 的 Actions/check-runs 为 0，statuses/comments 为空，无 workflow。未运行 Lean/Lake，不将来源不明解释为已证实构建失败

## P0：先让当前一元模型成为可复现、无占位的内核检查结果

- [ ] **P0.1 建立当前完整构建基线**
  - 路径：`lean/lean-toolchain`、`lean/lakefile.lean`、`lean/lake-manifest.json`；当前 8 个库模块为原 Source、Atlas、PrimeBirth、Regression、Distribution，加 ReturnWord、ReturnPacket、ReturnCombination。默认 Theorems glob 含 ReturnCombination → ReturnPacket → ReturnWord；旧 Distribution → PrimeBirth → Atlas → Source 链未改
  - [x] 已收到旧 5 模块精确 SHA 的构建摘要：`docs/receipts/build-5b13173eecd3863ed99fb0633d18499521a843c7.md:3–14` 报告 `cd lean && lake build`、退出 0、3016 jobs / 0 errors 和 5 模块覆盖。`5b13173e` 与当前保留的旧 5 模块/依赖相同，但不含新增 3 模块；旧 614-job 收据作为历史证据保留
  - [x] 旧 5 模块收据已补 Lean/Lake 版本文字、0 warnings 与 clean working tree 报告。它们是维护者已提交的证据文本，不是本审计器独立运行所得；不再将这些字段列为完全缺失
  - [x] 已收到 `f63b59db` 的 3019-job / 0 errors / 0 warnings / 退出 0 维护者摘要，目标 `fbaca6225b108cd54364cf56964ec2c1c81e540c` 已解析并位于当前父链；其 8 模块库源码与 `3d0c1e9b` 相同。该收据给 Lean/Lake 版本并替代旧失联目标报告；它只对应历史 68 项范围，不覆盖随后新增的 30 个 theorem
  - [x] 历史 `15670425` / `d0041c5d` 的 3019-job / 82 项 clean 摘要与 10 项 [2,3] 输出已收到；其更正目标 `f0ae0fa994ea3e7e1d19ff0bda4dc6eb3a6eb18` 和原目标 `a5183616…` 仍是上轮已确认的失联字段。该历史来源缺陷不改写，也不套用于下述可解析的 90/94 项报告
  - [x] 历史 `23a3dcc3` 收据明确指向可解析源码 `23b93b81baac87ab07bd85c70bde5a010f8d329d`，报告 3019 jobs / 0 errors / 0 warnings / 退出 0、固定 Lean/Lake 版本和 clean working tree；目标已含 90 项入口。该报告的来源对应保留，不把其 clean 字段转用于后续源码
  - [x] 上轮 `dfbe1671e5d66e24afff7c1f48737dc7906bd9dc` 收据指向实际直接父源码 `fbc8fb7ec89ccd20b5da86ba9e4e9f1315eabc37`，报告 3019 jobs / 0 errors / 0 warnings / 退出 0、固定 Lean/Lake 版本和 94 项 clean。目标与当时收据提交的 Lean tree 相同，已含全部 94 项入口；该历史源码/输入对应仍有效，不覆盖本轮新增四声明
  - [x] 当前 `3526d4e1` 的 3019-job / 98 项 clean 摘要及 4 项输出已收到；所写目标 `c0f8ab25db3ccefbb59d80d45519628855677f10` 经 commit API 返回 422，Git commit/目标入口返回 404，暂不能绑定到实际源码 `8d2a7c65…`
  - 剩余：先补新 98 项收据的可解析精确目标，或可核验的内容等价/执行来源；再提供当前 `8d2a7c65aa323a5d27ed0b94acefa1db02b079f7` 的完整 8 模块 build/audit 原始日志、全部 98 项逐项输出、clean checkout 和模块/回归执行记录，并独立重现。新收据没有 clean working tree 字段，旧 90 项中的文字不能补足；旧 94 项已核实的来源保留。没有可访问 CI run，不把来源待核或未独立验证解释为实际构建失败
  - [x] 当前 Atlas/Distribution 保留旧 34 项逐项文本；当前实际源码 `8d2a7c65…` 已包含完整 98 项 `lean/AxiomAudit.lean`，输入位置明确；新收据目标与该输入的执行对应仍待核。根入口不在默认 target/glob 内，仍须单独运行 `cd lean && lake env lean AxiomAudit.lean` 并保存完整原始输出；旧 `40fb96b3`/`5b13173e` 的脚本时间差只作为历史证据边界保留
  - 在固定工具链干净 checkout 上运行 `cd lean && lake build` 及 `lake build Definitions Theorems`，覆盖全部 8 模块。另检查 ReturnWord 单模块及新导入链，不凭有无显式 import 推断编译成败。必要时先取固定依赖及 mathlib cache；记录精确 SHA、Lean/Lake 版本、checkout 状态、命令、退出码、warning 和原始日志
  - 验收：当前同一精确源码提交的完整默认构建退出 0，8 个库模块和扩展后的审计入口实际包含；说明所有 warning。缓存、单模块或文字 “Verified” 不替代该收据，不通过移除默认 target 凑通过

- [ ] **P0.2 验证已补完的良基递归展开与基础出生规则**
  - 路径：`lean/Definitions/Def_PrimeMother_Atlas.lean:129–172`；声明 `birth`、`birth_E` L139、`birth_root` L144、`birth_succ_succ` L153
  - [x] 源码修复：`36add88e` 已消除最后直接占位。既有 P1.2 扩展及本轮 P2.1 新增均未改变 birth 定义、这三个引理的目标/脚本或严格先前阶段依赖
  - [x] 旧 34 项收据（对应当前未改模块）L33–35 给出这三个引理的具名公理文本，均列 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx`，并报告构建/审计退出 0；入口已保存
  - 剩余：P0.1 的完整原始执行日志及独立重现；旧 94 项报告的源码/入口定位继续有效，新 98 项来源问题按 P0.1 补齐。复核 `WellFounded.fix_eq` 展开、`show` / `congr 1` / `propext`、见证重组和 0/1 边界。不再把已收到的报告写成缺失
  - 验收：固定工具链上的当前三个引理编译成功，完整传递公理输出无 `sorryAx`；定义没有素数判定或最终结论型输入。收到当前源码报告与独立重现须区分

- [ ] **P0.3 验证已提交的主定理证明链**
  - 路径：`lean/Theorems/Thm_PrimeMother_PrimeBirth.lean:19–115`；声明 `birth_ge_two` L21、`birth_iff_no_earlier_mother` L36、`birth_iff_prime` L58
  - 当前状态：主定理自 `3e9d7d3` 已无直接占位；`36add88e` 补齐其展开依赖。本轮 PrimeBirth 及其 Atlas/Source 依赖均未改，原目标、递归与模型假设保留
  - [x] 旧 34 项收据（对应当前未改模块）L48–50 给出 `birth_ge_two`、`birth_iff_no_earlier_mother`、`birth_iff_prime` 输出，均只有三项标准公理；对应当前 Atlas/Distribution 所在的相同源码/依赖，审计入口已保存
  - 剩余：P0.1 完整原始日志和独立重现；旧 94 项入口与其目标 SHA 的对应保留，当前 98 项执行来源按 P0.1 补齐。检查 L21–32 的 0/1 边界；L36–55 的展开/if 两分支；L71–82 的非平凡素因子和严格范围；L85–104 的归纳、商非 0/1 与 atlas 见证；L107–115 的素数定义方向
  - API 依据：[固定版本 Basic.lean L68–77](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Nat/Prime/Basic.lean#L68-L77)、[Defs.lean L107–120](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Nat/Prime/Defs.lean#L107-L120)、[Defs.lean L407–408](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Nat/Prime/Defs.lean#L407-L408)
  - 验收：原始目标 `∀ n, 2 ≤ n → (birth n = true ↔ Nat.Prime n)` 不削弱、不添加结论型假设；当前完整文件编译且整个证明链不依赖占位

- [ ] **P0.4 执行回归测试并扩展当前内核依赖收据**
  - 路径：`lean/Theorems/Thm_PrimeMother_Regression.lean:14–107`、当前 8 个库模块、已提交 `lean/AxiomAudit.lean`；仍需完整执行日志
  - [x] `9473ec06` 的 0、1、2、3、4、6、9、25 共 8 个证明式 examples 保留，仍在默认 glob 范围内。`birth` 为 noncomputable，样例是等式证明；25 借用主定理在 5 上的实例，不是主定理独立正确性证据
  - [x] 既有收据 L22–55 给出旧 5 模块全部 34 个公开 theorem 的具名公理文本，审计入口的 34 个命令与该范围逐项匹配；Source 9 + Atlas 17 + PrimeBirth 3 + Distribution 5 均已覆盖。各项是标准公理子集或无公理；此完成子项仅指收到文本并核对覆盖，不等于实际重跑
  - [x] 旧 5 模块完整审计输入与调用已提交，包含 Regression 导入；维护者报告该范围审计退出 0。默认 build 不包含此根入口，必须单独调用
  - [x] `ade6c9ee` 已扩展至 8 模块导入闭包；`fbaca622` 补齐 listMax 两条，后续新增 theorem 均同步输入。当前 **98 个唯一具名命令完整匹配全部 98 个公开 theorem**，无遗漏/重复/多余；ReturnCombination 小标题已由 (44) 修为 (48)。实际源码 `8d2a7c65aa323a5d27ed0b94acefa1db02b079f7` 已含同一入口；这里只确认输入覆盖，不为新收据的失联目标建立执行对应，未独立执行
  - [x] 旧失联目标的两条 packetStep 输出、可解析 68 项摘要、历史 82 项的 10 个 [2,3] 输出及 90 项的 8 个 singleton 输出保留原适用范围。上轮 `dfbe1671e5d66e24afff7c1f48737dc7906bd9dc` 报告实际源码 `fbc8fb7ec89ccd20b5da86ba9e4e9f1315eabc37` 的 94 项 clean/退出 0，展示四条记录/支持几何的标准公理输出；该对应继续保留。本轮收到另四条类/长度有序输出文本，名字与当前入口相符，但收据目标来源待核
  - 当前缺口：核实新收据目标后，在当前同一精确 SHA 提交全部 **98 项**逐项输出及完整执行日志。新 3 模块为 ReturnWord 9 + ReturnPacket 7 + ReturnCombination 48 = 64 项；最新收据只展示新增 4 项，未附其余 94 项当次输出。历史文本不能拼接为同一 SHA 的完整执行日志；输入/分节计数已核实，执行目标、完整输出、checkout/执行记录和独立内核重现仍待补
  - [x] 已提交 [2,2] 词等式、singleton 展开/长度、[2,3] 的完整 packet/端点分类/边数互异/邻接 10 项，以及上轮 p≥2 的 singleton 位置/次数/elementary/完整 packet/count-only simple-return 8 项。`packetWord [2]` 与 `[4]` 的这些性质已有一般 singleton theorem 覆盖，不再列为源码缺失；其具体内核实例/sector/birth 验收仍开放。保留旧 `singlePrimeWord` p=2/p=4、packetWord []/[2,3,5]/[2,2,2]、[0,1,0,1] 的重复长度/sector 判决及 5、3、5/raw slice 对照。singleton 8 项及上轮四项记录/支持几何均保留其精确源码对应输出，[3,2,5] 顺序对照保留；本轮四项类/长度有序的输出来源待核。补递增合数与含 0/1 输入的前提边界；均未独立执行 Lean
  - 剩余：在当前已含入口的精确 SHA 保存完整执行日志和每个模块/样例检查记录。旧 34/94 项文本以及新 98 项报告不能扩张成所有匿名样例/私有辅助声明都有具名输出；8 个 examples 与私有辅助的独立输出尚未提交。旧 `5b13173e` 的历史脚本来源时间差不再列作当前入口缺失
  - 已收到的新增公理覆盖：`block_edge_count`、`block_adjacent_meet`、`block_interior_disjoint`、`block_cover`、`tiling_exists_iff`、`qualified_is_mother`、0/1 的裸母体/非合格母体四声明、`provenance_complete` / `provenance_witness`；Distribution 的 `chainIso_preserves_crk`、`mem_cone_iff`、`path_sieve_identity`、`birthCount_eq_primeCounting`、`birth_support_eq_primes`
  - 验收：相同当前 SHA 的完整 build、全部样例与依赖审计共同通过，审计入口实际执行且日志可访问；拒绝 `sorryAx` / 偷渡结论的自定义公理。源码 grep 不代替内核检查

## P1：补齐论文的一元语义与可维护性

- [ ] **P1.1 补完无标签源的序同构、唯一性与传输**
  - 路径：`lean/Definitions/Def_PrimeMother_Source.lean:27–122`、`lean/Theorems/Thm_PrimeMother_Distribution.lean:25–37`；论文 “Atomic successor source / Clock reconstruction / Relabelling invariance”
  - [x] `63875fea` 已添加规范归纳源 `Chain`、前缀关系 `ChainLE`、秩 `crk`、单调/严格单调、`chainOf`、`crk_chainOf`、`crk_injective`、`clock_iso` / `clock_surjective` 的无直接占位脚本，并标明 Nat 部分是秩模型
  - [x] `67b8f50f` 新增 `IsChainIso`（保根/后继的 Chain 自映射）及 `chainIso_preserves_crk` 脚本。这类规范 Chain 自映射事实上被构造子条件确定，不应把未单列 bijectivity 当作独立错误；但声明范围仍非一般源间同构传输
  - `clock_iso` L93–94 仍只断言 `crk` 双射。补 `ChainLE a b ↔ crk a ≤ crk b`、相应序结构和正式 order isomorphism，明确保根/后继相容性
  - 补任意满足保根/后继条件的候选 `f : Chain → Nat` 的唯一性（如 `f = crk`）；同秩前缀唯一、或 Chain 自映射保持秩，不等于该桥接声明已经提交
  - 明确规范 Chain 与论文一般 rooted directed source 的建模关系；若声称覆盖一般源，给出其结构/假设及与 Chain 的等价。Atlas/birth/ledger 仍只在 Nat 上定义；补源层对象、秩模型正式对应，以及重标记保持 atlas/provenance/mother/birth 的准确声明
  - 验收：源→Nat 序同构、候选映射唯一性与所宣称传输分别有准确声明并经当前内核检查；注释与 README 不超出已实现范围

- [ ] **P1.2 补全路径 atlas 与完整 chronological provenance**
  - 路径：`lean/Definitions/Def_PrimeMother_Atlas.lean:61–123,174–245`；论文 `lem:atlas-rank`、Regular atlas、Birth ledger、Stage provenance（论文 L161–237）
  - [x] 秩模型分块脚本已提交：`AtlasTiling` L61、`blockLo` / `blockHi` L67/70、`block_edge_count` L73、`block_adjacent_meet` L79、`block_interior_disjoint` L84、`block_cover` L91、`tiling_exists_iff` L117。规范数值切点、正块长条件下覆盖等不再是“全部未实现”
  - 剩余路径语义：AtlasTiling 仅存块数/下界/乘法等式；补实际有限段、端点/边/有序路径同构见证及其与数值模型的等价。区间端点等式和同边数不自动构成已经写出的路径同构声明；半开边区间覆盖也须与闭顶点路径的共同端点表述对齐
  - 剩余唯一性：`tiling_exists_iff` 只是存在式重包装。补正块长或合格母体域内的块数/切点/atlas 唯一性。裸 `AtlasTiling 0 0` 可分别取 r=2、r=3，不能无条件声称整个扩展模型唯一；这不反驳论文预期非空前缀范围
  - [x] `QualifiedMother` L176 明列 `Pi < H`、`birth Pi=true` 与 atlas；`qualified_is_mother` 和 `mother_zero_zero` / `not_qualified_zero` / `mother_one_two` / `not_qualified_one` 明确裸关系与资格层，并覆盖 0/1 边界。原 birth 仍只查询严格更早 birth
  - [x] `BirthLedger` L205、`BirthProvenance` L210、`provenance_complete` L217、`provenance_witness` L243 已有无直接占位脚本：H≥2 时给出 born/all-fail 或 blocked/一个合格母体，给定合格母体可得到 tiling 非空
  - 剩余完整记录：论文 provenance 保存当前前缀、有序早期 birth ledger 及**每个成员**的 atlas 结果族。当前 ledger 是 Set，provenance 是两分支 Prop，blocked 分支仅保留一个母体；补完整有限族及其与递归规则的对应。`provenance_witness` 当前输入是 QualifiedMother，未直接表达从整份 retained record 中提取对应结果
  - 验收：所有合格先前母体的结果可从记录取出；born 证书证明全部失败，blocked 给出实际路径继承见证；适用域内唯一性、源层重标记保持记录和 P0 当前 build/公理输出共同通过

- [ ] **P1.3 验证已提交的一元结果并补测度/实数版本**
  - 路径：`lean/Theorems/Thm_PrimeMother_Distribution.lean:25–129`；论文 Relabelling invariance / Path-sieve identity / Exact distribution identity
  - [x] `MotherCone` L43 与 `mem_cone_iff` L46 已给母锥的后续 r 倍（r≥2）秩刻画；`path_sieve_identity` L57 已给 n≥2 时较早 birth 母锥覆盖等价于非素数。MotherCone 本身是裸 atlas 关系，不预设 Pi 为素数；对 primitive/birth 前缀须结合主定理取得 Pi≥2/素数范围
  - [x] `birthCount` L97 按 `Finset.range (x+1)` 过滤 `2≤m ∧ birth m=true` 定义；`birthCount_eq_primeCounting` L103 的 Nat 截断计数脚本及 `birth_support_eq_primes` L121 的 Nat 出生集合等式已提交。它们通过主定理识别素数，未把最终结论放进 birth 定义
  - [x] 旧 34 项收据报告相同未改 5 模块的完整构建，L51–55 列出本模块五个 theorem 的标准公理输出；审计入口已保存并逐项核对
  - 剩余当前验证：依 P0 补完整原始日志并独立重现，检查 x=0/1 和含上端点的计数边界；旧 94 项入口/源码来源仍已核实，当前 98 项执行来源待核；不把本模块的对应收据/五项历史输出改写为缺失
  - 剩余论文范围：实现出生测度（Dirac 和）、测度相等及相应支持集声明；当前 `birth_support_eq_primes` 只是 Nat 的 Set 等式，不是已定义测度的 support。补实数 x≥2 的截断/取整桥接与计数恒等式；源码已明确仅声称 Nat 版本，不将该未实现范围当作隐藏假设
  - 重标记剩余范围依 P1.1/P1.2：`chainIso_preserves_crk` 仅证明规范 Chain 秩保持，未正式传输 provenance、mother、birth
  - 验收：每个声称完成的论文结论有准确 Lean 声明与当次内核证据；区分 Nat/实数、集合/测度和规范模型/一般源。支持集/计数恒等式不等于新的素数间隔估计

- [ ] **P1.4 补齐 README 验证依据与 CI**
  - 路径：`README.md:13–50`、根 `.gitignore:1`；建议 `.github/workflows/lean.yml`
  - [x] `300036da` 新增 README，列出固定版本、默认构建、主定理与 finite-return / boundary 未实现范围
  - [x] 历史 7/17 项、旧 5 模块 3016-job/34 项文本、可解析 68 项摘要及 90 项 clean working tree/8 项输出均保留；旧 82 项失联目标仍为历史缺陷。上轮 `dfbe1671e5d66e24afff7c1f48737dc7906bd9dc` 的实际可解析目标 `fbc8fb7ec89ccd20b5da86ba9e4e9f1315eabc37`、3019-job/94 项 clean 报告和 4 项输出继续保留正确源码/入口对应。当前 `3526d4e1` 的 98 项摘要/4 项输出已收到，但 c0f8ab25… 目标不可解析；来源、checkout、完整输出/日志及独立重现按 P0 补齐
  - 剩余文档：README 链接收据、完整日志和审计入口，说明报告来源与适用 SHA；不要把 L50 “P0 complete” 或 L39 “Verified” 扩张为独立重现或论文全范围已完成。更新 L13–17 模块/ledger 覆盖、L23–25 源层范围，并加入 Distribution 的 Nat 限定、P2.1 词/packet/单返回及多块合法词构造的部分进展，以及未实现测度/一般源/历史双射/一般素数族范围
  - CI 仍未提交；根 `.gitignore` 仍忽略 `.github/`，添加 workflow 时须确保实际入库。本审计不修改 ignore、CI 或仓库设置
  - CI 覆盖 push/PR、固定工具链、完整 `lake build`、8 模块/样例/98 项公理入口以及占位/依赖门禁；不能仅 grep 无 sorry 就声称证明可信
  - 验收：当前新源码有可访问成功 run，失败/缺失/未运行分别记录；README 清楚区分已实现且检查、实现待检查和未实现

## P2：论文最终结论的缺失实现，按依赖顺序推进

P2.1 已有词/packet/单返回、多块合法词、单步 elementary-return、append 保持、最终词逐块记录与有序支持长度、递增且每项 ≥2 时的记录类严格递增、p≥2 的 singleton 完整 packet/次数几何、[2,2] 词等式及 [2,3] 具体完整 packet 几何回归；一般族和语义工作仍开放。P2.2–P2.5 仍为未实现的建议模块/目标，不能当作现有成果。

- [ ] **P2.1 有限 return source 与实际 packet 几何**
  - 现有路径：`lean/Definitions/Def_PrimeMother_ReturnWord.lean:21–105`、`lean/Definitions/Def_PrimeMother_ReturnPacket.lean:26–168`、`lean/Theorems/Thm_PrimeMother_ReturnCombination.lean:17–1134`；历史源桥接仍建议 `Def_PrimeMother_ReturnSource.lean`
  - 对应论文：`prop:return-normal-form` L1142–1174、simple-return sector L1220–1226、`thm:return-combination` L1238–1307
  - [x] 词层源码：`IsReturnWord` L54、`listMax` 与 9 个基础 theorem 已提交；new/old label 扩张条件不依赖素数列表。剩余：有限顶点等价关系、不合并相邻点、无标签同构、first-occurrence 规范化和逆构造，证明双向对应/唯一性；不能用词谓词本身代替历史双射
  - [x] Packet 基础源码：`occurrences`、`IsRecurrent`、`IsElementaryReturn`、`ReturnPacket`、`ReturnsOverlap`、`PacketAdjacent` 与 4 个 theorem 已提交。剩余：在合法词和完整 packet 顶点域上构造图、证明 elementary-return 端点唯一及 packet 对应、共享原子边等价与连通性；`simpleReturn_packet_card` 只展开次数定义，不建立端点对应
  - [x] Sector 条件桥接源码：`ade6c9ee` 将 `IsSimpleReturn` L39–40 明确为次数部分；新增 `returnSupport`、`SupportIso`、`IsSimpleReturnSector` 和 3 个 theorem。`sector_of_distinct_support_lengths` L156–168 给“次数条件 + 不同类支持长度互异 ⇒ 当前 sector”。[2,3] 已有次数/分类及边数互异；既有 singleton 已排除不同返回类，可据此建立其 vacuous sector 条件。两者均尚无显式 sector theorem，一般 packetWord 前提未证，cut-open 模型与执行验收仍待补
  - **继续对齐 cut-open 语义**：论文 L994–997 的 `N(J):=J` 不保留 quotient 标签相等模式；L1220–1224 的路径非同构等价于 ranks 互异。当前 `SupportIso` L131–132 比较 raw 模式，导致 sector 过宽。w=[0,1,2,3,1,0,4,2] 满足合法词、次数条件和当前 sector，却有支持边数 5、3、5；详见 ade6c9ee 历史记录。须定义实际 cut-open 有序路径及其同构/秩对应，或在明确 rank-model 范围下用支持边数准确刻画，再证明正反等价；仅保留现有充分条件不足以推出反向 distinct-prime 分类
  - 修正 `returnSupport` L110–114 的“raw slice 自动首次出现规范化”注释；若保留 raw-pattern 关系用于历史等价，应与 unary cut-open 路径同构分开。只对子词重编号不能消除上述 5、3、5 对照。所有语义谓词均应在合法历史/词的明确适用域使用，且与随后推出素数性的 theorem 分开
  - [x] 旧单返回构造源码：`spine`、`singlePrimeWord` 及 11 个 theorem 已提交；`singlePrimeWord_elementary (p) (hp : 2 ≤ p)` 得到端点 1、p+1 和无中间同类，支持长度 p。这个长 p+2 的旧构造仍缺完整 packet/count-only simple-return 的显式 theorem；既有 singleton 结果针对不同的长 p+1 的 `packetWord [p]`，见下。两个构造均还需 return birth/empty-atlas-ledger 判据及 unary 桥接，p≥2 本身允许合数
  - [x] 多块合法词源码：`4cd15d0d691432f45b80f8add8b990d4ab5db536` 新增 `packetWordAux` / `packetWord` / `PacketInv` 和上述 6 个 theorem；`isReturnWord_packetWord` 在每项 ≥2 下成立，不需素性/互异。这里只记录源码实现，未验收编译；不能据其注释勾选论文 (ii)
  - [x] 单步几何源码：`3d0c1e9b` 已给 `PacketInv` L192–195 增加 `w[b - 1]? = some lprev` 并维护它；`packetStep_elementary` L348–391 给出单步词上标签 lprev、端点 b−1/b−1+p、支持边数 p 和无中间同类。此位置缺口已补，不再列作完全缺失；当前构建/内核对应仍待 P0 验收
  - [x] 通用 append 保持源码：`fd00c30c` 的 `elementaryReturn_append_preserved` L423–441 已证明任意尾部追加保留旧 elementary return 的 c/a/b 及中间无同类。`packetWord_singleton` / `packetWord_singleton_length` L444–455 和 `packetWord_two_two` L460–462 也已提交；上轮已补完 singleton 次数/完整 packet，见下；append 引理本身不保持全词次数
  - [x] [2,3] 具体完整 packet：`f0ae0fa7` 的 L477–573 已给词 [0,1,0,2,1]、端点 (0,2)/(1,4)、类 0/1 恰两次、packet={0,1}、count-only simple-return 及全部 elementary returns 分类。L578–596 又给指定两类边数互异与 `PacketAdjacent … 0 1`。剩余是显式 sector/正式图对象与 P₂ 同构及 birth；不能将具体案例扩大为一般族
  - [x] singleton 完整 packet 源码：`23b93b81` L611–834 在 p≥2 下给所有位置分类、非零类至多一次、零类精确出现 {0,p}、端点 (0,p) 的 elementary return、`ReturnPacket (packetWord [p]) = {0}` 和 count-only simple-return。这里已排除三次及以上的隐藏类，完整 packet/次数不再缺失；尚无显式全 elementary-return iff 分类、singleton sector/图/连通性或 birth theorem，已有次数事实可作桥接。新 8 项输出来自可解析同一源码收据，独立内核执行仍待 P0
  - [x] 最终词逐块记录源码：`fbc8fb7ec89ccd20b5da86ba9e4e9f1315eabc37` L855–969 已给 blockRecordsAux、任意 builder 的后缀分解、每项 ≥2 时全部记录在最终词上的 elementary return，以及 `map (b−a) records = ps` 的有序长度等式。不再把递归记录/最终词保留列为缺失；此处“全部”只量化记录，不是最终词所有 returns 的 iff 分类
  - [x] 记录类互异源码：`8d2a7c65` L989–1125 给 aux 下界/有序及公开 `packetWord_classes_sorted`；公开版只需 SortedLT 与每项 ≥2，不需素性。L1129–1134 的支持有序只需 SortedLT。这关闭相应域内的记录类互异，未给全词次数/完整 packet 或 sector；新 4 项输出收据的目标来源待 P0 核实
  - 下一步从已有类互异与逐记录端点标签落实不同记录的端点位置互异（不要求支持区间不相交）的显式桥接，并证明恰两次出现、无额外返回/两次类和完整 packet，再给 simple-return 与路径交叠图。仍须使用准确条件：[3,2,5] 虽互异但类 0 出现三次，[2,2,2] 也重复类；每项 ≥2 的逐记录结果和 append 保持均不保证全词次数。不得把已完成的记录类互异或逐记录最终词接入重新列为缺失；剩余是全词分类及对正确 sector/图/birth 的桥接
  - 在已提交 packetWord 基础上，证明任意**非空**有限互异素数集经递增排列后的精确 packet、支持秩集合等于输入集及交叠图为路径图；引入 return birth/ledger 并连接 unary theorem，同时完成 born packet 反向分类。singleton 完整 packet/次数与 [2,3] 具体 packet/端点分类已提交，但一般族、正确 sector 及 birth 尚未完成。论文定理 (ii) 写“every finite set”时应显式补非空前提以匹配总述
  - 验收：词/历史双射、完整 cut-open simple-return 条件与秩互异等价、singleton birth 与一般族正向/反向分类分别有准确 Lean 定理；empty/singleton/重复支持长度/合数对照明确，predicate 不以待证素数集合直接作定义；依 P0 在同一精确 SHA 完成新 3 模块的 64 项及全库 98 项公理验证

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

