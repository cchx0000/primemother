# PrimeMother TODO：Lean 状态与完成路线

审计日期：2026-10-10 08:32（UTC）  
已审计提交游标：`master` @ [ade6c9ee16f4ec671077b9f22c42f0738b76e56b](https://github.com/cchx0000/primemother/commit/ade6c9ee16f4ec671077b9f22c42f0738b76e56b)  
当前 Lean 源码基线：[ade6c9ee16f4ec671077b9f22c42f0738b76e56b](https://github.com/cchx0000/primemother/commit/ade6c9ee16f4ec671077b9f22c42f0738b76e56b)（ReturnPacket 新增 sector 谓词与 distinct-length 充分条件；共 8 个库模块、67 个公开 theorem。AxiomAudit 已覆盖 65 项输入，仍漏 2 项；已提交执行收据仍只覆盖旧 34 项）  
首次完整源码与论文审计：[258fb757f4712b18ce45310bbebbd34e9dc9226d](https://github.com/cchx0000/primemother/commit/258fb757f4712b18ce45310bbebbd34e9dc9226d)

<!-- primemother-audit-cursor: ade6c9ee16f4ec671077b9f22c42f0738b76e56b -->

## 当前结论与验证边界

当前仓库已有一元 prime-birth 秩模型、8 个回归样例、部分无标签源层、秩区间 tiling/provenance 和 Nat 分布结果，以及 return-word、packet、单返回与多块合法词构造。**本轮新增 `IsSimpleReturnSector`、支持长度桥接与扩展公理审计输入，但 raw equality-pattern 同构尚未对齐论文 cut-open 路径的同构；不能把“补了 sector 谓词”记作完整语义已验收。** 无标签历史双射、packetWord 精确几何/sector 实例、packet birth 和任意非空互异素数族的正反分类仍未完成。本轮仅审计源码与已提交证据，未运行 Lean/Lake，不以“0 sorry”代替编译成功。

- 从上次游标 `4cd15d0d691432f45b80f8add8b990d4ab5db536` 继续，核对 `728d2a1a70972c891c4a57e4cb133d79b5b032e6` 仅同步本 TODO 并跳过自触发；随后逐个审计唯一新代码提交 `ade6c9ee16f4ec671077b9f22c42f0738b76e56b`。父链连续，本提交只改 ReturnPacket（+75/−2）与 AxiomAudit（+37）；审计前 TODO blob 为 `c7576e52364450e9826c2328416e5199ec4bd924`
- ReturnWord 的 `IsReturnWord` 仍从 [0] 按“不同于末项、至多 max+1”扩张，9 个 theorem 涵盖 max、非空、首项与标签界。它尚未定义有限历史/顶点等价关系/无标签同构及双向规范化；Packet 文件仍未实现该历史双射
- ReturnPacket 将 `IsSimpleReturn` L39–40 明确限定为次数部分；新增 `returnSupport` L115–116、`SupportIso` L131–132、`IsSimpleReturnSector` L146–149 及 3 个 theorem。`sector_of_distinct_support_lengths` L156–168 以次数条件和不同类的支持长度互异为前提，推出当前 sector 谓词；这是有效的充分条件脚本结构，未证明 packetWord 满足这些前提，也未推出素数性、birth 或反向分类
- **语义差距仍在**：论文 L994–997 的 unary normalization 是 cut-open ordered path `N(J):=J`，L1220–1224 要求这些路径两两非同构并明确其等价于 return ranks 互异。当前 `SupportIso` 还要求原始子词的全部标签相等模式一致，这比仅有序原子路径同构更强；其否定使当前 sector 比论文条件更宽。合法词 [0,1,2,3,1,0,4,2] 的三个 elementary returns 为 [0,5]、[1,4]、[2,7]，边数 5、3、5；次数均为 2，三个 raw patterns 两两非同构，故满足当前谓词却有重复 rank 5。详见本轮增量记录；这是有限静态模型检查，非 Lean 回归结果
- 独立的注释问题：`returnSupport` L110–114 声称全词已 first-occurrence-normalized，所以任意 raw slice 也已规范化；例如合法词 [0,1,0,2,1] 的 [1,4] 子词是 [1,0,2,1]，重新按首次出现编号才是 [0,1,2,0]。标签重命名不改变 `SupportIso` 的相等模式，因此这条注释错误本身不否定长度桥接；论文 cut-open 语义差距也不能只靠对子词重新编号解决
- ReturnCombination 未变：单返回构造的 `singlePrimeWord_elementary` 仅需 p≥2，支持边数 p，允许合数；多块 `isReturnWord_packetWord` L326–347 仅需列表每项 ≥2，空列表输出 [0]。`PacketInv` 仍缺前一位置的标签对应和每项端点/次数/完整 packet 数据，尚无合法互异素数列表的完整 sector、精确支持秩、路径交叠图或 born 分类
- 当前 8 个库模块经去注释源码扫描，直接 `sorry` / `admit` / `axiom` 声明均为 **0**；公开 theorem 为旧 34 + ReturnWord 9 + ReturnPacket 7 + ReturnCombination 17 = **67**（64 + 本轮 3），匿名 examples 仍为 8。旧 `birth` 严格先前阶段递归、0/1 边界、`birth_iff_prime` 目标/脚本及所有旧模块/依赖均未改变；新定义未把素数判定或最终结论作为输入。源码扫描不证明传递依赖无 `sorryAx`
- 已提交 [3016-job 收据](https://github.com/cchx0000/primemother/blob/ade6c9ee16f4ec671077b9f22c42f0738b76e56b/docs/receipts/build-5b13173eecd3863ed99fb0633d18499521a843c7.md) 仍仅覆盖未变化的旧 5 模块和 34 项公开 theorem；版本、clean、warning 和退出 0 是维护者报告。[当前 AxiomAudit](https://github.com/cchx0000/primemother/blob/ade6c9ee16f4ec671077b9f22c42f0738b76e56b/lean/AxiomAudit.lean) 已新增 3 个 return 模块导入、通过导入闭包覆盖全部 8 模块，并新增 31 个具名命令，总计 **65 个输入命令**；仍漏 `listMax_nil`、`listMax_cons`，没有当前 33 项新增 theorem 的执行输出。文件头“all 5”、Packet 小标题“(6)”也未同步。输入覆盖改善不能当作已执行收据
- 固定 Lean `v4.33.1`、mathlib `0df444a360eaa60ab8c11dca51a86af692955474`、Lake 配置未改。默认 Theorems glob 在配置上包含 ReturnCombination → ReturnPacket → ReturnWord；根 `AxiomAudit.lean` 仍须单独运行。本轮没有编译成功或失败的实测记录
- 新代码 SHA `ade6c9ee16f4ec671077b9f22c42f0738b76e56b` 的 Actions runs 0、check-runs 0、commit statuses/comments 空；全树无新收据/CI workflow，根 `.gitignore` 仍为 `.github/`。提交标题“audit covers 65 thms; 0 sorry”只对应输入数量/源码状态，不证明当前 8 模块/67 项验收。旧收据目标与审计入口首次入库 SHA 的对应问题保留
- 一元 P1 的正式序同构/一般源传输、实际路径 atlas/完整 chronological provenance、实数/测度版本仍未补完。P2.1 继续为“部分源码已提交，语义/分类/内核验收未完成”；P2.2–P2.5 未实现范围不变。README/论文未改，README 的模块、finite-return 范围和验证文字需同步；本审计仅改 `todo.md`

以下当前源码行号以 `ade6c9ee16f4ec671077b9f22c42f0738b76e56b` 为准；旧 5 模块仍与 `67b8f50f92b5f755c708f7cfd79fbaddaf3d664b` 一致。历史增量记录保留当时证据状态，后续收据和实现不改写历史事实。

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

后续审计从上述提交游标之后按提交顺序处理；本审计器自身仅修改 `todo.md` 的提交不触发重复写入。若出现历史分叉、缺失提交或并发修改，先重新比较 HEAD 和最新文件，不覆盖他人变更。

## P0：先让当前一元模型成为可复现、无占位的内核检查结果

- [ ] **P0.1 建立当前完整构建基线**
  - 路径：`lean/lean-toolchain`、`lean/lakefile.lean`、`lean/lake-manifest.json`；当前 8 个库模块为原 Source、Atlas、PrimeBirth、Regression、Distribution，加 ReturnWord、ReturnPacket、ReturnCombination。默认 Theorems glob 含 ReturnCombination → ReturnPacket → ReturnWord；旧 Distribution → PrimeBirth → Atlas → Source 链未改
  - [x] 已收到旧 5 模块精确 SHA 的构建摘要：`docs/receipts/build-5b13173eecd3863ed99fb0633d18499521a843c7.md:3–14` 报告 `cd lean && lake build`、退出 0、3016 jobs / 0 errors 和 5 模块覆盖。`5b13173e` 与当前保留的旧 5 模块/依赖相同，但不含新增 3 模块；旧 614-job 收据作为历史证据保留
  - [x] 新收据已补 Lean/Lake 版本文字、0 warnings 与 clean working tree 报告。它们是维护者已提交的证据文本，不是本审计器独立运行所得；不再将这些字段列为完全缺失
  - 剩余：当前精确 SHA 的完整 8 模块构建、原始日志和各模块/样例实际执行记录。没有可访问 CI run；旧 5 模块摘要不等同新增 ReturnWord/ReturnPacket/ReturnCombination 已编译，`4cd15d0d691432f45b80f8add8b990d4ab5db536` 的提交信息也不能替代其声称的 3019-job 构建收据
  - [x] 当前 Atlas/Distribution 已有对应源码的构建/公理报告；`lean/AxiomAudit.lean` 与完整调用也已保存。入口仅在 `40fb96b3` 首次入库且不在默认 target/glob 内；补明确脚本来源的执行记录，或在包含入口的精确 SHA 上另跑 `cd lean && lake env lean AxiomAudit.lean`
  - 在固定工具链干净 checkout 上运行 `cd lean && lake build` 及 `lake build Definitions Theorems`，覆盖全部 8 模块。另检查 ReturnWord 单模块及新导入链，不凭有无显式 import 推断编译成败。必要时先取固定依赖及 mathlib cache；记录精确 SHA、Lean/Lake 版本、checkout 状态、命令、退出码、warning 和原始日志
  - 验收：当前同一精确源码提交的完整默认构建退出 0，8 个库模块和扩展后的审计入口实际包含；说明所有 warning。缓存、单模块或文字 “Verified” 不替代该收据，不通过移除默认 target 凑通过

- [ ] **P0.2 验证已补完的良基递归展开与基础出生规则**
  - 路径：`lean/Definitions/Def_PrimeMother_Atlas.lean:129–172`；声明 `birth`、`birth_E` L139、`birth_root` L144、`birth_succ_succ` L153
  - [x] 源码修复：`36add88e` 已消除最后直接占位。既有 P1.2 扩展及本轮 P2.1 新增均未改变 birth 定义、这三个引理的目标/脚本或严格先前阶段依赖
  - [x] 当前源码收据 L33–35 给出这三个引理的具名公理文本，均列 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx`，并报告构建/审计退出 0；入口已保存
  - 剩余：P0.1 的完整原始执行日志、脚本/目标 SHA 对应与独立重现；复核 `WellFounded.fix_eq` 展开、`show` / `congr 1` / `propext`、见证重组和 0/1 边界。不再把已收到的当前源码报告写成缺失
  - 验收：固定工具链上的当前三个引理编译成功，完整传递公理输出无 `sorryAx`；定义没有素数判定或最终结论型输入。收到当前源码报告与独立重现须区分

- [ ] **P0.3 验证已提交的主定理证明链**
  - 路径：`lean/Theorems/Thm_PrimeMother_PrimeBirth.lean:19–115`；声明 `birth_ge_two` L21、`birth_iff_no_earlier_mother` L36、`birth_iff_prime` L58
  - 当前状态：主定理自 `3e9d7d3` 已无直接占位；`36add88e` 补齐其展开依赖。本轮 PrimeBirth 及其 Atlas/Source 依赖均未改，原目标、递归与模型假设保留
  - [x] 当前源码收据 L48–50 给出 `birth_ge_two`、`birth_iff_no_earlier_mother`、`birth_iff_prime` 输出，均只有三项标准公理；对应当前 Atlas/Distribution 所在的相同源码/依赖，审计入口已保存
  - 剩余：P0.1 完整原始日志、已保存入口与目标 SHA 的对应及独立重现。检查 L21–32 的 0/1 边界；L36–55 的展开/if 两分支；L71–82 的非平凡素因子和严格范围；L85–104 的归纳、商非 0/1 与 atlas 见证；L107–115 的素数定义方向
  - API 依据：[固定版本 Basic.lean L68–77](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Nat/Prime/Basic.lean#L68-L77)、[Defs.lean L107–120](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Nat/Prime/Defs.lean#L107-L120)、[Defs.lean L407–408](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Nat/Prime/Defs.lean#L407-L408)
  - 验收：原始目标 `∀ n, 2 ≤ n → (birth n = true ↔ Nat.Prime n)` 不削弱、不添加结论型假设；当前完整文件编译且整个证明链不依赖占位

- [ ] **P0.4 执行回归测试并扩展当前内核依赖收据**
  - 路径：`lean/Theorems/Thm_PrimeMother_Regression.lean:14–107`、当前 8 个库模块、已提交 `lean/AxiomAudit.lean`；仍需完整执行日志
  - [x] `9473ec06` 的 0、1、2、3、4、6、9、25 共 8 个证明式 examples 保留，仍在默认 glob 范围内。`birth` 为 noncomputable，样例是等式证明；25 借用主定理在 5 上的实例，不是主定理独立正确性证据
  - [x] 既有收据 L22–55 给出旧 5 模块全部 34 个公开 theorem 的具名公理文本，审计入口的 34 个命令与该范围逐项匹配；12 个 Atlas theorem 与 5 个 Distribution theorem 均已覆盖。各项是标准公理子集或无公理；此完成子项仅指收到文本并核对覆盖，不等于实际重跑
  - [x] 旧 5 模块完整审计输入与调用已提交，包含 Regression 导入；维护者报告该范围审计退出 0。默认 build 不包含此根入口，必须单独调用
  - [x] `ade6c9ee` 已把 3 个 return 模块纳入审计导入闭包，并新增 31 个具名打印命令；当前共有 65 个输入命令。此子项仅验收输入文件已扩展，不声称已经执行或全覆盖
  - 当前缺口：67 个公开 theorem 中仍漏 `listMax_nil`、`listMax_cons` 的具名命令；补至 67 项，并修正入口文件头“all 5”和 ReturnPacket 小标题“(6)”的过期数量。ReturnWord 9、ReturnPacket 7、ReturnCombination 17 共 33 项均缺当前精确 SHA 的已提交执行输出；不能用输入命令数量替代输出收据
  - 回归目标：保留 [0,1,0,1] 的次数条件/重复长度对照、p=2/p=4 的单返回词及 packetWord 的 []、[2]、[4]、[2,3,5]、[2,2]、[2,2,2]；加入 [0,1,2,3,1,0,4,2] 的当前 sector/重复 rank 对照，以及 [0,1,0,2,1] 的 raw slice/首次编号对照。分别检查合法词、cut-open 路径语义与完整 simple-return/packet 结论；这些仍是尚未执行的 Lean 验收目标
  - 剩余：明确 `5b13173e` 收据目标使用的审计脚本来源，保存完整执行日志和每个模块/样例检查记录，或在含入口的精确 SHA 重现。34 项不能扩张成所有匿名样例/私有辅助声明都有具名输出；8 个 examples 与私有辅助的独立输出尚未提交
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
  - [x] 当前源码收据报告完整 5 模块构建，L51–55 列出本模块五个 theorem 的标准公理输出；审计入口已保存并逐项核对
  - 剩余当前验证：依 P0 补完整原始日志/精确脚本来源并独立重现，检查 x=0/1 和含上端点的计数边界；不再将本模块的对应收据/五项输出列为缺失
  - 剩余论文范围：实现出生测度（Dirac 和）、测度相等及相应支持集声明；当前 `birth_support_eq_primes` 只是 Nat 的 Set 等式，不是已定义测度的 support。补实数 x≥2 的截断/取整桥接与计数恒等式；源码已明确仅声称 Nat 版本，不将该未实现范围当作隐藏假设
  - 重标记剩余范围依 P1.1/P1.2：`chainIso_preserves_crk` 仅证明规范 Chain 秩保持，未正式传输 provenance、mother、birth
  - 验收：每个声称完成的论文结论有准确 Lean 声明与当次内核证据；区分 Nat/实数、集合/测度和规范模型/一般源。支持集/计数恒等式不等于新的素数间隔估计

- [ ] **P1.4 补齐 README 验证依据与 CI**
  - 路径：`README.md:13–50`、根 `.gitignore:1`；建议 `.github/workflows/lean.yml`
  - [x] `300036da` 新增 README，列出固定版本、默认构建、主定理与 finite-return / boundary 未实现范围
  - [x] 历史 7/17 项收据保留；`40fb96b3` 新增旧 5 模块的 3016-job 摘要、34 项公理输出及已保存入口/调用。版本、clean、warning 和模块覆盖均有维护者报告
  - 剩余文档：README 链接收据、完整日志和审计入口，说明报告来源与适用 SHA；不要把 L50 “P0 complete” 或 L39 “Verified” 扩张为独立重现或论文全范围已完成。更新 L13–17 模块/ledger 覆盖、L23–25 源层范围，并加入 Distribution 的 Nat 限定、P2.1 词/packet/单返回及多块合法词构造的部分进展，以及未实现测度/一般源/历史双射/一般素数族范围
  - CI 仍未提交；根 `.gitignore` 仍忽略 `.github/`，添加 workflow 时须确保实际入库。本审计不修改 ignore、CI 或仓库设置
  - CI 覆盖 push/PR、固定工具链、完整 `lake build`、8 模块/样例/67 项公理入口以及占位/依赖门禁；不能仅 grep 无 sorry 就声称证明可信
  - 验收：当前新源码有可访问成功 run，失败/缺失/未运行分别记录；README 清楚区分已实现且检查、实现待检查和未实现

## P2：论文最终结论的缺失实现，按依赖顺序推进

P2.1 已有下列词/packet/单返回、多块合法词构造及 sector 条件桥接的部分源码；P2.2–P2.5 仍为未实现的建议模块/目标，不能当作现有成果。

- [ ] **P2.1 有限 return source 与实际 packet 几何**
  - 现有路径：`lean/Definitions/Def_PrimeMother_ReturnWord.lean:21–105`、`lean/Definitions/Def_PrimeMother_ReturnPacket.lean:26–168`、`lean/Theorems/Thm_PrimeMother_ReturnCombination.lean:17–347`；历史源桥接仍建议 `Def_PrimeMother_ReturnSource.lean`
  - 对应论文：`prop:return-normal-form` L1142–1174、simple-return sector L1220–1226、`thm:return-combination` L1238–1307
  - [x] 词层源码：`IsReturnWord` L54、`listMax` 与 9 个基础 theorem 已提交；new/old label 扩张条件不依赖素数列表。剩余：有限顶点等价关系、不合并相邻点、无标签同构、first-occurrence 规范化和逆构造，证明双向对应/唯一性；不能用词谓词本身代替历史双射
  - [x] Packet 基础源码：`occurrences`、`IsRecurrent`、`IsElementaryReturn`、`ReturnPacket`、`ReturnsOverlap`、`PacketAdjacent` 与 4 个 theorem 已提交。剩余：在合法词和完整 packet 顶点域上构造图、证明 elementary-return 端点唯一及 packet 对应、共享原子边等价与连通性；`simpleReturn_packet_card` 只展开次数定义，不建立端点对应
  - [x] Sector 条件桥接源码：`ade6c9ee` 将 `IsSimpleReturn` L39–40 明确为次数部分；新增 `returnSupport`、`SupportIso`、`IsSimpleReturnSector` 以及 3 个 theorem。`sector_of_distinct_support_lengths` L156–168 已写出“次数条件 + 不同类支持长度互异 ⇒ 当前 sector”的充分条件；未验收执行，也未证明 packetWord 的前提
  - **继续对齐 cut-open 语义**：论文 L994–997 的 `N(J):=J` 不保留 quotient 标签相等模式；L1220–1224 的路径非同构等价于 ranks 互异。当前 `SupportIso` L131–132 比较 raw 模式，导致 sector 过宽。w=[0,1,2,3,1,0,4,2] 满足合法词、次数条件和当前 sector，却有支持边数 5、3、5；详见本轮记录。须定义实际 cut-open 有序路径及其同构/秩对应，或在明确 rank-model 范围下用支持边数准确刻画，再证明正反等价；仅保留现有充分条件不足以推出反向 distinct-prime 分类
  - 修正 `returnSupport` L110–114 的“raw slice 自动首次出现规范化”注释；若保留 raw-pattern 关系用于历史等价，应与 unary cut-open 路径同构分开。只对子词重编号不能消除上述 5、3、5 对照。所有语义谓词均应在合法历史/词的明确适用域使用，且与随后推出素数性的 theorem 分开
  - [x] 单返回构造源码：`spine`、`singlePrimeWord` 及 11 个 theorem 已提交；`singlePrimeWord_elementary (p) (hp : 2 ≤ p)` 得到端点 1、p+1 和无中间同类，支持长度 p。剩余：证明整个词的 simple-return/完整 singleton packet；引入实际 return birth/empty-atlas-ledger 判据并用 unary theorem 推出素数情形的 born。现有 p≥2 构造允许合数，不等于 prime birth
  - [x] 多块合法词源码：`4cd15d0d691432f45b80f8add8b990d4ab5db536` 新增 `packetWordAux` / `packetWord` / `PacketInv` 和上述 6 个 theorem；`isReturnWord_packetWord` 在每项 ≥2 下成立，不需素性/互异。这里只记录源码实现，未验收编译；不能据其注释勾选论文 (ii)
  - 优先补构造的几何不变量：`PacketInv` L189–191 缺 `w[b - 1]? = some lprev`，`packetWordAux_invariant` L309–321 只存在量化最终状态，没有与输入列表对应的端点/支持长度/两次出现记录。分别证明位置、端点互异和完整 packet（包括没有额外返回），再证明 simple-return 与路径交叠图；[2,2]/[2,2,2] 回归区分重复长度和三次出现，不把 ≥2 当作互异素数前提
  - 在已提交 packetWord 基础上，证明任意**非空**有限互异素数集经递增排列后的精确 packet、支持秩集合等于输入集及交叠图为路径图；引入 return birth/ledger 并连接 unary theorem，同时完成 born packet 反向分类。当前多块构造仍只有合法词声明；新增 sector 桥接尚未用于它，仍无这些一般族分类或 packet birth 定理。论文定理 (ii) 写“every finite set”时应显式补非空前提以匹配总述
  - 验收：词/历史双射、完整 cut-open simple-return 条件与秩互异等价、singleton 与一般族正向/反向分类分别有准确 Lean 定理；empty/singleton/重复支持长度/合数对照明确，predicate 不以待证素数集合直接作定义；依 P0 在同一精确 SHA 完成新 3 模块及 33 项公理验证

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
