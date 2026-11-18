# 第 4 个发布的计划

**范围已定，收束后的工作计划在同目录的 `RELEASE_4_WORK_PLAN.md`；压缩之后从那里接着做，冲突时
以它为准。** 本文件保留经过、作者的原话和扫描结果的详表。作者最后的决定（2026-11-11 晚）：
「赞同一起修 S1-S5 / C 要做 / D 按你建议来」。

状态：**整理稿**，2026-11-11 晚（本地时间），会话压缩之前写下。没有评审过，没有动任何代码。
作者的决定只有两条（第 1 节）；其余都是待办和【提案】，不能当作基线。

标记：【已定】= 作者明确决定；【提案】= 我提的、未获批准；【实测】= 跑过；【读码】= 只读了源码。

源码路径相对于 Isabelle2026 的 `src/`。private tree 在 `7de251e`（第 3 个发布）。
相关文档（同目录）：主计划 `SLEDGEHAMMER_FACT_TRIGGER_PLAN.md`（现状在它的 13.8 节）；第 3 个
发布的维修方案 `RELEASE_3_REPAIR_PLAN.md`。

## 1. 起因和作者的决定

第 3 个发布之后，我在报告里把「`auto`、`fastforce`、`force` 拿到全局事实必然失败」列为已知
而不修的问题。作者此前没有意识到有这一项：它在第 3 版发布前提过多次，但都夹在长报告里，
作者当时明说「我没仔细看」，我却让这个决定靠「不回复就是不改」定了下来。

【已定，2026-11-11】作者的原话：
- 「这个问题必须被修复！容易修复吗？」
- 「整理一下我们要来发第四版了！」

即：这一项要修，并为此出第 4 版。

作者对出版本方式的要求（贯穿这一版）：
- 不要零碎地出版本。每个版本只带一点内容、隔几个小时又出一个，是不可接受的；第 2、3 版就是
  这样，还连累 `default_fact_qualifiers` 返工。
- 不要等发布以后才告诉作者有什么问题。
- 行为变化不能擅自做。
- 每一步照常请示，不是「一口气做到底」。

## 2. 必须修的：`auto`、`fastforce`、`force` 拿到全局事实

### 2.1 现象

Sledgehammer 除了外部 prover，还直接拿证明方法去试（tactic prover，
`HOL/Tools/Sledgehammer/sledgehammer_prover_tactic.ML` 的 `run_tactic_prover`）。它把这次尝试
选中的事实分成两类交给 Try0：局部事实放进 using 类，全局事实放进 direct 类【读码】。

Try0 怎样把 direct 类的事实写进证明文本，由每个方法的配置决定（`HOL/Tools/try0_util.ML` 的
`facts_config`，`allows_directs` 字段；各方法用哪个配置在 `HOL/Try0_HOL.thy`）【读码】：

| 配置 | 方法 | direct 类的事实 |
|---|---|---|
| `metis_attrs`（`allows_directs = true`） | `metis`、`meson` | 写在方法名后面：`by (metis foo)`，正确 |
| `full_attrs`（`allows_directs = true`） | `auto`、`fastforce`、`force` | 写在方法名后面：`auto foo`，**这三个方法不接受** |
| `clas_attrs`、`simp_attrs`、`no_attrs`（`false`） | `blast`、`fast`、`simp`、`argo`、`linarith` 等 | 归入用不上的类，走 `using foo by …`，正确 |

中间一行的结果：`Method.method_cmd` 报 `Bad arguments for method "auto"`，`run_tactic_prover`
把这个 `ERROR` 当作这次尝试放弃。【实测，2026-11-10，仅 `auto`】直接调用
`Try0_Util.apply_raw_named_method "auto"` 配 `full_attrs` 和一条 direct 事实，报的正是这个错。
`fastforce`、`force` 是【读码】，没有跑。

这是 Isabelle2026 原版的行为，本 feature 三个版本都没有碰它。它不产生错误的证明，只是这些
尝试白白失败。对本 feature 的后果：触发器生成的全局事实对这三个 prover 无效。

`full_attrs` 的使用者只有这三个方法和 AFP 的 Zippy
（`afp-2026-10-26/thys/Zippy/Zippy/Instances/Zip/Zip_Try0.thy`）【grep 实测】。

### 2.2 修法【提案】

把 `Try0_Util.full_attrs` 的 `allows_directs` 从 `true` 改为 `false`。只改这一个值，文件
`try0_util.ML` 本来就在被补丁之列，不动任何签名条目，`Try0_HOL.thy` 不动。改后这三个方法的
direct 类事实与 `blast`、`simp` 一样走 `using foo bar by auto`。

为什么是 `using`：Sledgehammer 自己在别处给这三个方法印的证明文本本来就是 `using … by auto`
（`sledgehammer_proof_methods.ML` 的 `partition_proof_method_facts` 把全部事实放进 using 那
一组，预演时用 `Method.insert_tac` 插入）【读码，来自第 3 版方案的第一轮评审】。

**容易吗**：代码是一行。工作量在别处，见 2.3、2.4 和第 4 节。

### 2.3 它是行为变化，范围要先实测

下面全部是【读码，来自第 3 版方案的评审】，**这一版动手前必须实测**，不能再照抄：

- 影响的是所有默认配置下的 Sledgehammer 调用，不只是用了触发器的。
- 默认调度下每个 tactic prover 的尝试：`auto` 是 0 条和 16 条事实两次，`fastforce` 是 0、16、
  32 三次，`force` 只有 0 条一次（`good_slices_of_tactic_prover` 配合默认调度表）。所以变的
  是 `auto` 的 16 条那次和 `fastforce` 的 16、32 条那两次，且只在该次尝试含全局事实时：从
  立刻放弃变成真的去跑，占满它的时间片，可能成功。`force` 只有用户设了 `max_facts` 才变。
- 成功之后还要做最小化，在同一个线程里把方法再跑多次（16 条事实时线性，最多再跑 16 次；
  32 条时二分）。tactic prover 的证明不做预演。
- 每次成功立刻计入 `max_proofs`（默认 4）。tactic prover 排在 ATP 和 SMT 之前，后面的尝试
  可能不再启动，用户看到的证明会变：`using … by auto` 多了，ATP 来的少了。
- MaSh 开着学习时，这些证明用到的事实进入持久状态，影响以后的事实选择。
- `try0` 命令的输出不变：它自己从不填 direct 类。
- Zippy 的 `zip` 在默认参数下只有 0 条事实的尝试，与 `force` 一样只在设了 `max_facts` 时变；
  它是否拒绝 direct 类事实没有测过。

要实测的最小集合（建议）：若干个目标上，改前改后各跑一次默认配置的 `sledgehammer`，记录
找到的证明、各 prover 的顺序和总耗时；专门挑 `auto`/`fastforce` 带事实能证、ATP 也能证的
目标，看 ATP 的证明是否被挤掉。

### 2.4 测试【提案】

- 确定性的：直接调用 Try0 的方法，`directs = [xref]`，对 `auto`、`fastforce`、`force` 各期望
  `SOME "using … by <方法>"`。改之前这个调用抛 `Bad arguments`；改成别的类会得到别的文本。
  注意 Try0 已注册的方法在注册时就取了 `full_attrs` 的值，所以这类测试只有在 private tree
  构建之后才反映修改；草稿环境里要直接调 `apply_raw_named_method` 并传改过的配置。
- 端到端：触发器给出一条全局的生成事实，`provers = auto`（以及 `fastforce`），目标只靠它能
  证，检查结果用到了这条事实。`force` 在默认调度下拿不到事实，要么设 `max_facts`，要么不测。

## 3. 这一版还要不要带别的：逐条请作者定

出第 4 版之前把所有已知的东西摆出来，作者逐条明确说要或不要。**不以沉默为默认。**

| # | 内容 | 现状 | 我的建议 |
|---|---|---|---|
| A | 没有名字的局部事实和 `this` 的名字：命题印出来包一层 cartouche（`cartouche_term`），末尾的 `simplify_spaces` 会压缩字符串常量里的空白，名字读回来是另一个命题。属于第 3 版那一类问题里唯一还留着的一处（维修方案 N4） | 没修。评审给过一个只改 `cartouche_term` 的局部修法，没有试过 | 先在草稿里试；干净就带上，免得将来为它再出一版 |
| B | Metis 的 `open_attrib` 对匿名事实拼错（N3） | 没修。没有有意义的输入能走到 | 不修 |
| C | 多条定理的事实加会改变上下文的属性，名字求值出不同的定理（N1） | 没修。Isar 没有能表达它的写法 | 不修，无法修 |
| D | `relevant_facts` 同时产出三份名单的分支没有测试（N2） | 两轮评审逐个模式对照过原版 | 不补（要依赖用户目录里的 MaSh 状态） |
| E | README 的「Other changes」没有提第 3 版的修正；第 4 版又有一处影响所有用户的行为变化 | 第 3 版时作者说不用改 | 第 4 版应当写明行为变化；文案要作者批 |
| F | 动手前再做一次全面扫描：Sledgehammer 与 Try0、Metis 之间还有没有「按构造必然失败」或「印出的文本读不回来」的地方 | 第 3 版扫过事实引用的文本这一类；tactic prover 的配置这一类没有系统扫过 | 做，结果并入本表再请作者定 |
| G | 主计划第 7 节里仍标着未核实的静态分析 | 四项已查明，其余没动 | 不属于这一版 |

主计划第 8 节的「已知且接受的后果」（`fact_filter = mash` 时触发器不运行等）是设计决定，
不在此列。

### 3.1 作者对上表的决定【已定，2026-11-11 晚】

作者的原话：「A 必须修 / B 修 / C 修 / D 这是一个 bug？ / E 修 / F 好，run an Opus agent 去做 /
G 现在就去核实！我真的他妈不想再出第五版了！！！」

- **A 必须修。**
- **B 修。**
- **C 修。** 我原先说无法修。可行的方向【提案，未评审】：让「名字」和「交给 prover 的定理」按
  构造一致。现在 `fact_of_ref` 是先把整条引用 `foo[attrs]` 求值成一串定理，再给每条起名
  `foo(j)[attrs]`；两者在属性会改变上下文时可能不同。改成：对每条定理的引用 `foo(j)[attrs]`
  单独求值，把求值得到的那条定理交给 prover。这样名字读回来必然就是 prover 用的那条，
  不再需要「两者碰巧相同」。代价：与用户写的 `foo[attrs]` 整体求值的结果在那种少见情况下
  不同（用的是每条单独施加属性的结果）；多几次求值。Metis 那边有同样的问题（方法参数是
  多定理事实且带属性时，名字 `foo(k)[attrs]` 与实际用的定理可能不同），Metis 不能换定理，
  只能按「名字读回来是这条才用」的规则退回；是否处理、怎样处理并入 F 的扫描。
- **D**：作者问它是不是 bug。答：不是 bug，是一个分支没有被任何测试跑到。两轮评审都只是读
  代码对照了原版。为了不留隐患，至少要把这个分支真正跑一次（需要 MaSh 已有学习状态，可以
  在 private tree 自己的用户目录里做，不影响别的树）；要不要再加进测试会话待定。
  **【实测，2026-11-11 晚】这个分支真正跑过了**（private tree，探针
  `ai-artifacts/sh_trigger_error_probe/g_ml/G_ML.thy`；先用 `Sledgehammer_MaSh.mash_learn` 让
  MaSh 学习，`mash_can_suggest_facts_fast` 为真之后调用 `relevant_facts`，名额 64，目标 `R 7`）：
  - 不指定 `fact_filter`、有一个生成事实的触发器：返回三份名单 `mesh`、`mepo`、`mash`，各 64
    条，生成的事实在三份里都是第 0 位。
  - 同上、没有触发器：三份名单，都不含它。
  - `fact_filter = mesh`：一份名单，含它。`fact_filter = mash`：一份名单，不含它（MePo 不运行，
    主计划第 8 节已接受）。
  - 有触发器时的 `mash` 名单，恰好等于没有触发器时的 `mash` 名单在 MePo 的序号处插入生成的
    事实再截到 64 条。
  不足：生成的事实在 MePo 里的序号是 0，所以「插在同一个序号」只在序号 0 上验证过；非 0 的
  序号由测试会话里对 `insert_generated_facts` 的单元检查覆盖（序号 16）。要不要把这个探针变成
  测试会话的一部分（它要先学习，约 20 秒，状态写在该树自己的用户目录里）待定。
- **E 修**：README 写明第 3、4 版的修正和行为变化，文案要作者批。
- **F**：由一个 Opus agent 做全面扫描，目标是不再有第 5 版。
- **G**：现在就核实主计划第 7 节里仍未核实的各项。

### 3.2 F 的结果：全面扫描（Opus agent，2026-11-11 晚）

报告全文在 MLML 仓库的 `ai-artifacts/sh_release4_sweep_report.md`（不提交）。它**只读了源码，
什么都没跑**；下面每一条在采用之前都要在草稿或 private tree 里实测。它确认七个被补丁的文件
之外没有别的差异，并在末尾列了「查过、没问题」的清单（MePo 的全部改动、合并函数、
`string_of_xref'`、Metis 起名不抛异常、中断没有被吞掉，等等）。

**新发现，逐条待作者定**（「原版」= Isabelle2026 原版就有，不是本 feature 引入的）：

| # | 问题 | 来源 | 后果 | 修在哪 | 我的建议 |
|---|---|---|---|---|---|
| S1 | tactic prover 永远作用在第 1 个子目标上，不管 Sledgehammer 被要求证第几个。`Try0_Util.apply_raw_named_method` 固定 `Select_Goals 1`，`run_tactic_prover` 把整个状态交给它。例：`sledgehammer [provers = simp] 2` 时 `simp` 证掉了第 1 个子目标，却被报告成找到了证明 | 原版 | **错误的结果**；M1（`auto` 等）修掉之后 tactic prover 成功得更多，更容易碰到 | `sledgehammer_prover_tactic.ML`（已在补丁里）。两种做法：先 `Proof.prefer` 到目标子目标并在文本前加 `prefer n`（Sledgehammer 自己的一行证明就是这种写法）；或者子目标不是第 1 个时直接放弃 | 修。两种做法在草稿里都试，交评审选 |
| S2 | ATP 或 SMT 找到的证明，只要其中一条事实的名字读不回来，整个证明就丢了：`sledgehammer_instantiations.ML` 的 `instantiate_facts` 对每个名字求值，没有任何处理器，预演失败后走到这里一抛异常，结果变成「未知」 | 原版 | 找到的证明不显示。A 修掉之后最常见的起因没了，但别的起因还在（印出的命题读回来类型不同等） | `sledgehammer_instantiations.ML`，**新增被补丁的文件**：任何名字求值失败时返回 `NONE`，退回已有的「重构失败」消息 | 修。它是把任何名字缺陷放大成「证明丢失」的那一环 |
| S3 | `meth_of` 没有 `fast` 的分支，也没有别的包注册的方法的分支，一律落到 `metis`。开着 `instantiate` 选项时，`fast` 证出来的东西被印成 `by (metis …)`；`simp` 实际用的是 `using f by simp`，被印成 `simp add: f` | 原版，非默认模式 | 印出的证明文本不是实际成功的那个方法 | `sledgehammer_prover_tactic.ML`：`meth_of` 返回 option，没有对应时保留 Try0 自己的文本 | 修 |
| S4 | MePo 接受「一串引用」作候选名字（如 `PQ nothing`，求值恰好一条定理），但 tactic prover 只认「恰好一个引用」，于是它们对这条候选一律放弃 | **本 feature 的代码** | 输入很刻意，后果是悄悄少了几个 prover | `sledgehammer_mepo.ML` 的 `accept_item`：改用 `Attrib.eval_thms ctxt [xref_of_name ctxt name]` 求值，使「MePo 接受的名字每个 prover 都能读」按构造成立。报错文案不变 | 修 |
| S5 | 归纳规则实例化用的谓词文本（`p_inst`）同样经 `hackish_string_of_term` 压缩空白 | 原版，非默认模式 | 目标含带多个空格的字符串常量时，实例化出的规则没用 | 与 A 同一个文件，用同一个打印函数 | 随 A 一起修 |
| S6 | README 有三句不准确、八处缺失（报错在 `try`、Mirabelle 等处并不终止 Sledgehammer；`hyp_ts`/`concl_t` 的形状取决于调用者；第 2–4 版的各项修正和行为变化；触发器在所有 MePo 调用者处运行；`typargs_of_ptype` 没提；同名注册会替换；等等） | 文档 | | README | 并入 E，文案给作者批 |
| S7 | 测试的空白一长串：tactic prover 走 `using` 的路径、没有名字的局部事实经真实的 tactic prover、子目标不是第 1 个、`hyp_ts` 非空、多个触发器的顺序、Metis 的匿名/字面/带引号的多定理参数，等等。另有两处检查偏弱：`e`、`cvc5` 没装时悄悄跳过；两次真实的 `metis` 调用只查不抛异常 | 测试 | | 测试会话 | 补（自决）。**注意**：任何会载入 MaSh 状态的测试都会让同一次构建里之后的测试改走合并路径，测试会话里不能有 |
| S8 | 几处小的：`indexes_of_selection` 对非法区间悄悄返回空（注释写明前提）；候选名字前后带空格会让 Metis 拼名字出错；等 | 本 feature | 很低 | 各自的文件 | 改（自决） |

**它对已知各项的评估：**

- **M1（`auto` 等拿到全局事实）**：只有 Sledgehammer 的 tactic prover 会填 direct 类，`try0` 命令、
  Auto Try0、`try`、Mirabelle 的 try0 都不受影响。没有任何东西依赖 `allows_directs = true`。
  AFP 的 Zippy（`zip*`）用同一个配置、同一个参数解析器，今天同样失败，同一处修改也会修好它。
  默认的 `provers` 列表包含所有注册过的 Try0 方法，所以默认调用就会受影响；2.3 的尝试次数
  （`auto` 0 和 16，`fastforce` 0、16、32，`force` 只有 0）它也确认了。
- **A**：一行，同一个文件，不动签名：
  `fun cartouche_term ctxt = close_form #> Syntax.pretty_term ctxt #> content_of_pretty #> cartouche`。
  **不要动 `hackish_string_of_term` 本身**：它还被 Sledgehammer 的 spying、Nitpick、Nunchaku 的
  哈希和 AFP 的 Isabelle_DOF 使用。`cartouche_thm` 的另一个使用者是
  `contrib/auto_sledgehammer/library/sledgehammer_solver.ML`（把这种名字写进它缓存的证明文本）。
  仍然存在的原版局限：印出的命题读回来可能是别的项（类型不显示、记号有歧义）。
- **B**：在 `metis_instantiations.ML`（**新增被补丁的文件**）。`open_attrib` 不在签名里；改成同时
  返回开头和结尾。它确认这个错实际上走不到（匿名事实没有 schematic variable）。可以经已导出的
  `Metis_Tactic.pretty_name_inst` 测。
- **C**：方向成立。对 Sledgehammer：每条定理单独求值
  `Attrib.eval_thms ctxt [(xref_j, args)]`，用的是用户原来的 token（报错位置仍指向用户的
  文本）。只有属性会改变上下文、后面的属性又读它时结果才变。**今天 tactic prover 和预演本来就是
  逐条单独求值的，只有 ATP 拿到的是整体求值的第 j 条；改完之后所有 prover 一致。** 一个例外要
  保留：没有属性时仍然整体求值（结果相同；否则对巨大的事实是平方级的）。
  对 Metis：定理由 Isar 定死，换不了；正确的做法是「名字读回来确是这条才用」，这需要一个
  Metis 看得见的文本求值函数。它建议只写进文档、不写代码。**这一点待作者定**：若要做，把
  `xref_of_name` 那几行（只用 Pure 的函数）放到 Metis 看得见的 `Try0_Util` 里即可，第 3 版否决
  这个挪动的理由（没有调用者需要）就不成立了。
- **D**：它逐个模式对照原版，结论是这个分支正确。并指出**这是真实用户从第二次调用
  `sledgehammer` 起走的主路径**（第一次调用只用 MePo 并启动学习），不是冷僻分支。最便宜的
  确定性测试：把 `Par_List.map` 之后的那段提成一个纯函数，用构造的输入测；要新增一个签名
  条目。不要把「先让 MaSh 学习再测」做成测试会话的一部分（见 S7 的注意）。

**下游**（它查的）：三个下游 feature 都不补丁这七个文件，也不补丁 `metis_instantiations.ML`，
没有文本冲突；它们的测试都不用 Sledgehammer、Try0、Metis。`light_locale` 未提交的工作改了
`Pure/Isar/attrib.ML`，而 Metis 起名依赖 `Attrib.gen_thm` 把整条事实存在名字 token 的值里；
它合并之后应当构建一次 `Sledgehammer_Fact_Trigger_Test`（那里断言了这个值）。

**若上表全部照建议做，被补丁的文件从七个变成九个**：加 `metis_instantiations.ML`（B）和
`sledgehammer_instantiations.ML`（S2）。

## 4. 做法（第 3 版的教训，照做）

1. 全面扫描（上表 F），把候选收齐，一次请作者定范围。
2. 草稿实现并实测（办法见主计划 13.5 和维修方案第 2 节：共享树的 HOL 会话上用 `ML_file`
   载入修改后的文件；草稿在 MLML 仓库的 `ai-artifacts/` 下，不提交）。2.3 的行为变化需要
   `sledgehammer` 命令本身跑新代码，草稿环境做不到，只能在 private tree 构建后测，构建要
   作者下令。
3. 据实写本计划的正式稿，方案和草稿代码一起送对抗评审（CLAUDE.md 的 typical review workflow）。
4. 评审之后自己改的东西和新写的测试，在打标签之前再过一次小范围评审。
5. 发布之前单独发一条短消息，只列「已知但这一版不修的问题」，逐条要作者明确确认。
6. 作者下令后：改 private tree、构建、提交、检查清单、`make-patches … 4`、推送、conda 试运行、
   正式发布（现在的发布流程：补丁工具 1.1.0，`features` 写成
   `xqyww123/Sledgehammer_Fact_Trigger@Isabelle2026/sledgehammer_fact_trigger/4`）。
7. 下游（第 5 节）。

## 5. 下游：第 4 版会让三个 feature 再迁移一次

直接建在本 feature 上的有三个（各自 `.gitmodules` 的 `base`）：

| feature | 现状 | 谁在照看 |
|---|---|---|
| `default_fact_qualifiers` | 已合并第 3 版（`e0b9191`，已推送），检查清单只读跑过全过。标签 `…/1` 建在第 2 版上，**从未上过频道** | 它的会话已退出；作者让本会话处理 |
| `global_form` | 在第 3 版上出了它的第 2 版（MLML 提交 `e529f741` 的说法），不在频道上 | 原是会话 `global form`，2026-11-11 晚已联系不上 |
| `light_locale` | `.gitmodules` 的 base 已改成本 feature，但合并还没做（private tree 里有 35 个未提交的文件） | 会话 `Minilang Upgrading` |

【已定，2026-11-11 晚】作者：「default_fact_qualifiers 短时间内不会发布」。所以它现在不发布，
也不出第 2 版；第 4 版出来之后给它再做一次 base 迁移（作者此前让本会话处理它），发布与否
到时等作者下令。

关于 memory：我提议把这次的教训记进 memory，作者拒绝（「这些应该发给你的 Antropic，所以给我
raise feedback!」）。已按作者的要求起草了一份反馈（本地排队，由作者决定是否发出）。不要再
提议把它记进 memory。

通知情况（2026-11-11 晚）：`Minilang Upgrading` 已被告知第 4 版要来。`global form` 会话联系
不上（不在会话列表里，消息没有送达），`global_form` 这个 feature 眼下是否有人照看不清楚，
已报告作者。

## 6. 压缩之前各处的状态

已发布：`isabelle-sledgehammer-fact-trigger 2026.0.3`、`isabelle-patch-control 1.1.0`（详见
主计划 13.8）。

未提交的修改：
- 本文件（新文件，提交须作者批准）。
- 主计划 `SLEDGEHAMMER_FACT_TRIGGER_PLAN.md`：13.8 节和文件头。
- `RELEASE_3_REPAIR_PLAN.md`：4.1 节加了一句指向本文件的话。
- `contrib/default_fact_qualifiers/ai-artifacts/DEFAULT_FACT_QUALIFIERS_PLAN.md`：第 5 节补了
  现状。

未推送的提交：MLML 的 `728767d0`（更新三个 submodule 指针）。

等作者答复的：
1. 第 3 节的 A–G 各项要或不要（F 的扫描结果出来后会有补充）。
2. `default_fact_qualifiers`：是否按第 5 节的提案等第 4 版。
3. 上面这些未提交的文档是否提交，`728767d0` 是否推送。
4. 是否把这次的教训记进 memory（需作者明确批准）。
5. 早先遗留的：那封关于 unary concept 计划第 7 节的来信该转给哪个会话；concept 一侧搁置的
   问题清单在 MLML 仓库的 `ai-artifacts/CONCEPT_UNARY_PENDING_PLAN_EDITS.md`。

草稿和探针（都在 MLML 仓库的 `ai-artifacts/` 下，不提交）：`sh_release3_draft/`（第 3 版的
草稿实现、探针、变异副本）、`sh_trigger_typecheck/`、`sh_trigger_error_probe/`、
`sh_xref_print_probe/`、`sh_name_probe/`。
