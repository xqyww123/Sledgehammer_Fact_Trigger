# 第 4 个发布的维修方案

状态：rev 3，2026-11-15。rev 1 经第一轮对抗评审判为「修改后接受，需要复评」；rev 2 并入了七条
意见和作者据此作的三个决定，复评判为「修改后接受，不需要再评」（第 7 节）；rev 3 改掉复评指出
的那一处（3.2 的检查）和它认可的小项。作者：与测试、文档相关、不改变设计的，我可自决。
作者 2026-11-15 批准把改动放进 private tree；七个文件 2026-11-18 在 private tree 里提交为
`0f47be1` 并已推送，HOL 和测试会话构建通过，十二个变异体全部被测试抓到；正式的测试文件和 README
经过第三次评审并已改完（第 7 节）。第 4 节的 12 条 2026-11-17 全部由作者定完，代码不因此改动。
作者 2026-11-18：**先不发布，可以提交和推送**。现状和下一步见 `RELEASE_4_WORK_PLAN.md` 第 10 节。

标记：【实测】= 跑过；【读码】= 只读了源码；【来自评审】/【来自扫描】= 评审或扫描 agent 读码
得出、我没有逐条核对；【已定】= 作者已决定。

源码路径相对于 Isabelle2026 的 `src/`。相关文档：`RELEASE_4_WORK_PLAN.md`（范围、步骤、进度、
评审记录的全文）、`RELEASE_4_PLAN.md`（经过和扫描结果）、`RELEASE_3_REPAIR_PLAN.md`、
`SLEDGEHAMMER_FACT_TRIGGER_PLAN.md`（主计划）。

## 1. 范围

作者定的范围【已定】：M1、A、B、C、D、E、S1–S5，加我自决的 S6–S8。作者的要求：这一版把已知
的收齐，不要第五版；行为变化不能擅自做；维修方案一定要评审。

评审之后作者的决定【已定，2026-11-15】：
- C 只改 Sledgehammer 一侧；Metis 一侧不改，列入已知不修（3.4）。
- S3 多走一步：preplay 没有成功时不替换 Try0 的命令（3.8）。
- 新增的导出名字 `Sledgehammer_MaSh.facts_of_filter_results` 批准（3.5）。

不在范围内【已定，2026-11-12】：Sledgehammer 输出的多步 Isar 证明里的语句。

本稿覆盖代码各项和测试（S7）。README（E、S6）：作者 2026-11-15 说「与测试、文档相关的，在不
改变设计的前提下，你可以自决」，所以 README 由我改写、经评审，改完给作者看（第 6 节），不再
逐字请示。

## 2. 草稿和依据

草稿在 MLML 仓库的 `ai-artifacts/sh_release4_draft/`（不提交）。`draft.diff` 是相对第 3 版的
差异，`base/` 是第 3 版的原文件。这一版改动七个文件：`try0_util.ML`、
`metis_instantiations.ML`、`sledgehammer_fact.ML`、`sledgehammer_instantiations.ML`、
`sledgehammer_mepo.ML`、`sledgehammer_mash.ML`、`sledgehammer_prover_tactic.ML`。

办法：在共享树的 HOL 会话上用 `ML_file` 依次加载草稿文件（isabelle-mcp）。限制【实测】：
`sledgehammer` 命令和 `Sledgehammer.run_sledgehammer` 仍是 heap 里的旧代码；`metis` 方法因为
重新注册而是草稿目录里的那份。草稿目录里的 `metis_tactic.ML` 与第 3 版只差一处：
`lambda_def` 写成 `Metis.lambda_def`（那条事实在 `HOL.Metis` 之外被隐藏），这一处只为草稿环境，
不进发布；`draft.diff` 里它是 `metis_tactic.ML` 的唯一差异。经 `sledgehammer` 命令的端到端
检查要等改动进了 private tree 才能跑（5.3）。

【实测，2026-11-15；每个数字都是新起的会话里从头跑一遍得到的】
- `Release4_Draft.thy`：121 项检查全部通过（rev 3 的草稿；汇总的数字可能不含写在
  `lemma … proof … qed` 里面的几条检查，它们可能在汇总之后才执行。发布的测试里 `check` 失败
  就报错，以构建为准）。下面的 45 和 20 是 rev 2 时跑的，此后只改了 3.2 的那条检查和注释。
- `Trigger_Draft.thy`（现有的触发器测试加新增的）：45 项全部通过。
- 对照 `base/Release4_Base.thy`：由 `Release4_Draft.thy` 只换理论名机械生成，跑在第 3 版的文件
  上。20 项失败，另有两段直接报错（M1：`Bad arguments for method "auto"`；D：函数不存在）。
  失败的正是下面要修的各项；第 3 版已有的检查在那里全部通过。**每次改了草稿的检查，都要
  重新生成对照并重跑**（rev 1 的对照是旧的一份，评审指出后重做）。

## 3. 各项

### 3.1 M1：`auto`、`fastforce`、`force` 拿到全局事实

**问题**【实测】：Sledgehammer 的 tactic prover 把全局事实作为 Try0 的 direct 类事实交给方法。
`Try0_Util.full_attrs` 的 `allows_directs = true`，Try0 于是把事实写在方法名后面：`auto foo`。
这三个方法不接受这种参数，报 `Bad arguments for method "auto"`，prover 放弃。

**修法**：`HOL/Tools/try0_util.ML` 里 `full_attrs` 的 `allows_directs` 改为 `false`。Try0 对不
接受 direct 类事实的方法已有的做法是把它们放进 `using`：`using foo by auto`。一个值。

**谁受影响**【来自扫描】：只有 `run_tactic_prover` 填 direct 类事实；`try0` 命令、Auto Try0、
`try`、Mirabelle 的 try0 不变。AFP 的 Zippy（`Zip_Try0.thy`）用同一个配置，同样被修好；
【实测，全文搜索】MLML 的 `contrib/`（含两份 AFP）里除了它没有别处用 `full_attrs`。

**草稿里的检查**【实测】：三个方法各得到 `using QR["OF" PQ [ OF P7 ]] by <方法>`；`simp:` 前缀
的事实仍写在方法里；没有事实时不变。

**行为变化的实测**【实测，2026-11-15】。办法：不改 private tree；探针会话（MLML 仓库
`ai-artifacts/sh_m1_probe/`，建在 private tree 的 HOL 上）把三个方法在 Try0 的方法表里重新注册
成 `allows_directs = false` 或 `true`，对 20 个单子目标的目标各跑默认配置的
`Sledgehammer.run_sledgehammer`（只关掉 `learn`；8 线程），改前改后各两遍。跑了两次：第一次
进程里没有载入 MaSh 状态，事实只来自 MePo；第二次先载入 MaSh 状态（80 次调用都确认
`mash_can_suggest_facts_fast` 为真），走的是默认配置下第二次调用起的合并名单。

| | 只有 MePo：改前 → 改后 | MaSh 已载入：改前 → 改后 |
|---|---|---|
| 没有找到证明的次数（各 40 次） | 0 → 0 | 0 → 0 |
| 总耗时（秒） | 156.4 → 160.6 | 227.3 → 228.4 |
| 报告「found a proof」的总数 | 265 → 263 | 296 → 286 |
| 其中 `fastforce` | 16 → 56 | 16 → 59 |
| 其中 `auto` | 16 → 25 | 16 → 22 |
| 其中 `force` | 16 → 16 | 16 → 16 |
| 其中外部 prover（cvc5、vampire、verit、spass、zipperposition、e） | 133 → 86 | 144 → 92 |
| 出现带 `using` 的 `fastforce` 证明的目标数（共 20） | 0 → 11 | 0 → 10 |
| 出现带 `using` 的 `auto` 证明的目标数 | 0 → 4 | 0 → 2 |

- 新出现的证明形如 `using card_mono by fastforce (15 ms)`。
- `force` 不变：默认调度下它只有 0 条事实的那一次尝试。
- 外部 prover 报告的证明少了约三分之一。原因【读码】：`max_proofs` 默认是 4，找到 4 个证明
  之后不再启动新的尝试；tactic prover 更快，名额先被它们用掉。没有一个目标因此失去证明。
- 证明里有时留着一条用不到的事实。只有 MePo 的那次，改后有 4 处（`using measure_induct by
  auto` 两次、`using add_right_imp_eq by fastforce`、`using injD top_apply by fastforce`），
  改前 `simp` 也有 3 处。【实测，2026-11-16】`measure_induct` 那处的原因：16 条事实的那次
  尝试走 `linear_minimize`，它按顺序每次去掉一条、留下的不再重试。剩 `measure_induct`、
  `nat.exhaust_disc` 两条时，去掉 `measure_induct` 的那次测试只剩 `nat.exhaust_disc`，而
  `using nat.exhaust_disc by auto` 在 10 秒内不结束（`by auto` 3 毫秒、两条都用 8 毫秒），
  于是 `measure_induct` 被留下，空集从没有被测试。两次运行结果相同。所以多出的事实不是因为
  时限短：一条事实会让方法失败或不终止，就会挡住排在它前面的事实被去掉。
  `injD top_apply` 那处两次一样的运行给出不同结果（另一次是 `using injD by fastforce`），
  像是时限的缘故，没有核实。rev 1 至 rev 3 写的「【来自评审】时限短」对 `measure_induct` 这处
  不对。这是原版最小化的行为，M1 只是让这三个方法也带着事实进了最小化。探针在 MLML 的
  `ai-artifacts/sh_release4_draft/minimize_probe/`。
- MaSh 开着学习时，这些新证明会像别的证明一样被学进去【读码】；实测关了学习。

### 3.2 A、S5：没有名字的局部事实的名字，归纳规则实例的谓词

**问题**【实测】：没有名字的局部事实（以及 `this`）的名字是 `‹命题›`。打印命题用的
`hackish_string_of_term` 先按 76 列排版，再把连续空白压成一个空格；字符串常量里的空白也被压掉。
`have "length ''a  b'' = 4"`（两个空格）得到名字 `‹length ''a b'' = 4›`，是另一个命题。
`instantiate_induct_rule` 里归纳谓词的文本 `p_inst` 用的是同一个函数。

**修法**（`HOL/Tools/Sledgehammer/sledgehammer_fact.ML`）：新增局部函数
`fun line_of_term ctxt = Syntax.pretty_term ctxt #> content_of_pretty`（`ATP_Util.content_of_pretty`
是 `Protocol_Message.clean_output o Pretty.unformatted_string_of`：一行、无标记、不动 token 内部
的空白），`cartouche_term` 和 `p_inst` 改用它。`hackish_string_of_term` 本身不动【来自扫描】：
Sledgehammer、Nitpick、Nunchaku 的 spying 散列和 AFP 的 Isabelle_DOF 在用它。

**别的调用者**【来自扫描和评审】：`cartouche_term` 经已导出的 `Sledgehammer_Fact.cartouche_thm`
被 `auto_sledgehammer` 用到（`library/sledgehammer_solver.ML`），它拿到的名字相应地保留空白；
那里有一句注释提到 `hackish_string_of_term`，在另一个仓库里。

**检查**【实测】：名字是 `‹length ''a  b'' = 4›`；一条很长的命题的名字与期望的一行字符串
逐字相同；它出现在 `nearly_all_facts_of_context` 的结果里；归纳规则实例的名字是
`nat.induct[where P = "λn. length ''a  b'' + n = n + 4"]`，实例的命题里是原来的字符串。

**归纳规则实例的检查依赖原版的时限**：`instantiate_induct_rule` 在原版里包在
`try (Timeout.apply 0.01 秒 …)` 里，超时和任何错误都悄悄变成「没有这个实例」。【实测】本机
300 次调用没有一次丢实例，中位数 2.7 毫秒，99 分位 5.1 毫秒，最大 7.8 毫秒，余量不大；发布的
构建跑在 linux-64、linux-aarch64、win-64 的机器上，`tools/release_build.sh` 没有设
`timeout_scale`。做法【我自决；裁判推荐的那种】：测试会话的选项里设 `timeout_scale = 5`（并把
`timeout` 从 600 改成 120，会话的时限是两者的乘积，不变），检查要求必须得到实例（最多试 100
次），再比较它的名字和命题。`timeout_scale` 把这个会话里每个 `Timeout.apply` 的时限都乘以 5；
没有哪条检查靠超时发生来通过。【实测】这样的会话里 `Timeout.scale ()` 是 5.0。这与作者的 SKILL
isabelle-patch-feature 3.4 第 4 步的建议一致。rev 2 写的是「得不到实例就跳过」：复评指出它在
`p_inst` 读不回时照样通过，【实测】确实如此（变异体见 5.3），已作废。

**修不到的**：名字是 Isabelle 打印出来的命题，Isabelle 不保证它能读回成同一个命题。3.7 保证
这种情况下找到的证明不再丢失。

### 3.3 B：Metis 给匿名事实加 `of` 实例化

**问题**【实测】：`Metis_Instantiations` 的 `open_attrib` 对以 `]` 结尾的名字去掉末尾的 `]`、
接上 `, `，结尾固定是 `]`。匿名事实 `[[simp]]` 于是成了 `[[simp], of x]`，Isar 读不了。

**修法**（`HOL/Tools/Metis/metis_instantiations.ML`，新增的被补丁文件）：`open_attrib` 换成
`attrib_brackets`，返回开头和结尾两段文本：名字形如 `[[…]]` 时属性放进它自己的方括号里
（`[[of x]]`、`[[simp, of x]]`），其它情况同原来。名字两端的空白先去掉（触发器给的名字若带
尾部空白，原来得到 `foo[a] [of x]`）。函数不导出，签名不变。

**检查**【实测】，经已导出的 `Metis_Tactic.pretty_name_inst`：`[[]]`、`[[simp]]`、`[[ ]]`、
`foo[OF bar[of y]]`、`foo`、`foo(2)`、`‹P 7›`、`foo[a] `（尾部空白）八种名字，以及没有实例化时
名字原样返回。

### 3.4 C：多定理事实带会改变上下文的属性（只改 Sledgehammer 一侧）

**背景**【实测】：`pair` 是两条定理 `f x = h x` 和 `P (f y) ⟹ Q y`。`pair[simplified, simp]` 整体
求值时属性逐条应用，上下文从一条传给下一条：第一条被声明为 simp 规则之后，第二条被化简成
`P (h ?y) ⟹ Q ?y`。而 `pair(2)[simplified, simp]` 单独求值得到 `P (f ?y) ⟹ Q ?y`。

一个名字指哪条定理，取决于同一个证明里它前面的名字：Isar 读 `using` 和方法参数里的多个引用
时上下文从前一个传到后一个，Try0 也把一次尝试的全部事实放在一个 `Attrib.eval_thms` 里求值
【来自评审；两个名字一起求值与单独求值结果不同这一点实测】。只有外部 prover 的输入、preplay
和 `instantiate_facts` 是逐个名字单独求值的。所以**没有一种起名方式在所有情况下都对**。

**问题**【实测】：第 3 版在名字 `pair(2)["simplified", "simp"]` 下交给 prover 的是
`P (h ?y) ⟹ Q ?y`，而这个名字单独读是 `P (f ?y) ⟹ Q ?y`。对目标 `P (h 7) ⟹ Q 7`，
`by (metis pair(2)[simplified, simp])` 失败，`by (metis pair(1)[simplified, simp]
pair(2)[simplified, simp])` 成功【实测】。prover 只用第二条就能证这个目标，于是只含第二个名字
的证明是失败的那种【推断，未经 `sledgehammer` 命令端到端跑】。

**修法**【已定：采用】（`sledgehammer_fact.ML` 的 `fact_of_ref`）：引用带属性时，先取不带属性的
整条事实算出各条的单条引用，再对每条单独求值 `Attrib.eval_thms ctxt [(单条引用, 属性)]`，把
求值得到的定理交给 prover。每个名字单独读回来就是交给 prover 的那条定理【实测】。引用不带
属性时仍整体求值一次（结果相同；`atp_problem_import` 会传很大的不带属性的事实，逐条取是
平方级【来自扫描】）。带属性时每条定理各取一次整条事实，动态事实每次重算【来自评审】；带
属性的引用是用户手写的，不会很大。

**行为变化**：对这种事实，交给 prover 的第二条及以后的定理与第 3 版不同。属性不改变上下文时
定理与第 3 版相同【实测：`four`、`four(3-, 1)`、`imps[of 7]`、`imps(2-, 1)[of 7]`、`two`、
`two(2)[symmetric]`、`nothing`、`nothing[simp]`、动态事实 `algebra_simps(2-3)[symmetric]`】。

**残留**（第 4 节第 3 条）：证明里把这条事实的几个名字都列出来时，Isar 和 Try0 按顺序一起读，
后面的名字读成的定理可能与 prover 单独拿到的不同（上例里一起读时第二条是 `P (h ?y) ⟹ Q ?y`）。
上例里证明照样成立；一般情况不保证。第 3 版是反过来：都列出来时一致，只列后面的名字时不
一致。原版对不同引用之间也是这样（`sledgehammer (foo[simp] bar[simplified])`）【来自评审】。

**Metis 一侧不改**【已定】。用户手写 `by (metis pair[simplified, simp])` 并开着
`metis_instantiate` 时，Metis 建议 `by (metis pair(2)[simplified,simp, of "7"])`，照抄回去证明
失败【实测，第 3 版】。rev 1 的修法（名字单独读回来不是这条定理就不起名）在真实调用里无效
而且有害【实测】：`metis` 方法拿到的上下文是解析完参数之后的，属性的声明已经在里面，检查
形同虚设，还重复声明 simp 规则、多出 `Ignoring duplicate rewrite rule` 警告。改对要在 `metis`
方法里做额外的求值，得到的也只是一句不完整的建议。作者决定不改，列入第 4 节第 4 条。草稿的
`metis_tactic.ML` 已恢复成第 3 版。

### 3.5 D：`relevant_facts` 出名单的那段

**问题**：MaSh 学习过之后，`relevant_facts` 给出三份名单（合并的、MePo 的、MaSh 的）。合并和
插入的逻辑在已导出的 `mesh_facts_with_mepo`、`insert_generated_facts` 里，有测试；只有 MePo 的
分支经 `relevant_facts` 有测试。没有测试的是 `relevant_facts` 末尾的十来行：出三份还是一份、
三份各是什么。走到它需要磁盘上的 MaSh 状态，会话测试里不能载入。2026-11-11 手工跑过一次，
结果正确。

**修法**（`HOL/Tools/Sledgehammer/sledgehammer_mash.ML`）：把 `Par_List.map` 之后的那段原样提成
`facts_of_filter_results : Proof.context -> int -> string option -> string -> (fact * origin) list option * ((fact * real) list * fact list) option -> (string * fact list) list`
（上下文、`max_facts`、用户给的 `fact_filter`、实际生效的 fact filter、MePo 和 MaSh 各自的
结果）。`relevant_facts` 改为调用它，再对每份名单做原来的 `add_and_take`。行为不变【读码：逐行
对照；评审同样结论】。

**新增的签名条目**【已定：作者批准名字】：`Sledgehammer_MaSh.facts_of_filter_results`，记入
`tools/signature_additions.txt`。

**检查**【实测】，用构造的输入：三份名单的名字和顺序；MePo 的名单；MaSh 的名单里生成的事实
在它的 MePo 位置上；`fact_filter = mesh` 只给一份；只有 MePo；`fact_filter = mash`。

### 3.6 S1：tactic prover 永远作用在第 1 个子目标

**问题**【实测】：`run_tactic_prover` 把整个证明状态交给 Try0，Try0 只作用在第 1 个子目标，
成功的标准是「子目标数减少了」。目标是 `True` 和 `R 7`、要求证第 2 个时，`simp` 证掉了第 1 个，
Sledgehammer 报告找到了证明，文本证的却是第 1 个子目标。

**修法**（`HOL/Tools/Sledgehammer/sledgehammer_prover_tactic.ML`）：要求的子目标不是第 1 个时，
把 `Proof.prefer subgoal state` 交给 Try0，并在 Try0 给的命令前加 `prefer n `。状态和文本前缀
由同一个 `if` 给出，不会不一致。思路与 Sledgehammer 自己的单行证明相同
（`apply_on_subgoal`），文本的顺序不同：这里是 `prefer n using … apply …`，那里是
`using … prefer n apply …`【来自评审】；两种都是合法的 Isar。

**检查**【实测；括号里是同一检查在第 3 版上的结果】：
- `True`、`R 7`，证第 2 个：`prefer 2 using QR["OF" PQ [ OF P7 ]] apply simp`，这段文本作为真实
  的 Isar 证明跑通（第 3 版：没有 `prefer 2`）。
- 第 1 个子目标证不了、第 2 个能证：成功（第 3 版：`Gave up`）。
- `True`、`R 7`、`True`，`auto` 不带事实证第 2 个：放弃（第 3 版：`Try this: apply auto [1]`，
  把证掉第 1 个当成功）。
- `Q 99`、`True`、`True`，`auto` 证第 2 个：`prefer 2 apply auto [1]`（第 3 版：`Gave up`）。
- 状态带 chained 事实：`prefer 2 apply simp` 用到了它（第 3 版：`Gave up`）。
- 子目标是第 1 个时文本里没有 `prefer`。

`auto` 这类处理多个子目标的 Try0 方法成功后会接着处理其余的子目标；`prefer` 之后原来排在前面
的子目标挪到了后面，也在其中【来自评审】。这是原版对 `auto` 的做法（第 4 节第 7 条）。

`Proof.prefer` 在 chain 模式下报错【读码】，但走不到：`run_sledgehammer` 先做
`Proof.assert_backward`；万一报错，已有的处理把 `ERROR` 变成「Gave up」。

**没有采用的做法**：子目标不是第 1 个时直接放弃。更简单，但 tactic prover 在 `sledgehammer`
命令带子目标编号时就完全不可用。评审没有反对 `prefer`。

### 3.7 S2：一条事实的名字读不回，外部 prover 找到的证明就整个丢失

**问题**【来自扫描；失败的那一步实测】：preplay 失败后，
`Sledgehammer_Instantiations.instantiate_facts` 对每个用到的事实的名字调用 `thms_of_name`，外面
没有处理器。任何一个名字读不回，异常一路传到 `launch_prover_and_preplay`，结果变成
`SH_Unknown`，已经找到的证明不显示。

**修法**（`HOL/Tools/Sledgehammer/sledgehammer_instantiations.ML`，新增的被补丁文件）：名字求值
放进 `try`；有名字读不回时 `instantiate_facts` 返回 `NONE`（它本来就用 `NONE` 表示「没有推出
实例化」），调用者按已有的路径显示证明文本和「One-line proof reconstruction failed」。签名不变。

**检查**【实测】：名字里有一个读不回时返回 `NONE`、不抛异常（第 3 版抛 `ERROR`）；名字都读得
回时得到 `PQ[of "7"]`、`P7`。

### 3.8 S3：tactic prover 已经证出的证明被别的文本换掉

**问题**【实测】：tactic prover 的结果里带着 Try0 实际运行并成功的命令。但只要 Sledgehammer
之后对它做了 preplay，消息就改用 preplay 的文本。这只在显式开 `instantiate` 且推出了实例化时
发生（默认路径不对 tactic prover 做 preplay【来自评审】）。两种坏情况：
- `fast` 和 HOL 之外注册的方法（AFP 的 Zippy）在 `meth_of` 里没有对应的 `proof_method`，一律
  当成 `Metis_Method`：`fast` 证出来的证明被印成 `by (metis …)`。
- preplay 失败或超时：`simp` 实际证出的是 `using QR["OF" PQ [ OF P7 ]] by simp`，显示的却是
  `One-line proof reconstruction failed: by (simp add: QR[OF PQ[OF P7]])`，或
  `Try this: by (simp add: …) (> 1.0 s, timed out)`。preplay 的写法与 Try0 的不同（事实放在
  `simp add:` 里、带实例化），时限也可能更短，所以它失败并不说明 Try0 的证明有问题。

**修法**【第二点已定：采用】（`sledgehammer_prover_tactic.ML`；`meth_of` 不在签名里）：
`meth_of` 返回 option；消息只在「这个 Try0 方法有对应的 `proof_method`，并且 preplay 的结果是
`Played`」时采用 preplay 的文本，其余情况显示 Try0 的命令。`preferred_methss` 的类型是原版签名
里的，没有对应时仍填 `Metis_Method` 作后备，与第 3 版相同。

**行为变化**（只在显式 `instantiate` 下）：preplay 失败或超时时，显示 Try0 运行过的命令，不再
显示重构失败或「timed out」的文本；`fast` 等显示自己的命令。`instantiate` 加
`preplay_timeout = 0` 时，第 3 版印的是带实例化的命令，没有验证过，也没有任何标记【来自评审：
`string_of_play_outcome (Play_Timed_Out 0)` 是空串】；现在印 Try0 运行过的命令，里面没有用户要
的实例化。这是「只采用 `Played` 的结果」这条规则的直接结果，已告知作者。

**检查**【实测；括号里是第 3 版】：`fast` 配 Metis 的 preplay 结果，消息是 `using … by fast`
（`by (metis QR[OF PQ[OF P7]])`）；`simp` 配失败的 preplay，消息与没有 preplay 时相同
（`One-line proof reconstruction failed: …`）；配超时的 preplay 同样；配成功的 preplay，消息是
`by (simp add: QR[OF PQ[OF P7]])`，不变。

**仍然存在的**（第 4 节第 6 条）：preplay 成功时显示的是 preplay 的证明，它经过验证，但与 Try0
实际运行的不是同一个写法。原版如此。

### 3.9 S4：MePo 接受 tactic prover 读不了的候选名字

**问题**【实测】：MePo 用 `thms_of_name` 求值候选的名字，它接受几个引用连写；tactic prover 用
`xref_of_name` 读名字，只接受恰好一个引用。候选名字 `PQ nothing`（两个引用，共一条定理）被
MePo 接受，所有 tactic prover 却读不了、放弃。

**修法**（`HOL/Tools/Sledgehammer/sledgehammer_mepo.ML` 的 `accept_item`）：改用
`Attrib.eval_thms ctxt [xref_of_name ctxt name]` 求值。

**用户可见的变化**：报错文案不变（主计划 4.4 的两句），但两个引用连写的名字从「evaluates to
2 theorems, but exactly one is expected」变成「cannot be evaluated:」加一行语法错误【实测】。
现有测试里「two theorems」那条改用一个含两条定理的事实。

**检查**【实测】：一个引用照常；`PQ nothing` 报「cannot be evaluated」；含两条定理的事实、
`nothing`、未定义的事实各报原来的那一句。现有的触发器测试全部通过。

### 3.10 S8

`Try0_Util.indexes_of_selection` 的注释加「valid」。别的小项走不到或不现实，不动。

## 4. 已知、这一版不修的（发布前逐条请作者确认）

1. Sledgehammer 输出的多步 Isar 证明里的语句：字符串里的空白被压缩；加在常量上的类型标注
   打印时丢失。【已定】不修。
2. 没有名字的局部事实的名字是打印出来的命题，可能读不回成同一个命题（3.2）。一条这样的
   名字有歧义时，tactic prover 的整次尝试放弃，因为 Try0 把事实放在一起求值。【实测】
   （2026-11-16，评审先指出）两条局部事实 `(0::int) ≤ 1` 和 `(0::nat) ≤ 1` 的名字都是
   `‹0 ≤ 1›`，Isar 读它时报 `Ambiguous specification of literal fact`；目标 `Q 7`、事实 `P7`、
   `PQ` 时 metis 得到 `by (metis P7 PQ)`，再加上这两条用不到的事实，结果是 `Gave up`。只有其中
   一条时名字读得回，因为 Isar 按文本去找对得上的局部事实。有名字的那条（`foo`）不受影响。
   例子在 MLML 的 `ai-artifacts/sh_release4_draft/Unnamed_Fact_Example.thy`。【已定】接受
   （作者 2026-11-16）。
3. 多定理事实带会改上下文的属性：证明里把它的几个名字都列出来时，后面的名字读成的定理可能
   与 prover 拿到的不同（3.4）。【已定】接受。
4. Metis 自己的提示信息（没用到的定理、`metis_instantiate` 的建议）里，多定理参数带这种属性
   时第二条及以后的定理名字不对（3.4）。【已定】不修。
5. tactic prover 的证明里有时留着一条用不到的事实（3.1）。原版最小化的行为：逐条去掉事实时，
   另一条会让方法不终止的事实挡住了它（实测的那处）。不会让本来证得出的目标证不出：最小化
   只在证出之后开始，只去掉去掉后仍能证的事实，失败时用原证明（`maybe_minimize`）。
   【已定】接受（作者 2026-11-16）。
6. tactic prover 在 `instantiate` 下、preplay 成功时，显示的是 preplay 的写法而不是 Try0 实际
   运行的写法（3.8）。原版。【实测，2026-11-16】目标 `R 7`、prover `simp auto`：默认显示
   `using P7 PQ QR by simp`；加 `instantiate` 显示 `by (simp add: P7 PQ[of "7"] QR[of "7"])`。
   显示的证明都实际跑成功过；默认 `instantiate = smart` 下 tactic prover 不做 preplay【读码】。
   【已定】接受（作者 2026-11-16）。
7. `auto` 这类处理多个子目标的方法，成功时会顺带处理其余的子目标（3.6）。从第 1 个子目标
   开始时是原版的行为；这一版加了 `prefer n` 之后，其余的子目标里也包括原来排在前面的。
   【实测，2026-11-16】子目标 `x + 0 = x`、`R 7`、`Q 99`，`sledgehammer [provers = auto] 2` 给出
   `prefer 2 using P7 PQ QR apply auto [2]`，粘贴后只剩 `Q 99`。只有 `auto` 在 Try0 里登记为处理
   多个子目标。【已定】接受（作者 2026-11-16）。
   **【更正，2026-11-17】** 上面「原版的行为」说得不准：这违反 Sledgehammer 自己的约定。
   `proof_method_command`（`sledgehammer_proof_methods.ML`）写出的证明只作用在所求的子目标上：
   前面加 `prefer i`，还有别的子目标时用 `apply`，多目标方法再加 `[1]`。tactic prover 显示的是
   Try0 自己的命令，不守这个约定。是原版的缺陷；后果是证明文本多证掉别的子目标，不给出错误的
   证明。它使 auto_sledgehammer 先拆再证的分支报 `No subgoal!`（工作计划 9.3 第 11 条）。根源
   修复的难点是文本：Try0 只看到一个子目标时写 `by auto`，真实状态里应是 `apply (auto)[1]`；
   改字符串、改用 Sledgehammer 的写法、改 Try0 接口各有代价，都比在 auto_sledgehammer 里修难。
   【已定】第 4 版不修根源，仍按接受处理；auto_sledgehammer 自己修（作者 2026-11-17 同意）。
8. `Sledgehammer_Tactics.run_prover` 交给 prover 的状态是 `Proof.init ctxt`【读码】，没有目标，
   tactic prover 在那里必然放弃【来自评审】；它排在 `provers` 第一个时这个入口就没有结果。原版；
   用到它的是 Mutabelle 和 TPTP 的工具【来自评审】。【实测，2026-11-16，第 4 版与不带本包的
   共享树结果相同】`sledgehammer_with_metis_tac` 证 `R 7`：vampire、cvc5 证出；auto、metis、simp
   没有结果；`(1::nat) + 1 = 2` 上 auto、simp 也没有结果。直接原因：Try0 在 `Proof.init` 的状态上
   报 `No proof goal`，被 `run_tactic_prover` 变成 Gave up。另外它给 tactic prover 的事实上限取第
   一个 slice 的 0 条。【全文搜索】Mutabelle 的调用在注释里；TPTP 只传 SPASS、Vampire、E、
   Satallax；MLML 的 `contrib/`（含 AFP，不含 ICSE27）里没有别的调用者。
   **【已定】不修**（作者 2026-11-17 先定「这个也是要修的」，得知 auto_sledgehammer 不用
   `Sledgehammer_Tactics` 后改定：「不影响我们的 auto_sledgehammer 的 bugs 全都先不修」）。
   下面是改定之前讨论到的修法，留作以后参考：
   - 状态【已定，作者 2026-11-17 赞同】：用 `Proof.theorem` 以第 i 个子目标的命题建一个只有这个
     目标的状态，调用者给的 chained 事实用 `Proof.using` 放进去；问题里子目标编号 1、子目标数 1，
     `goal` 用新状态的目标（顺带改掉原代码把子目标数传成 i）。外部 prover 也用这个状态，一条路；
     改前改后实测外部 prover 的结果，若变了再分开。
   - tactic prover 用哪个 slice：待定。
   - 证出后怎样重放：待定。
9. `auto_sledgehammer` 的 `fast_mepo` 没有局部事实时不调用 MePo，触发器不运行。原因在
   `run_mepo_and_render`（`sledgehammer_solver.ML` 第 1338–1339 行）：候选池为空就不调用 MePo。
   **【已定】在 auto_sledgehammer 里修**（作者 2026-11-17）：候选池为空也调用 MePo。和
   `No subgoal!`、没有 target 的修复一起做（工作计划 9.3 第 11 条）。
10. `try` 命令和自动 Sledgehammer 吞掉触发器的报错（主计划第 7、8 节）。【实测】（2026-11-16，
    第 4 版的 HOL）同一目标：坏触发器注册前 `try` 由 Sledgehammer 找到证明；注册后 `try` 只输出
    `Tried in vain`；`sledgehammer` 命令显示报错原文。自动 Sledgehammer 只读了码
    （`src/Tools/try.ML` 第 84–95 行）。【已定】接受（作者 2026-11-16）。
11. 主计划第 8 节的「已知且接受的后果」。第 1、2、3、5 点【已定】接受（作者 2026-11-17）；
    第 4 点（候选比触发它的常量晚一轮被接受、名次偏低）作者问能否做名次补正，待议。
    【实测，2026-11-17，MLML `ai-artifacts/sh_release4_draft/mepo_round/`】同一个命题 `S 1`，目标
    `T 1`、事实 `S x ⟹ T x`：作为候选池里的普通事实排第 3；由「`S` 变成相关时」触发的触发器生成，
    排第 18；由「目标常量 `T`」触发的触发器生成，排第 4。原因：MePo 容许一个还不相关的常量，所以
    池里的事实第 0 轮就被接受；触发器要等 `S` 在第 0 轮之后变成相关才被告知，候选最早第 1 轮。
    MePo 对生成的候选打分并无偏差，滞后来自触发器被告知的时机。第 1 轮里它得满分 1.0，排在五条
    带 simp 加分（1.03–1.09）的事实之后，故 12 + 6 = 18。讨论过三种补正（同一轮里补一次、事后挪到
    上一轮末尾、生成候选专用加分），都改不了「晚一轮出现」，例子里都约到第 13。
    **【已定】第 4 版不改打分和名次**（作者 2026-11-17）；README 写明：候选在触发器得知常量之后
    才出现，在目标常量上触发就没有滞后；候选的 `stature` 影响它的分数。以后用实测数据定一个
    经验性的补正（作者建议，见工作计划）。
12. Try0 运行时把事实求值成裸定理交给 `using`，属性所作的声明（如 `foo[simp]`）在 Try0 的运行
    里不生效；印出来的 `using foo[simp] by auto` 被粘贴后，声明会生效【来自评审】。原版；M1 让
    `auto`、`fastforce`、`force` 的全局事实也走这条路。【实测，2026-11-17，MLML
    `ai-artifacts/sh_release4_draft/declaration_probe/`】目标
    `(case xs of [] ⇒ (0::nat) | y # ys ⇒ y) ≤ sum_list xs`：`auto` 失败、`auto split: list.split`
    成功；Try0 带 `using list.split[split]` 失败（声明不生效）；粘贴的 `using list.split[split]
    apply auto` 成功（生效）；auto_sledgehammer 的重放形式 `((insert list.split[split])[1], auto)`
    失败（不生效）。所以 auto_sledgehammer 的重放与 Try0 的运行一致，这一条不会让它出错；受影响的
    是把文本粘贴进证明的 `sledgehammer` 命令用户。**【已定】这是期望行为，不是 bug，不修**
    （作者 2026-11-17）。

## 5. 文件、签名、测试、顺序

### 5.1 被补丁的文件和签名

九个文件：第 3 版的七个，加 `HOL/Tools/Metis/metis_instantiations.ML` 和
`HOL/Tools/Sledgehammer/sledgehammer_instantiations.ML`（`tools/patched_files.txt` 相应加两行）。
这一版改动其中七个；`metis_tactic.ML`、`sledgehammer_util.ML` 不动。新增的签名条目只有 3.5 的
一个；已有的条目一个不改。

### 5.2 测试（S7）

草稿的检查改写成测试会话里的测试（`check` 失败即构建失败）：
- `Fact_Reference_Test.thy`：3.1 的直接检查（Try0 的三个方法带 direct 类事实、`simp:` 事实、
  没有事实；不需要 `sledgehammer` 命令，`force` 在默认调度下端到端走不到）；3.2–3.4、3.6–3.8 的
  检查；扫描报告指出的空白（`blast`、`argo` 的 direct 类事实，`intro:`、`dest:`、`elim:` 前缀，
  字面事实的文本是普通字符串时的打印，动态事实，Metis 的匿名和带引号的多定理参数，tactic
  prover 带一条没有名字的局部事实）。
- `Sledgehammer_Fact_Trigger_Test.thy`：3.5、3.9 的检查，加触发器的输入（两个触发器都运行、
  同名注册替换、第一轮之前的调用、`accepted` 逐轮累积、`new_consts` 在 `rel_consts` 里）。
- 经 `Sledgehammer.run_sledgehammer` 的端到端测试（已写进 `Sledgehammer_Fact_Trigger_Test.thy`，
  要等改动进了 private tree 才能构建）：`provers = auto` 和 `fastforce` 配一个生成的全局事实，
  消息里有 `using QR["OF" PQ [ OF P7 ]] by <方法>`（3.1）；两个子目标、证第 2 个，消息里有
  `prefer 2 using … apply simp`（3.6）；`provers = simp`、`instantiate = true`、
  `preplay_timeout = 0`，消息里是 Try0 的命令 `using QR["OF" PQ] by simp`（3.8）。都不需要外部
  prover。3.4 没有端到端测试：tactic prover 是按名字重新求值的，只有外部 prover 直接用
  `fact_of_ref` 交出的定理，而新增的测试不用外部 prover；3.4 由直接调用 `fact_of_ref` 的检查
  覆盖（它在第 3 版上失败）。

规则：
- 文本里含 Isabelle 打印出来的 term 的，比较字符串，不读回【作者的建议】；只含事实引用语法的，
  保留「求值得到的就是那条定理」。
- **测试会话关掉 MaSh**：`tests/ROOT` 的选项加 `MaSh = "none"`，并加一条检查
  `not (Sledgehammer_MaSh.is_mash_enabled ())`。原因【来自评审】：状态带 chained 事实时
  `run_sledgehammer` 不管 `learn` 参数都会学习，学习会载入并改写用户目录里的 MaSh 状态，此后
  同一进程里不带 fact filter 的调用都改走合并名单。关掉之后这条规则不靠每个测试自己记住。
  D 的检查直接调用提出来的函数，不需要 MaSh。
- 归纳规则实例的检查见 3.2。
- 已发布的 `hammer` 检查在装了 `e`、`cvc5` 的机器上会运行它们，没装就跳过。它从第 1 版起就
  在，这一版不动；新增的测试都不用外部 prover。

### 5.3 顺序

作者明确同意后把改动放进 private tree → 构建（已授权）、跑测试会话 → 对新测试做变异核对
（每个修法一个改回去的变异体，测试会话必须失败；S5 另加一个「`p_inst` 读不回」的变异体：去掉
`|> lambda (Free ind_x)`，草稿环境里已实测它被现在的检查抓到）→ README 的改写（文档，我自决，
改完给作者看）→ 发布前的短消息（第 4 节）→ 提交、发布各自等作者下令。

## 6. README 的要点（改写稿另交）

- 「触发器抛异常或候选求值失败会让 Sledgehammer 报错停下」要补上例外：`try` 和自动
  Sledgehammer 吞掉报错，Mirabelle 记进日志后继续。
- 「tactic prover 接受带属性的事实名字」：到这一版对 `auto`、`fastforce`、`force` 才成立。
- `hyp_ts`、`concl_t` 的形状取决于调用者，主计划 4.1 的准则要进 README。
- 第 2、3、4 版修了什么，以及 3.1、3.4、3.6、3.8、3.9 的行为变化。
- 候选名字必须恰好是一个事实引用；`Sledgehammer_MePo.typargs_of_ptype`；同名注册替换。

## 7. 评审记录

**第一轮（2026-11-15，对 rev 1）：「修改后接受，需要复评」。** 三个评审者（对照源码的正确性；
行为变化与同类问题是否收齐；优雅与测试），每条意见一个新的辩护者，一个裁判；Opus、`xhigh`、
只读。七条意见全部成立，两条部分成立。每条我都自己跑过或读过核实（探针
`ai-artifacts/sh_release4_draft/Review_Probe.thy`、`Metis_Example_*.thy`、`Pair_Example_*.thy`）。
全文和核实的结果在 `RELEASE_4_WORK_PLAN.md` 8.5 节。

| 意见 | 处理 |
|---|---|
| C 的 Metis 一侧在错的上下文里求值，真实调用里无效并多出警告 | 作者决定 Metis 一侧不改；草稿恢复第 3 版（3.4） |
| 3.4「tactic prover 按名字单独求值」不成立；C 只是换了哪种情况对 | 3.4 重写；残留列入第 4 节；作者决定保留 Sledgehammer 一侧的改法 |
| S3 只去掉一个原因：preplay 失败或超时仍换掉 Try0 的命令 | 作者决定采纳评审的做法（3.8） |
| 3.1 对「留下用不到的事实」的原因和次数写错 | 3.1、第 4 节第 5 条改正 |
| 归纳规则实例的检查依赖 0.01 秒的时限（「读回 term」那一半被驳回） | 实测了余量；检查改成得不到实例时跳过；删掉重复的一条（3.2） |
| 经 `run_sledgehammer` 的测试可能载入并改写 MaSh 状态；M1 的探针其实只走了 MePo | 测试会话关掉 MaSh（5.2）；补跑了载入 MaSh 的探针（3.1） |
| 第 3 版的对照用的是旧的一份检查 | 重新生成并重跑；写明每次都要重做（第 2 节） |

**复评（2026-11-15，对 rev 2）：「修改后接受，不需要再评」。** 两个评审者（第一轮的裁决是否
落实；评审之后的改动本身），每条意见一个辩护者，一个裁判。rev 2 落实了第一轮的各条裁决；两条
意见都指向同一处并都成立：rev 2 新改的归纳规则实例的检查在得不到实例时跳过，于是 `p_inst`
读不回时照样通过，而且是否用 `timeout_scale` 本该提给作者。【实测】变异体在 rev 2 的检查下
通过。处理：作者表示测试和文档相关、不改变设计的我可自决；采用裁判推荐的做法（3.2）。复评
认可的小项已并入：第 4 节第 12 条；3.8 对 `instantiate` 加 `preplay_timeout = 0` 的准确说法；
第 4 节第 3、7 条的标注；两处注释；3.8 的端到端测试；第 2 节对汇总数字的说明。全文在
`RELEASE_4_WORK_PLAN.md` 8.6 节。

**第三次评审（2026-11-15，对评审之后才写的东西：正式的测试文件和 README）：「修改后接受」。**
两个评审者（测试；README），每条意见一个辩护者，一个裁判。四条意见都成立或部分成立，都是测试
和文档的事：
- 四条经 `run_sledgehammer` 的测试匹配一段连续的文本，而那段文本只在最小化把多余的事实全部
  去掉时才出现；最小化的每次测试时限很短（约 1 秒），机器卡顿时可能留下一条多余的事实，测试
  就误报失败。改成检查同一条消息里的几个片段；最小化照常开着。
- README 没写 M1 的可见后果（`max_proofs` 的名额先被 tactic prover 用掉，外部 prover 报告的证明
  变少）；`hyp_ts`、`concl_t` 那段没有给出可操作的做法（`fastype_of1`、`Term.dest_abs_fresh`）；
  「Known limits」里 Isar 那条没说限制是什么。都已补上。
- 小项：README 的几处措辞（`prefer n` 只在不是第 1 个子目标时出现；「事实列表」特指
  `sledgehammer (foo bar)` 这种写法；`typargs_of_ptype` 的对象；Mirabelle 那句的说法；每个
  「before」指什么，并加了一段「New in version 2026.0.4」）；候选名字和三份名单的检查从
  `Fact_Reference_Test.thy` 挪到 `Sledgehammer_Fact_Trigger_Test.thy`，用那里已有的辅助函数。
  没有采纳的一条：README 里补一句第 3 版 Metis 对没有名字的事实的处理，因为我没有核实它的
  确切行为。
改过的测试重新构建并重做变异核对，结果记在 `RELEASE_4_WORK_PLAN.md` 8.8 节。

第一轮裁判认为值得做的小项都已并入：S1 的判断合成一处；3.6 的两处措辞；3.2 列出 `auto_sledgehammer`；
3.4 的开销；第 4 节新增第 2 条的后半和第 8 条；M1 的直接检查进测试文件；3.5 的措辞；
`tools/patched_files.txt`；已发布的 `hammer` 检查的去留（5.2）。
