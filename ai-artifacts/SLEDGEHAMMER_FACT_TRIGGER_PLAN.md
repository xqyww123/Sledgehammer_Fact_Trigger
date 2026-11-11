# Sledgehammer fact trigger 计划

状态：已实现并发布为 `isabelle-sledgehammer-fact-trigger 2026.0.1`（现状见 13.6）。
设计稿 rev 3，2026-11-11（UTC）定稿；实现期间作者改定的地方已并入各节（5 节第 3 处修法等）。rev 1 和 rev 2 各经过一轮对抗评审
（结论都是「修改后接受」），本稿已并入两轮的结论和作者的决定。第二轮没有发现设计缺陷，只补了
说明和测试；作者定不再评第三轮。评审记录见第 12 节。

标记约定：【已定】= 作者明确批准；【自决】= 作者交给实现者自行决定的实现细节，
此处记录所做的选择；【后果】= 由设计带来、作者已知情并接受的行为；
【实测】= 跑出来的数据，不要重测；【未核实】= 只凭读源码或推断，实现时须验证。

源码指 Isabelle2026 发行版，路径相对于它的 `src/`。MePo 的代码一律按函数名引用，不写行号：
补丁本身会让行号移动。MePo 的文件是 `HOL/Tools/Sledgehammer/sledgehammer_mepo.ML`。

探针文件在 MLML 仓库的 `ai-artifacts/sh_name_probe/`（未提交）。

---

## 1. 这是什么

**fact trigger 是 MePo 迭代里的一个可编程钩子：每当有常量新变得相关，或已相关的常量获得新的
类型实例时，已注册的函数可以现场给出新的候选事实，这些候选和普通定理一样参加 MePo 的打分
和选择。**

动机：有些事实对证明有用，但不值得、或不可能事先全部存成定理。起因是 concept 设计里的祖先
事实：一条深度为 N 的继承链上的一个实例，若把「该实例满足每个祖先 concept」都存成定理，
是 N²/2 条。改成只存叶子事实（如 `ring int.ring`）和每条继承边一条 parent 规则，祖先事实
（如 `monoid int.ring`）在需要时由 OF 链推出，存储是线性的。simplifier 一侧用 simproc 按需
推出；Sledgehammer 一侧就需要这个钩子。

本计划只做通用机制。concept 的触发器是它的一个使用者，不在本计划范围内。

「常量」一词在本文按 MePo 的用法：真正的常量、固定变量（`Free`），以及两种伪常量：
不在等式右侧的 λ 抽象算一个；每条定理所属的 theory 算一个（theory 伪常量，见 2.4）。

## 2. 背景：MePo 的流程

入口是 `relevance_filter`。输入：候选池（全部可见定理）、目标的前提与结论、名额
`max_facts`。

### 2.1 准备阶段（一次）

1. 频率表 `const_tab`：扫一遍候选池，统计每个常量（按名字和类型实例）的出现次数
   （`count_fact_consts`）。之后不再变化。
2. 每条候选配上它的常量列表（`pair_consts_fact`）；一个常量都没有的丢弃；分数为「未计算」。
3. 初始相关常量集合 = 目标前提和结论里的常量（`goal_const_tab`）。

### 2.2 一轮（`relevance_filter` 里的 `iter`）

状态：剩余名额、当前阈值、相关常量集合 `rel_const_tab`、待评列表（每条带「未计算」或缓存
分数）、搁置列表（带旧分数，本轮不看）。

1. 打分：待评列表逐条取缓存分数或现算（`fact_weight`）；≥ 阈值的入围。
2. 挑选（`take_most_relevant`）：分数 > 0.99999 的全要；其余按分数取若干条（开始约 12，
   随剩余名额降到 1）；总数截到剩余名额。
3. 扩散：被接受定理的所有常量并入相关常量集合，得 `rel_const_tab'`。**表项发生变化的常量**
   称为本轮新增常量（判断函数 `is_dirty`，比较某常量在新旧两张表里的整个表项）。
   表项变化有两种：新出现的名字；已有的名字多了一个结构上不同的类型实例
   （`add_pconst_to_table` 按 `ptype_eq` 判重，其中类型变量与固定类型不相等）。
4. 重新分配：含新增常量的落选候选放回待评列表并清空分数；不含的，落选和原搁置的进搁置
   列表，入围未取的带缓存分数留在待评列表。
5. 阈值按接受条数上升，剩余名额减去接受数。
6. 输出本轮接受的，递归。名额用完或某轮无入围时停止。

缓存分数之所以准确，是因为频率表固定，而相关常量集合的变化由 `is_dirty` 追踪。

`iter` 结束后还有一步 `insert_special_facts`：按需把 `ext` 和几条集合定理插到结果的固定
位置，并在名额已满时截掉结果的末尾。所以 `iter` 接受的定理不一定都在最终结果里。

### 2.3 分数

分数 = 相关常量权重和 ÷（相关常量权重和 + 不相关常量权重和 − 身份加分）。常量全部相关
时为 1.0。身份加分由 `stature`（作用域 × 规则类别）决定（`stature_bonus`）。打分不受
schematic variable 改名的影响。

### 2.4 theory 伪常量

打分前把每条定理的命题包一层，等于在它的常量列表里加一项「所属 theory 名 + 固定后缀」
（`theory_constify`）；目标结论同样加当前 theory 名。权重很低，只起微调作用。

### 2.5 出 MePo 之后

- 输出顺序就是接受顺序；接受时的分数不保留。
- 各 prover slice 取名单的前若干条。
- `Sledgehammer_MaSh.relevant_facts` 并行运行 MePo 和 MaSh（`Par_List.map`），产出三份名单：
  合并的、纯 MePo 的、纯 MaSh 的。发行版的 slice 里约 118 个用合并名单，约 15 个用纯 MePo，
  约 13 个用纯 MaSh。
- 合并（`mesh_facts`）只看名次。某条定理不在某个筛选器的名单里时：属于该筛选器「没学过的
  定理」则那一侧不计入平均，否则按 0 分计入（`mesh_facts` 里的 `score_in`）。

### 2.6 【实测】轮数与规模

环境：HOL `Main`，候选池 16371 条。方法：把 `sledgehammer_mepo.ML` 复制为探针并在每轮
结束处计数（探针目录里的 `mepo_probe.ML`、`MePo_Rounds.thy`）。

| 目标 | 名额 | 轮数 | MePo 耗时 | 扫描的常量总数 | 新增常量总数 | 重新打分总数 |
|---|---|---|---|---|---|---|
| `rev (xs @ ys) = rev ys @ rev xs` | 1024 | 27 | 0.78 s | 3396 | 115 | 45135 |
| 同上 | 256 | 12 | 0.48 s | 851 | 45 | 10669 |
| `finite A ⟹ card (A ∪ B) + card (A ∩ B) = card A + card B` | 1024 | 21 | 0.83 s | 3378 | 85 | 43517 |
| `a dvd b ⟹ gcd a b = abs a`（int） | 1024 | 14 | 0.67 s | 3859 | 48 | 19985 |
| 同上 | 64 | 3 | 0.48 s | 184 | 13 | 8290 |

每轮新增常量 1 到 12 个（含 theory 伪常量）；几乎每轮都有新增常量。

## 3. 接口

【已定】本节全部，含类型名、构造子名、字段名、函数名。

### 3.1 触发器（在 `Sledgehammer_MePo` 里）

```ML
(* MePo 已有的类型，导出为抽象类型：一个常量的一个类型实例 *)
type ptype
val typargs_of_ptype : ptype -> typ list

type candidate =
  {name    : string,     (* Isar 事实表达式，如 "QR[OF PQ[OF P7]]" *)
   prop    : term,       (* 打分和去重用的命题；是提示，不被验证（4.3） *)
   stature : stature}    (* ATP_Problem_Generate.stature，决定身份加分 *)

type trigger_input =
  {ctxt       : Proof.context,
   hyp_ts     : term list,                 (* 目标的前提 *)
   concl_t    : term,                      (* 目标原本的结论，不含 theory 伪常量那层包装 *)
   new_consts : string list,               (* 本轮新增常量的名字，不过滤伪常量 *)
   rel_consts : ptype list Symtab.table,   (* 完整相关常量集合，MePo 的表原样传出 *)
   accepted   : lazy_fact list}            (* 已被 MePo 接受的定理，新的在前 *)

type trigger = trigger_input -> candidate list

val add_trigger : string -> trigger -> Context.generic -> Context.generic
```

- `ptype` 的定义是 `PType of int * typ list`（阶数 + 类型参数）；`typargs_of_ptype` 取第二个
  分量，常数时间。
- `lazy_fact = ((unit -> string) * stature) * thm`（`Sledgehammer_Fact`）。
- 注册用 Generic_Data，按名字存；同名视为同一个触发器。不提供删除。
- `hyp_ts` 和 `concl_t` 是 MePo 自己收到的目标参数，原样传出，**形状由 MePo 的调用者决定**，
  MePo 不做统一（它管不了第三方调用者，也补不回丢失的类型信息）：
  - Sledgehammer 自己的调用者用 `ATP_Util.strip_subgoal`，把子目标的 ⋀ 约束变量换成新的
    `Free`，这些 `Free` 没有在 `ctxt` 里固定。
  - 别的调用者可能直接传拆出来的项，顶层带着没有绑定者的 `Bound`。例如 `auto_sledgehammer`
    的 `run_mepo_and_render` 用 `Logic.strip_assums_hyp` / `strip_assums_concl`。
  - 任何调用者下，绑定者之下的子项本来就含 `Bound`。

### 3.2 带来源的结果与合并（供发行版自身和外部的事实筛选器共用）

```ML
(* 在 Sledgehammer_MePo 里 *)
datatype origin = From_Pool | From_Trigger

val mepo_suggested_facts_with_origin :
  Proof.context -> params -> int -> relevance_fudge option ->
  term list -> term -> lazy_fact list -> (fact * origin) list

(* 在 Sledgehammer_MaSh 里，紧挨 mesh_facts *)
val mesh_facts_with_mepo :
  Proof.context -> int ->
  real * (fact * origin) list ->                    (* MePo 的权重和带来源的结果 *)
  (real * ((fact * real) list * fact list)) list -> (* 其它筛选器：权重，带分数的名单，没学过的定理 *)
  fact list

val insert_generated_facts : (fact * origin) list -> fact list -> fact list
```

- `mepo_suggested_facts` 保持原类型，等于 `mepo_suggested_facts_with_origin` 去掉来源。
- `mesh_facts_with_mepo` 内部做三件事：给 MePo 的名单按名次赋分；把来源为 `From_Trigger`
  的事实追加到其它每个筛选器的「没学过的定理」列表；调用现有的 `mesh_facts`。
  「生成的事实不被其它筛选器扣分」由它保证，调用者不需要知道。
- `insert_generated_facts` 把来源为 `From_Trigger` 的事实按它们在 MePo 名单里的序号插进
  另一份名单。它不绑定 MaSh。
- 外部的事实筛选器只需两步：调用 `mepo_suggested_facts_with_origin`，再调用
  `mesh_facts_with_mepo`。发行版的 `relevant_facts` 在 MePo 运行的模式下走同一条路径。
  MePo 不运行时（`fact_filter = mash`）保持对 `mesh_facts` 的原有调用，**绝不能**给
  `mesh_facts_with_mepo` 传一个空的 MePo 名单：那会让 `mesh_facts` 从单筛选器的分支切到
  多筛选器的分支，丢掉 MaSh「没学过的定理」。
- 外部筛选器若要让 MePo 与自己的筛选并行运行，调度由它自己做；这两个函数不管调度。

## 4. 行为

### 4.1 调用时机

- 【已定】每轮一次：2.2 第 3 步算出 `rel_const_tab'` 之后调用所有触发器，`new_consts` 是
  本轮新增常量的名字。
  【已定，2026-11-10】名额在某一轮用完时，那一轮之后不再调用：它产出的候选不会再被打分。
  这是实现时的做法，当时没有标明与上一句的字面不同，第二轮代码评审指出后作者接受。对纯函数
  的触发器来说它观察不到。README 因此写的是「每一轮之前调用」。
- 【已定】第 0 轮之前额外调用一次：`new_consts` 是初始相关常量集合的全部常量，`accepted`
  为空，产出的候选参加第 0 轮。理由有两条：目标里的常量如果表项此后不再变化（单态常量、
  固定变量、没有获得新类型实例的常量），就永远不会出现在新增常量里；表项会变的，也要到
  第 0 轮结束才出现，它的候选晚一轮才打分。
- 【已定】没有注册任何触发器时走原来的路径，`new_consts` 和 `accepted` 都不计算。
- 【已定】不设「触发器声明它关心哪些常量」的机制。触发器自己检查 `new_consts`，不相关时
  短路返回。
- 【已定】多个触发器按注册名的顺序依次调用，结果拼接。同一轮里所有触发器看到相同的输入；
  某个触发器刚产出的候选不进入 `accepted`（它们还没被接受）。
- 【已定】MePo 的所有调用者一律触发，不加开关。调用者清单见 6.1。

写触发器的准则：
- 能在一次调用里算完的推导，就在一条候选内部用 OF 链算完，不要拆成多条候选指望多轮扩散
  接起来（见 8 节第 4 条）。
- 同一个名字可能多次出现在 `new_consts` 里：每当它获得一个结构上新的类型实例时出现一次。
  各实例在 `rel_consts` 里。重复产出的候选由 4.3 的去重吸收。
- 计算 `hyp_ts`、`concl_t` 的子项的类型时，必须带着它的约束变量上下文（如 `fastype_of1`，
  或用 `Term.dest_abs_fresh` 打开绑定者）。不要假设拿到的是闭项（3.1）。
- 触发器是纯函数（4.4）。

### 4.2 输入

- 【已定】只传已接受的定理，不传落选者及其分数。
- 【已定】`rel_consts` 是 MePo 自己的持久化表，传指针，不转换、不复制。
- 【自决】`new_consts` 由本轮被接受定理的常量列表筛出 `is_dirty` 的那些并去重得到。
- 【自决】`accepted` 是迭代状态里新增的一个累计列表，每轮把新接受的接到前面。

### 4.3 候选的处理

- 【已定】触发器只输出候选，由 MePo 打分，与普通候选公平竞争。
- 【已定】候选在下一次打分时进入待评列表，分数未计算。
- 【已定】候选的定理在**被接受的那一刻**用 `Sledgehammer_Util.thms_of_name`（发行版已有）
  对 `name` 求值得到；落选的候选从不求值。
- 【已定】求值结果必须恰好一条定理。
- 【已定，2026-11-11 改】**不检查**求值得到的定理的命题与 `prop` 是否一致。`prop` 是打分
  和去重用的提示：交给 prover 和用于重放的是求值得到的那条真定理，所以不一致不会产生错误
  的结果，最坏只是这条事实的相关性分数算偏、或被错误地去重。假设触发器的实现是对的。
  由此触发器不必预测内核在 `OF` 时给 schematic variable 换的下标，也不必为此提前求值。
- 【已定】生成的候选之间由 MePo 按命题去重，触发器保持无状态。
  【自决】去重的键是 `Sledgehammer_Fact.normalize_vars prop`（发行版已有，Sledgehammer 自己
  就用它做 `Termtab` 的键；需要导出）。这样同一条事实经两条 OF 链得出时只占一个名额。
- 【已定】与候选池里已有定理的去重不做，交给下游的合并步骤。
- 【已定】命题里一个常量都没有的候选直接丢弃，与普通候选相同。
- 【已定】生成的候选的常量查频率表不能失败，频率也不能是 0。
  背景：`pconst_freq` 对查不到的常量名抛异常；查到名字但没有匹配的类型实例时频率为 0，
  导致权重无穷大、分数变成 0。
  【自决】做法：频率表保持固定，像原版一样。每条生成的候选带一张自己的频率表，等于固定表
  加上这条候选自己的出现次数（持久化结构上的一次廉价更新；为此把 `count_fact_consts` 改成
  接受一个命题）。这条候选按自己的表打分，恰如「候选池里只多了它一条」。候选池里的定理看到
  的频率不变，所以 2.2 说的「缓存分数准确」仍由结构保证。
- 【自决】候选的 theory 伪常量用当前 theory 的名字。它从一开始就相关，常量全部相关的候选
  仍得满分。

### 4.4 失败

【已定】下面三种情况都是触发器的 bug，直接报错，不丢弃、不降级为 trace。

- 触发器函数自己抛异常：不捕获，原样传播。它可以是任何异常，不只是 `ERROR`。
- 求值失败、求值结果不是恰好一条：用下面的文案（【已定】逐字批准；`<T>` 是注册名，`<N>` 是
  候选的 `name`）。

求值失败：
```
Sledgehammer fact trigger "<T>": the candidate <N> cannot be evaluated:
<Isabelle 原始报错>
```

不是恰好一条：
```
Sledgehammer fact trigger "<T>": the candidate <N> evaluates to <k> theorems, but exactly one is expected.
```

rev 1 里还有第三段「命题不一致」的文案；随 4.3 取消该检查而删除。

【自决】「求值失败」的范围：对 `name` 调用 `thms_of_name` 时抛出的**任何非中断的异常**，
不只是 `ERROR`。最典型的是 `OF` 或 `THEN` 链里两条定理对不上，这时 Isabelle 抛的是 `THM`
（`Drule.OF` 的 `OF: no unifiers` / `OF: multiple unifiers`），一路没有任何地方把它转成
`ERROR`。取消命题检查之后触发器不再提前求值，这类 bug 主要就在这里暴露。
- 用一个 `\<^try>\<open>… catch exn => …\<close>` 分支捕获。它在进入处理器之前就把中断重新抛出
  （`Isabelle_Thread.try_catch`），所以 MePo 被取消时不受影响。不要另写一个只捕获 `ERROR`
  的分支：发行版里围着 `thms_of_name` 的现成写法只捕获 `ERROR`，照抄会漏掉 `THM`。
- 文案里「Isabelle 原始报错」取 `Runtime.exn_message (Runtime.exn_context (SOME ctxt) exn)`。
  必须先附上证明上下文：不附的话 `THM`、`TERM`、`TYPE` 只打印出一行异常名和消息，不带
  涉及的定理和项，信息比原始报错还少。

- 【已定】触发器是纯函数，不改全局状态（MePo 与 MaSh 并行运行）。

【已定】作者提出「不做检查」时只指命题一致性；「恰好一条」保留，因为一条候选只能对应名单
里的一个位置。

### 4.5 与其它事实筛选器的关系

- 【已定】合并时把触发器生成并被接受的事实当作其它筛选器「没学过的定理」，使那一侧不计入
  平均，而不是按 0 分计入。由 `mesh_facts_with_mepo` 实现（3.2）。
- 【已定】把 MePo 接受的生成事实也放进纯 MaSh 那份名单，位置是它们在 MePo 名单里的同一个
  序号。由 `insert_generated_facts` 实现（3.2）。
- MaSh 自己不会推荐生成的事实：它按别名在传给它的候选池里找回定理
  （`find_suggested_facts`），生成的事实不在池里。它从已有证明里学到的是组成表达式的有名字
  的定理（如 `QR`、`PQ`、`P7`）。不为此做任何事。
- `contrib/Semantic_Embedding/Tools/Sledgehammer/sledgehammer_embedding.ML` 里有一个把 MePo 与
  向量相似度名单合并的筛选器，按现状它会把生成的事实降名次。【已定】这份代码已废弃，不管。
  事实：它依赖的注册函数 `Sledgehammer_MaSh.add_custom_fact_filter` 只存在于旧的
  `contrib/Isabelle2024` 树里，Isabelle2026 没有；加载它的 theory 也不在会话的 `ROOT` 里。
  将来若恢复，它按 3.2 的两步调用即可。

## 5. 名字表达式与重放

`candidate.name` 会原样写进 Sledgehammer 输出的证明文本，重放时由 Isar 解析。

【实测】（`SH_Name_Probe.thy`，三条引理 `PQ`、`QR`、`P7`，目标 `R 7`，只给一条事实
`QR[OF PQ[OF P7]]`）：

| 路径 | 结果 |
|---|---|
| ATP（`provers = e`） | 走通，预演通过 |
| SMT（`provers = cvc5`） | 走通，预演通过 |
| tactic prover（`provers = metis`） | Gave up；对照组用普通名字成功 |
| 手写 `by (metis QR[OF PQ[OF P7]])` | 通过 |

tactic prover 失败有两个独立的原因，【已定】两处都按正规方式修（不采用「把带属性的事实
一律放进 using 类」的绕法）：

1. **名字的解析**（`sledgehammer_prover_tactic.ML` 的 `run_tactic_prover` 里的
   `xref_of_fact`）。现状是手写的字符串处理，只认纯名字和 `name(3)`，属性一律为空。改为用
   `Parse.thm` 解析名字字符串，得到带属性的 `Try0.xref`。分词与 `thms_of_name` 相同，在
   `sledgehammer_util.ML` 里加一个共用的函数。cartouche 那一支保持原样。
   【实测】（`SH_Name_Probe2.thy`）这样解析后放进 using 类，metis、auto、simp 都成功。
2. **Try0 打印嵌套属性时带了 PIDE 标记**（`HOL/Tools/try0_util.ML` 的
   `Try0_Util.string_of_xref`）。direct 类的事实被打印成文本后在 `apply_raw_named_method` 里
   重新解析，带标记的文本解析失败。
   【实测】嵌套的 `QR[OF PQ[OF P7]]` 打印结果含标记，metis 和 auto 报
   `Outer syntax error: keyword "]" expected, but bad input`；单层的 `QR[OF PQ]` 不含标记；
   去掉标记后的文本 `QR["OF" PQ [ OF P7 ]]` 是合法 Isar（手写通过）。
   改为输出不带标记的文本：在原来的 `Pretty.unformatted_string_of` 之前加
   `Protocol_Message.clean_output`，与发行版 `sledgehammer_fact.ML` 的 `fact_of_ref` 打印属性的
   写法（`ATP_Util.content_of_pretty`）相同；`try0_util.ML` 加载得比 `ATP_Util` 早，所以写开。
   【实测，2026-11-10】改后打印结果是 `QR["OF" PQ [ OF P7 ]]`，metis 的 direct 类通过
   （`by (metis QR["OF" PQ [ OF P7 ]])`），simp 的 using 类通过。
3. **Try0 打印事实名时不加回引号**（同一个函数 `Try0_Util.string_of_xref`）。【已定，2026-11-10，
   代码评审发现】不是合法标识符的事实名，Sledgehammer 会加引号，最常见的是 `f.induct` 归纳
   证明里的归纳假设 `"1.IH"(2)`。原版手写的解析器把引号当成名字的一部分，查找失败，这个
   prover 放弃。第 1 处修法之后名字被正确解析成 `1.IH`，prover 能证出来，但 Try0 打印成
   `using 1.IH(2) by metis`，插入后解析不了。即第 1 处修法单独使用是一个退步，且不需要
   注册触发器就会发生。
   修法：打印名字时用发行版已有的 `Thy_Header.print_name'`（需要时加引号）；空名字（匿名的
   `[attributes]` 形式）原样保留。新增 `string_of_xref' : Proof.context -> Try0.xref -> string`，
   Try0 内部全部改用它，使打印与 `apply_raw_named_method` 里的重新解析用同一个上下文的
   关键字表，打印属性时也用它而不再用编译时的 `\<^context>`。原有的
   `string_of_xref : Try0.xref -> string` **类型不变**，定义为 `string_of_xref' \<^context>`。
   为什么要上下文：一个名字要不要加引号取决于关键字表，而关键字随 theory 增加；
   `try0_util.ML` 在直接建在 `Pure` 上的 `HOL.Try0` 里加载，编译时的关键字表几乎只有 Pure 的。
   为什么不直接改 `string_of_xref` 的类型（最初批准的是改类型）：发布的签名关卡
   （`isabelle-patch-control check-signatures`）要求 base 里已有的签名条目原样保留，feature
   只能新增条目。作者 2026-11-10 改定为现在的做法。
   这改变了原版 `try0` 对带引号名字的输出（原版打印出来也是坏的）。
   更正：上面「空名字（匿名的 `[attributes]` 形式）原样保留」里的语法写错了。匿名事实的写法是
   `[[attributes]]`（`Parse.thm` 的第一个分支），第 1 个发布把它打印成了 `[attributes]`，
   解析不了。见第 4 处。

4. **Try0 把每个属性各打一组方括号**（同一个函数）。【已定，2026-11-10，第二轮代码评审发现，
   第 2 个发布修】Isar 里一个事实后面只能跟一组方括号，多个属性用逗号隔开。原版和第 1 个
   发布把 `PQ[of 7, OF P7]` 打印成 `PQ["of" 7]["OF" P7]`，解析不了。原版里 Sledgehammer 到
   不了这里，是第 1 处修法让它可达：候选名字带两个以上并列属性时，全局事实配 metis 会让这个
   prover 放弃，局部事实则会报出一个插入后解析不了的证明。第 1 个发布的测试只用了单个属性
   （`QR[OF PQ[OF P7]]` 是嵌套，不是并列），没有查出来。
   修法：`string_of_xref'` 写成 `Parse.thm` 的逐分支逆运算。全部属性放进一组，用发行版已有的
   `Attrib.pretty_attribs`（没有属性时它什么都不打印）；匿名事实（名字为空且没有选择）在外面
   再套一层方括号，没有属性时打印 `[[]]`；字面事实和有名字的事实在后面接上属性。对有名字的
   事实和字面事实，属性为零个或一个时输出与原来逐字节相同；匿名事实的输出是有意改变的。
   作者的条件是先由一个 Opus agent 独立核对这个修法；它读源码逐项核对后结论为通过，并建议了
   两处已采纳的改动：复用 `Attrib.pretty_attribs` 而不是抄它的函数体；匿名分支的模式写成
   `Facts.Named (("", _), NONE)`，使 `""(n)` 这种带选择的空名字不被误当成匿名事实。
   它还指出两件不属于这次修改、没有处理的事：字面事实的文本里带着 YXML 标记（原版如此）；
   原版 `Sledgehammer_Fact.fact_of_ref` 给用户 `add:` 的事实起名时同样是每个属性一组方括号，
   这样的名字到了 tactic prover 会解析失败、该 prover 放弃（原版也是放弃）。
   【实测，草稿环境】16 种形式（普通名字、长名字、带选择、带引号、单个属性、嵌套属性、两个
   和三个并列属性、嵌套里含并列、匿名、空的匿名、字面事实、字面事实带属性、`where … , THEN …`、
   属性带多个事实参数、属性带引号里的项）解析、打印、再解析、再打印都稳定，可求值的那些前后
   求值出相同的定理；`by (metis QR[OF PQ, of 7, OF P7])` 通过。探针在 MLML 仓库的
   `ai-artifacts/sh_xref_print_probe/`（不提交）。

   另见：`auto` 带 direct 类事实时报 `Bad arguments for method "auto"`。这是把事实直接写在
   `auto` 后面造成的，与属性无关，没有查它在发行版里是否本来如此，不属于本计划。

## 6. 实现

【自决】本节除 6.4 外全部。

### 6.1 `sledgehammer_mepo.ML`

- 导出 `ptype`（抽象）与 `typargs_of_ptype`；新增 3.1 的类型与 `add_trigger`；新增 3.2 的
  `origin` 与 `mepo_suggested_facts_with_origin`。
- 迭代里的候选项改为两种情形的数据类型：候选池里的定理（现有的 `lazy_fact`），或尚未求值的
  触发器候选（带触发器名供报错使用，带 4.3 说的那张自己的频率表）。打分只用常量列表、
  `stature` 和频率表，两种情形都有。被接受时把后者求值成 `lazy_fact`（名字部分是返回 `name`
  的常函数）。
- **来源标记一直带到最终结果**，穿过 `insert_special_facts`：它的辅助函数越过标记读取定理，
  `ext` 和集合定理标为 `From_Pool`。这样「每条标为 `From_Trigger` 的事实都在结果里，位置就是
  它的序号」由结构保证，不需要另外维护一份可能与结果不一致的列表（2.2 末尾说的截断）。
- 迭代状态新增：`accepted` 累计列表、已见过的候选的去重键集合。频率表不进入迭代状态。
- 钩子位置：`iter` 里算出 `rel_const_tab'` 之后；以及 `iter 0` 之前的那一次。
- `mepo_suggested_facts` 是公开入口，发行版内外都有调用者，类型不变。调用者清单：
  - 发行版五处：`sledgehammer_mash.ML` 的 `prover_dependencies_of` 和 `relevant_facts`；
    `HOL/Tools/Mirabelle/mirabelle_sledgehammer_filter.ML`；`HOL/TPTP/atp_theory_export.ML`；
    `HOL/TPTP/mash_export.ML`。
  - MLML 的 contrib 里三处：`auto_sledgehammer/library/sledgehammer_solver.ML` 的
    `run_mepo_and_render`；`AutoCorrode/iq/Isar_Explore.thy`；已废弃的
    `Semantic_Embedding/Tools/Sledgehammer/sledgehammer_embedding.ML`。
  其中只有 `relevant_facts` 改用带来源的新函数（6.2）。

### 6.2 `sledgehammer_mash.ML`

- 新增 3.2 的 `mesh_facts_with_mepo` 与 `insert_generated_facts`。`mesh_facts` 不动。
- `relevant_facts`：MePo 一支改用 `mepo_suggested_facts_with_origin`；合并名单由
  `mesh_facts_with_mepo` 得出；纯 MaSh 名单经 `insert_generated_facts`；纯 MePo 名单去掉来源。
- **MePo 与 MaSh 必须仍然并行。** 现状是把两者作为同一个列表里的两个函数交给
  `Par_List.map`，这要求两者返回类型相同；改造后 MePo 返回带来源的名单，类型不同了。做法：
  仍然是一个 `Par_List.map` 跑两个函数，让它们返回一个局部的两情形结果类型（MePo 的结果，
  或 MaSh 的结果），之后再拆开。这样保留 `Par_List` 现有的取消和异常传播行为。不要改成
  先后运行。
- `fact_filter = mash` 和 `fact_filter = mepo` 两种单筛选器模式保持原有的调用（3.2）。

### 6.3 `sledgehammer_fact.ML`、`sledgehammer_util.ML`、`sledgehammer_prover_tactic.ML`、`try0_util.ML`

- `sledgehammer_fact.ML`：导出 `normalize_vars`（4.3 的去重键）。
- 其余三个文件：5 节的两处修法。

### 6.4 `contrib/auto_sledgehammer`（不属于本 feature 的补丁）

【已定】改。`raw_sledgehammer` 在 fork 出的任务里运行 `run_sledgehammer`，任务结果经
`Future.join_results` 后被丢弃，触发器的报错因此只在事件日志开启时可见，用户看到的是泛泛的
`Fail to prove the goal …`。

【已定】改法：在现有的清理（取消看门狗，再取消任务组）之后，重新抛出那个任务的**所有非中断
的异常**，不只是 `ERROR`。理由：按 4.4，触发器自己的异常原样传播，常见的 bug 抛的是
`Option`、`Empty`、`Match`、`THM` 等。中断必须继续忽略：找到证明后取消其余任务、看门狗超时
取消任务，表现出来都是中断。

【自决】
- 判断是否中断用 `auto_sledgehammer` 里已有的 `Interrupt_Family.find_interrupt`（它的
  `normalise` 已经在用），不新写谓词。
- 一个任务已经把证明存进结果槽、而另一支抛了非中断异常时：仍然抛出。依据是那份代码自己的
  规矩「bug 不能被隐藏」。触发器的 bug 不会走到这种情况，因为 MePo 在任何 prover 运行之前
  就失败了。

【后果】`run_sledgehammer` 里只有每个 prover 的运行和预演被一个捕获一切非中断异常的处理器
包住；`check_expected_outcome` 和结果回调在它之外。所以改后 `auto_sledgehammer` 自己的结果
回调里的 bug 也会暴露出来，而不只是触发器的。

## 7. 报错能否到达用户

来源：一个 Opus agent 的只读静态分析（2026-11-11），未运行验证。【未核实】整节。

原文到达：交互式 `sledgehammer` 命令（事实筛选这一段外面只有捕获超时的处理器）；
Sledgehammer 面板；`sledgehammer learn_prover` / `relearn_prover`；ML 直接调用
`run_sledgehammer`；`Sledgehammer_Tactics`；`auto_sledgehammer` 的 `fast_mepo` 方法和改进模式
的 fastforce 分支（后者在并行的另一分支先找到证明时会丢掉这个错误）。`Par_List.map` 按原值
重新抛出 MePo 的异常。MePo 从不在后台学习线程里运行。

被吞掉：
- 【后果】`try` 命令和自动 Sledgehammer（`Tools/try.ML`）。这是发行版对这两个工具的既定
  做法，不为触发器破例。
- `auto_sledgehammer` 的 `raw_sledgehammer`：见 6.4，要改。

原先未确定、2026-11-10 发布之后查明的四项（本节其余内容仍是【未核实】的静态分析）：

- **Isa-REPL**：【实测，用了替代品】`sledgehammer` 命令内部抛出的 `ERROR` 能到达客户端。
  做法：在共享树上起一个 REPL 服务器，执行
  `lemma "rev (rev xs) = xs" sledgehammer [provers = no_such_prover]`，客户端收到
  `REPLFail: No such prover: no_such_prover`。静态分析担心的「fork 出的命令的报错不打印」在
  这条路上没有发生。替代之处：共享树里没有触发器，用的是 `run_sledgehammer` 里另一处同步抛出
  的 `ERROR`；触发器自己的报错没有在 Isa-REPL 下跑过，按「同一个线程、命令返回之前抛出」
  推断它走同一条路。
- **批量构建**：【实测】会话构建失败，文本完整：
  ```
  *** Sledgehammer fact trigger "broken": the candidate no_such_fact cannot be evaluated:
  *** Undefined fact: "no_such_fact" (line 1)
  *** At command "sledgehammer" (line 14 of "…/Trigger_Error_Probe.thy")
  ```
- **Mirabelle**：【实测，`sledgehammer` 动作】不中断运行，报错写进 `mirabelle.log`：
  `… goal.by … unknown (SH 0ms):  error: Sledgehammer fact trigger "broken": the candidate
  no_such_fact cannot be evaluated:` 加下一行原始报错。原因是 `Mirabelle.run_action_function`
  用一个捕获一切非中断异常的处理器包住每个动作。直接调用 MePo 的 `sledgehammer_filter` 动作
  没有跑（它需要一个 `proof_file` 参数），它被同一个处理器包着。
- **两个 TPTP 导出工具**：【只读源码，未运行】`atp_theory_export.ML` 和 `mash_export.ML` 调用
  `mepo_suggested_facts` 的地方外面没有异常处理器，报错原样传给调用它们的 ML 代码。

批量构建和 Mirabelle 的探针在 MLML 仓库的 `ai-artifacts/sh_trigger_error_probe/`（不提交）。

已知的第三方行为，只记录、不处理：
- AutoCorrode 的 `iq/Isar_Explore.thy` 把 MePo 的调用包在 `handle ERROR _ => []` 里。在那里
  4.4 的求值失败报错（它是 `ERROR`）被悄悄丢掉，而触发器自己抛的非 `ERROR` 异常会传播。
- Isa-REPL 的前提选择请求经 `relevant_facts` 到达 MePo，它把任何异常的文本回报给客户端
  （评审所述，【未核实】）。

## 8. 【后果】已知且接受的

1. 用户显式写 `sledgehammer [fact_filter = mash]` 时 MePo 不运行，触发器不触发。
   MaSh 里调用 MePo 的 `prover_dependencies_of` 只服务于 `learn_prover` / `relearn_prover`，
   处理的是被学习的旧定理，不是当前目标。
2. 用户写 `sledgehammer (foo bar)` 只给定事实时，MePo 不运行，触发器不触发。
3. 触发器若生成了候选池里已有的定理，它在 MePo 里多占一个名额（4.3 不与候选池去重）。
4. 候选比触发它的常量晚一轮被接受；越晚被接受名次越低，小名额的 slice 用不上。
5. 触发器把 `prop` 写错时没有任何提示，只表现为相关性变差或被错误去重（4.3）。

## 9. feature 的组织

【已定】
- feature 名 `sledgehammer_fact_trigger`；分支 `Isabelle2026/sledgehammer_fact_trigger`；
  feature repository `contrib/sledgehammer_fact_trigger`，GitHub 上是公开仓库
  `xqyww123/Sledgehammer_Fact_Trigger`，BSD-3-Clause；conda 包名
  `isabelle-sledgehammer-fact-trigger`。
- base 是 `Isabelle2026/fast_abbrev_printing`；base 标签 `Isabelle2026/fast_abbrev_printing/1`。
- 它通过把 light_locale 在 Isabelle2026 上的 base 改成它（SKILL isabelle-patch-feature 3.7）
  进入 `daily`，之后跟随这条链上各 feature 的升级。链变为 fast_abbrev_printing →
  sledgehammer_fact_trigger → light_locale → …。改 base 由 light_locale 的会话来做。

已完成（2026-11-11）：新分支已推到 `isabelle-patched`；feature repository 的登记提交
`ba08582` 已推送；MLML 里登记 submodule 的提交 `0d1d427e`（未推送）；已发消息告知
light_locale 的会话（`light locale old plan`），3.7 第 1 步的检查已通过。

事实：
- Isabelle2026 上这条链里没有任何 feature 改过 Sledgehammer 或 Try0 的文件，Isabelle2025-2 上
  也没有。所以本 feature 在源码上不依赖其它 feature。
- 补丁涉及六个文件：`HOL/Tools/Sledgehammer/` 下的 `sledgehammer_mepo.ML`、
  `sledgehammer_mash.ML`、`sledgehammer_fact.ML`、`sledgehammer_util.ML`、
  `sledgehammer_prover_tactic.ML`，以及 `HOL/Tools/try0_util.ML`。它们都在 HOL 会话里，每次
  改动后验证都要在 private tree 里重建 HOL heap（需作者下令）。
- 按 `sledgehammer_fact_trigger` 这个名字算，最长的补丁文件路径是 189 个字符，Windows 的
  限制是 198。新增被补丁的文件时要重算。
- 首次发布前还要补的文件：`README.md`、`tools/patched_files.txt`、
  `tools/signature_additions.txt`、`tools/required_sessions.txt`、`tools/release_build.sh`。

## 10. 测试

【自决】放在 feature repository 的测试会话里，用一个玩具触发器（`PQ`、`QR`、`P7` 一类）。

1. 触发器生成的候选出现在 MePo 的结果里，名字是给定的表达式，来源是 `From_Trigger`。
2. 目标里一开始就含触发常量时也能生成（第 0 轮之前的调用）。
3. 落选的候选不被求值（用一个求值必然失败的 `name` 配一个必然落选的 `prop`，不报错）。
4. 同一候选在多轮里重复产出，结果里只有一条；同一条事实经两条 OF 链得出，结果里只有一条。
5. 求值结果带着被内核换过下标的 schematic variable 的候选（如 `QR[OF PQf]` 得
   `P ?x1 ⟹ R (f ?x1)`），触发器只声明 `prop` 而不提前求值，照常被接受。
6. 两种报错各一例，逐字比对文案；触发器函数抛非 `ERROR` 的异常时原样传播。
   求值失败要测两例：名字不存在（抛 `ERROR`），和 OF 链对不上（抛 `THM`）。后一例逐字比对
   文案的第一行；「原始报错」部分只检查它含有 `OF: no unifiers` 和涉及的定理，因为其中的
   源码位置使逐字比对不稳定。
7. 没有注册触发器时，MePo 的输出与 stock tree 逐条相同（若干目标）。
8. 名额已满、`insert_special_facts` 截掉末尾时，结果里标为 `From_Trigger` 的恰好是仍在结果里
   的那些。
9. 候选含候选池里从未出现的常量、或只在别的类型实例上出现过的常量时，正常打分。
10. 注册触发器后，不含生成候选常量的候选池定理的分数与未注册时相同（频率表固定）。
11. 端到端：ATP、SMT、tactic prover 三条路径各自给出含嵌套 `[OF …]` 名字的证明并预演通过。
12. `try0` 对嵌套属性的事实给出可重放的文本（5 节第二处修法）。
13. `mesh_facts_with_mepo`：生成的事实不因另一个筛选器而降名次。
    `insert_generated_facts`：纯 MaSh 名单里含有它，位置正确。
    没有任何来源为 `From_Trigger` 的事实时：`mesh_facts_with_mepo` 的结果等于对按名次赋分
    后的 MePo 名单调用 `mesh_facts` 的结果，`insert_generated_facts` 原样返回输入。这条在
    同一棵树里就能测。它测的是这两个函数本身，**守不住**改造后的 `relevant_facts` 里的分支
    选择（rev 3 原文说能守住，说过头了）。`relevant_facts` 另有一条不依赖 MaSh 状态的检查：
    `fact_filter = mepo` 时结果等于 MePo 的名单并含有生成的事实。同时产出三份名单的分支需要
    MaSh 已有学习状态，测试会话不测（依赖用户目录里的状态会使测试不稳定）。
14. 性能：有无触发器两种情况下 MePo 的耗时对比（基线见 2.6）。
15. `auto_sledgehammer`（在它自己的仓库里测）：触发器抛 `ERROR` 和抛 `Option` 时，方法都以
    该异常的文本失败，而不是泛泛的失败信息；正常找到证明、其余任务被取消时不受影响。

实现时与上面清单不同的地方（2026-11-10）：
- 第 7 项不在测试会话里：一棵树里没有原版 MePo 可比。它在草稿环境里测过（13.5），测试会话
  只保留第 10 项。
- 第 9 项只测了「常量在候选池里从未出现」；「只在别的类型实例上出现过」没有找到稳定的例子，
  没有测。
- 测试会话里 `PQ`、`QR`、`P7`、`PQf` 标了 `no_atp`，使它们不进候选池，`R 7` 只能靠触发器
  生成的事实证出。另加一条在候选池里的 `QZ: Q x ⟹ Z 0 ⟹ R x`，用来让 `Q` 在某一轮之后才变得
  相关。
- 「必然落选」的候选不能随手写：候选的 theory 伪常量从一开始就相关，所以只含少数罕见常量的
  命题（如 `Z 0`）分数反而很高，会被接受。测试里用的是含若干常见而无关的常量的命题
  （`wf (trancl Id)`）。

## 11. 不做的

- 让 MaSh 推荐或给生成的事实打分。
- 用 MaSh 的结果喂 MePo 的初始相关常量集合。
- `fact_filter = mash` 时为驱动触发器而单独跑一遍 MePo。
- 把定理的求值推迟到某个 prover 真正用到它时。
- 让触发器自带分数。
- 检查求值结果的命题与 `prop` 是否一致。
- 修 Semantic_Embedding 里已废弃的事实筛选器；移植「自定义事实筛选器」的注册机制。

## 12. 评审记录

rev 1 的评审（2026-11-11）：7 条不重复的 concern，全部成立或部分成立，没有被判为吹毛求疵的。

| concern | 处理 |
|---|---|
| 6.4 的提案只重新抛出 `ERROR`，仍吞掉常见的触发器 bug | 作者定：重新抛出所有非中断的异常（6.4） |
| 把候选计入中途变化的共享频率表，破坏分数缓存 | 作者交实现者自决：固定表加候选自己的出现次数（4.3） |
| 用 `aconv` 判断命题一致，逼触发器提前求值；两条链得出的同一事实不去重（两个评审各提一次） | 作者定：取消一致性检查；去重键用 `normalize_vars`（4.3） |
| 另外返回的生成事实列表，在 `insert_special_facts` 截断后可能与结果不一致（两个评审各提一次） | 自决：来源标记带到最终结果（6.1） |
| Semantic_Embedding 的筛选器会把生成的事实降名次（辩护中发现） | 作者定：那份代码已废弃，不管；合并做成通用接口（3.2、4.5） |
| MePo 行号有误；调用者数量写错 | 改为按函数名引用；调用者清单统一（6.1） |
| 4.1 里「目标常量永远不会作为新增常量出现」不准确 | 改写理由，补一条准则（4.1） |
| 第 9 节没说怎样进入 `daily` | 作者定（9） |

rev 2 的评审（2026-11-11）：6 条 concern，其中三条是同一件事，一条被判为吹毛求疵。rev 2
新加的设计没有被找出具体缺陷。

| concern | 处理 |
|---|---|
| 「求值失败」没说包括哪些异常；OF 链对不上抛的是 `THM`（三个评审各提一次） | 自决：任何非中断的异常；附上证明上下文再取文本（4.4） |
| `hyp_ts`、`concl_t` 的形状取决于调用者，注释没说 | 扩充 3.1 的说明，加一条准则（4.1）；不做统一 |
| `relevant_facts` 改造后怎样保持并行没说；3.2 的「走同一条路径」在 `fact_filter = mash` 时不成立 | 写明做法（6.2）；限定那句话（3.2）；加一条测试 |
| 没有列出 `relevant_facts` 的调用者 | 驳回：它的类型不变，调用者都不用改 |

代码评审（2026-11-10，对未提交的实现）：7 条 concern，一条被判为吹毛求疵，结论「修改后接受」。
MePo 的核心部分被判定忠实于 3–6 节，两段报错文案逐字一致，不注册触发器时与原版相同。

| concern | 处理 |
|---|---|
| 带引号的事实名经 tactic prover 后打印出的证明无法解析（退步） | 作者定：5 节第 3 处修法 |
| 「没有常量的候选直接丢弃」写了两遍 | 自决：原有的 `pair_consts_fact` 改成 `pair_consts`，接受命题和条目，两边共用 |
| `relevant_facts` 给结果打了标记却仍按列表位置取用，还有一个到不了的 `raise Fail` | 自决：按构造子拆成两个 option，恢复原版覆盖所有情况的 `case` |
| 几条测试在生成的事实丢失时也通过；第 10 项的检查查不出它声称要查的 bug | 自决：加存在性断言；第 10 项的候选改为含 2000 个目标常量的出现 |
| 端到端检查靠消息里的 `" ms)"` 判断预演成功 | 自决：改用 `run_sledgehammer` 返回的结构化结果 |
| 没有测试直接调用 `relevant_facts` | 自决：加 `fact_filter = mepo` 的确定性检查（10 节第 13 项） |
| `fact_thresholds` 为负时触发器不运行 | 驳回：那是原版完全跳过筛选的路径，且用户写不出负的阈值 |

代码评审第二轮（2026-11-10，发布第 1 版之后补做，只评第一轮之后的差异）：2 条 concern，都成立，
结论「修改后接受，需要发布第 2 版」。第一轮的修改里，`pair_consts` 和 `relevant_facts` 被逐个
模式对照原版确认无误（含同时产出三份名单的分支），加引号的部分也无误。

| concern | 处理 |
|---|---|
| `string_of_xref'` 把每个属性各打一组方括号，匿名事实少一层方括号，都解析不了 | 作者定：5 节第 4 处修法，发布第 2 版 |
| README 对触发器输入的描述与代码不完全一致（名字不只有常量、漏了去重和纯函数两条、调用时机） | 作者批准了逐句的改法；名额用完后不再调用这处偏离，作者接受（4.1） |

被否决的做法，别再提：
- 由 MePo 保证 `hyp_ts`、`concl_t` 的统一形状，或加运行时检查：管不了第三方调用者，也补不回
  丢失的类型。
- 让每个筛选器都返回带来源的名单，或让 `mesh_facts_with_mepo` 自己调度并行：前者让非 MePo
  的筛选器白白给每条事实打标记，还放弃了「只有 MePo 的参数能带 `From_Trigger`」这条由类型
  保证的性质；后者把调度塞进合并函数。
- 把 `auto_sledgehammer` 的 `run_mepo_and_render` 改用 `strip_subgoal`：会改变 `fast_mepo` 的
  选择和缓存，不属于本计划。
- 在 MePo 里把触发器的异常包成 `ERROR`：与「原样传播」相抵。
- 给 `pconst_freq` 加缺省值和下限 1：改动原版函数，且不计候选自己的出现次数。
- 把带属性的事实一律放进 Try0 的 using 类。

## 13. 实施交接（2026-11-11，设计会话压缩前写下）

### 13.1 现状

- 设计完成，两轮评审完成。**作者已下令：压缩之后开始实现。**
- feature repository `contrib/sledgehammer_fact_trigger`（`main`）：登记提交 `ba08582` 已推送。
  本文件未跟踪、未提交；要不要提交、何时提交，等作者定（新增文件须逐个经作者批准）。
- private tree `contrib/sledgehammer_fact_trigger/worktrees/Isabelle2026-sledgehammer_fact_trigger`
  在分支 `Isabelle2026/sledgehammer_fact_trigger` 上，已推送并设了上游，目前与
  `Isabelle2026/fast_abbrev_printing/1`（`b62eb9f`）相同，没有自己的提交。stock tree 在同一提交。
- MLML 里登记 submodule 的提交 `0d1d427e` 已提交、**未推送**（推送没有请示过）。
- light_locale 改 base：已发消息给会话 `light locale old plan`，由它在提交完自己当前的工作后
  按 SKILL 3.7 做；尚无回音。本 feature 不动 `contrib/light_locale` 的任何东西
  （那里有别的会话未提交的工作）。

### 13.2 需要作者下令的事

- 每一次 `isabelle build`（含 private tree 里重建 HOL heap、跑测试会话）。目前**没有**任何
  长期构建授权。
- 每一次 commit 和 push（private tree、feature repository、MLML、`contrib/auto_sledgehammer`）。
- 提交里的每个新增文件。

### 13.3 实现的顺序（【自决】，可调整）

1. 5 节的两处修法（`sledgehammer_util.ML`、`sledgehammer_prover_tactic.ML`、`try0_util.ML`）：
   与触发器无关，可独立验证。
2. `sledgehammer_fact.ML` 导出 `normalize_vars`。
3. `sledgehammer_mepo.ML`：3.1、3.2 的接口和 6.1。
4. `sledgehammer_mash.ML`：6.2。
5. feature repository 里的测试会话（10 节），以及首次发布前要补的文件（9 节末）。
6. `contrib/auto_sledgehammer` 的 6.4：在它自己的仓库里改和测，与本 feature 的补丁分开。

注意：
- 只在 private tree 里改，不改共享树 `contrib/Isabelle2026`，不改 stock tree。
- 运行 private tree 用它自己的 `bin/isabelle`，且 shell 里 `env | grep ^ISABELLE_` 须为空。
- Isa-REPL 和 isabelle-mcp 跑的是共享树，读不到 private tree 的改动；本 feature 的源码只能
  靠 private tree 里的构建来测。共享树上只能做「不含本 feature」的探针。
- 先加载 SKILL isabelle-patch-feature、isabelle-ML、isabelle-ml-style。

### 13.4 已有的探针和数据，不要重做

MLML 仓库的 `ai-artifacts/sh_name_probe/`（未提交）：
- `SH_Name_Probe.thy`：嵌套 `[OF …]` 名字走 ATP、SMT、tactic prover 三条路径（5 节的表）。
- `SH_Name_Probe2.thy`：用 `Parse.thm` 解析名字后交给 Try0 的 using 类和 direct 类
  （5 节两处修法的依据）。其中的 `xref_of_name` 可作第一处修法的起点。
- `mepo_probe.ML`、`MePo_Rounds.thy`：加了每轮计数的 MePo 副本和 2.6 的测量。

7 节的静态分析和两轮评审的明细都只在设计会话的记录里，结论已写进本文件。

### 13.6 发布之后的状态（2026-11-10，本地时间；以本小节为准）

**已发布**：`isabelle-sledgehammer-fact-trigger 2026.0.1`（build `Isabelle2026_0`）在 conda 频道上。
发布标签 `Isabelle2026/sledgehammer_fact_trigger/1`：private tree 在 `ffe3a04`，feature repository
在 `f938513`。试运行 `42965742154`，正式发布 `42967653920`（补丁工具仓库
`xqyww123/isabelle_patch_control` 的 `release-features.yml`），都全绿；三个平台
（linux-64、linux-aarch64、win-64）上都重建了 HOL 并通过测试会话，含 e、cvc5、metis 的端到端
检查。

private tree 的提交：`0ce3db4`（实现）、`5c54157`（`string_of_xref'`）、`ffe3a04`（合并
`Isabelle2026/fast_abbrev_printing/2`，没有文件变化）。base 标签是
`Isabelle2026/fast_abbrev_printing/2`；包依赖 `isabelle ==2026 0`、
`isabelle-fast-abbrev-printing ==2026.0.2`、`isabelle-patch-control >=1.0,<2`。

别的仓库里为这次发布做的提交：`contrib/auto_sledgehammer` 的 `2ccead2`（6.4，已随
auto-sledgehammer 0.3.1 发布）；补丁工具仓库的 `84e1d60`（发布流程的 feature 表加一行）；
`isabelle-packaging-ci` 的 `5755e7a`（`ROLLOUT_STATUS.md`）；MLML 的 `0d1d427e`、`07a2c41a`
（登记和更新 submodule 指针；发布后的 `f938513` 还没有在 MLML 里更新）。

发布之后验证的：
- fast_abbrev_printing 的发布构建脚本在本 feature 的 private tree 上通过（`Pure`、`HOL`、
  `HOL-Algebra`、它的四个测试会话，含与金标准逐字节比对的两个）。本 feature 不改变打印结果。
- 7 节原先未确定的四项。

建在本 feature 之上的 feature：`light_locale`、`default_fact_qualifiers`（各自的 `.gitmodules`）。
它们各自合并这次发布、再各自发布之后，本 feature 才进入 `daily`；在那之前共享树
`contrib/Isabelle2026` 不含本 feature。两个会话都已通知。

评审：代码评审第一轮见 12 节。第一轮里由实现者自决的修改当时没有按流程送回再评，这是疏漏；
第二轮评审在发布之后补做，只评第一轮之后的差异（结果另记）。

仍未做：`relevant_facts` 同时产出三份名单的分支没有被任何测试跑到；10 节第 10 项的检查没有
用故意写错的实现验证过；concept 一侧的触发器还没有人写（本计划范围之外）。

### 13.5 实现的状态（2026-11-10，发布之前写下；已被 13.6 取代）

13.3 的六步都已写完，**全部未提交，private tree 里还没有构建过**。

- private tree：六个文件已改（+248 / −69）。
- feature repository：新增 `tests/ROOT`、`tests/Sledgehammer_Fact_Trigger_Test.thy`、
  `tools/patched_files.txt`、`tools/signature_additions.txt`、`tools/required_sessions.txt`、
  `tools/release_build.sh`，都未跟踪。`README.md` 未写，是用户可见文案，须拟稿经作者批准。
- `contrib/auto_sledgehammer`：`library/sledgehammer_solver.ML` 的 `raw_sledgehammer` 已改。

没有构建时的验证办法（可重复使用）：在共享树的 HOL 会话上开一个草稿 theory，用 `ML_file` 按
`try0_util`、`sledgehammer_util`、`sledgehammer_fact`、`sledgehammer_mepo`、`sledgehammer_mash`、
`sledgehammer_prover_tactic` 的顺序重新载入 private tree 的文件，之后的 ML 里这些结构就是新的，
可以直接调用。限制：`sledgehammer` 命令和已注册的 Try0 方法仍绑着 heap 里的旧代码，所以端到端
的测试做不了。草稿文件在 MLML 仓库的 `ai-artifacts/sh_trigger_typecheck/`（不提交）：
`SH_Trigger_Typecheck.thy` 是逐项探针，`SH_Test_Dry_Run.thy` 是测试会话的 theory 加上那几行
`ML_file`、去掉端到端一段。

更正：下面说第 10 项验证过，说过头了。当时那条检查只能说明「注册一个被拒绝的候选不打乱
候选池的选择」，查不出「把候选计入共享频率表」这个 bug。代码评审后候选改成含 2000 个目标
常量出现的命题；它是否真能查出该 bug 没有用故意写错的实现验证过。防住这个 bug 的是结构：
频率表是不可变的值，候选的表是它的一份持久化更新。

【实测】这样验证过的：六个文件通过类型检查；10 节的第 1–6、8–10、13 项；第 7 项在五个目标上
与同一 heap 里的原版 MePo 逐条相同；第 12 项；第 14 项（MePo 单独计时，1024 名额：不注册
触发器 0.37–0.44 s，注册一个不产出的触发器 0.38–0.43 s，每轮 50 条新候选 0.49 s）；
`relevant_facts` 在 `fact_filter` 为缺省、`mepo`、`mesh` 时结果里有生成的事实，`mash` 时没有。
`auto_sledgehammer`：配一个不存在的 prover 时方法报 `No such prover: …`，正常目标照常证出。

还没验证的：第 11 项（端到端）；`relevant_facts` 同时产出三份名单的分支（需要 MaSh 已有学习
状态）；7 节里未确定的几项。

构建的位置：private tree 的用户目录是 `~/.isabelle/Isabelle2026-sledgehammer_fact_trigger`，
heap 在它的 `heaps/` 下，与本机其它 Isabelle 的用户目录分开（`isabelle getenv` 实测）。
