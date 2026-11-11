# 第 3 个发布的维修方案

状态：rev 3，2026-11-11，第三轮评审「修改后接受，不需要再评」；它要求的局部修改已并入本稿和
草稿并重跑通过。**待作者批准**（一处行为需作者定：3.1 的顺序；三个新名字）。rev 1 和 rev 2 各被一轮对抗评审判为
「不通过」，共同原因是方案里对代码的说法没有逐条核实。rev 3 换了做法：先在草稿环境里把修法
实际写出来、跑通，再据实写本稿。评审记录见第 7 节。作者的要求：「能修的都修一下。但维修方案
一定要评审」。

private tree 没有为本方案改动（3.1 说明的两行除外）。草稿实现不在 private tree 里。

标记：【实测】= 在草稿环境里跑过；【读码】= 只读了源码；【已定】= 作者已决定。
没有标记的修法描述，对应的代码都在草稿里并且跑过。

源码路径相对于 Isabelle2026 的 `src/`。private tree 现在在 `10d0506`（第 2 个发布）。

## 1. 这一类问题是什么

把一个事实引用写成文本时，写出了 Isar 解析不了、或者解析回来不是同一个事实的东西。Isar 的
语法（`Parse.thm`，`Pure/Isar/parse.ML`）是：

```
[[attrs]]                         匿名事实
‹prop›  [attrs]?                  字面事实
name  (selection)?  [attrs]?      有名字的事实；attrs 是一组方括号、逗号分隔
```

第 1、第 2 个发布之后的修改都是「被指出一处、修一处」。作者指出这样每个版本只带一点内容太
零碎，所以第 3 个发布之前把同类问题收齐，一次修完。

## 2. 草稿实现

位置：MLML 仓库的 `ai-artifacts/sh_release3_draft/`（不提交）。

- `try0_util.ML`、`sledgehammer_util.ML`、`sledgehammer_fact.ML`、`metis_tactic.ML`：从第 2 个
  发布复制后改成本方案的样子。`draft.diff` 是这四个文件相对第 2 个发布的差异（265 行，12 个
  hunk），**它就是打算放进 private tree 的修改**，只有一处例外：草稿的 `metis_tactic.ML` 把
  `lambda_def` 写成了 `Metis.lambda_def`，因为这个事实在 `HOL.Metis` 之外被隐藏；放进 private
  tree 时不带这一处。
- `Release3_Draft.thy`：在共享树的 HOL 会话上用 `ML_file` 载入这些文件，然后逐项检查。
  全部检查通过【实测】。

草稿环境的限制：`sledgehammer` 命令和 Try0 已注册的方法仍绑着 heap 里的旧代码，所以经过
Sledgehammer 的端到端路径没有在草稿里跑。`metis` 方法是例外：载入 `metis_tactic.ML` 会在
草稿 theory 里重新注册它，所以真实的 `by (metis …)` 调用跑的是新代码。

两个前提事实（rev 1 写错过）：
- `Try0_Util` 在所有 HOL theory 里都可见：`HOL/HOL.thy` 导入 `Try0`。反过来不成立，
  `Try0_Util` 看不到 `ATP_Util` 和 `Sledgehammer_Util`。
- `Facts.interval` 和 `Parse.attrib` 没有导出，Pure 之外不能调用。

## 3. 要修的

### 3.1 M1 Sledgehammer 给事实列表里的事实起名

位置：`HOL/Tools/Sledgehammer/sledgehammer_fact.ML` 的 `fact_of_ref`。它只在
`sledgehammer (foo[of x, OF bar] baz)` 这种**不带 `add:`** 的写法下运行。它给每条定理起一个
名字；名字之后被 tactic prover 解析，被 ATP 和 SMT 路径原样写进给用户的证明文本。

第 2 个发布里它自己拼字符串，有四处错：

| 错 | 输入 | 第 2 个发布起的名字 |
|---|---|---|
| 每个属性一组方括号 | `PQ[of 7, OF P7]` | `PQ["of" 7]["OF" P7]`，解析不了 |
| 匿名事实没有属性 | `[[]]` | `[]`，解析不了 |
| 「到末尾」的选择不在最后 | 4 条定理的 `four(3-, 1)` | 选出的是第 3、4、1 条，名字却是 `four(3)`、`four(4)`、`four(5)`；`four(5)` 不存在 |
| 字面事实里的空白被压缩 | `‹length ''a  b'' = 4›` | 名字里是 `''a b''`，是另一个命题 |

第三处的原因：`explode_interval max (Facts.From i) = i upto i + max - 1`，传给它的 `max` 是
选择**之后**的条数。

修法：不再自己拼字符串。对每条定理构造一个只指向它自己的事实引用，交给
`Try0_Util.string_of_xref'` 打印（第 2 个发布里它已是 `Parse.thm` 的逐分支逆运算）。

- 有名字、没有选择：用 Pure 已导出的 `Facts.selections (name, ths)`。它对只有一条定理的事实给
  名字本身，对 n 条给 `name(1)` … `name(n)`。匿名事实（名字为空）总是一条，落在这一支。
- 有名字、有选择：引用是 `name(i)`，`i` 由 M3 的函数按**整条事实**的长度展开；整条事实用
  `Proof_Context.get_fact ctxt (Facts.Named (name_pos, NONE))` 取得。
- 字面事实：引用就是原引用。

删除 `explode_interval`。`make_name`、`needs_quoting` 保留（`all_facts` 在用）。
`fact_of_ref` 的 `keywords` 参数变成不使用但保留：签名关卡不允许改已有的签名条目。

【实测】草稿起的名字，每个都经 `thms_of_name` 求值回对应的那条定理：

| 输入 | 名字 |
|---|---|
| `four` | `four(1)`, `four(2)`, `four(3)`, `four(4)` |
| `four(3-, 1)` | `four(3)`, `four(4)`, `four(1)` |
| `imps[of 7]`（两条定理） | `imps(1)["of" 7]`, `imps(2)["of" 7]` |
| `imps(2-, 1)[of 7]` | `imps(2)["of" 7]`, `imps(1)["of" 7]` |
| `PQ[of 7, OF P7]` | `PQ["of" 7, "OF" P7]` |
| `[[simp]]`、`[[]]` | `[["simp"]]`、`[[]]` |
| 证明内的 `‹length ''a  b'' = 4›[symmetric]` | `‹length ''a  b'' = 4›["symmetric"]`，两个空格保留，不含控制字符 |

上表里多条定理的名字是按这个顺序返回的，草稿的检查比对了确切的有序列表。

用户可见的后果：
- **顺序【待作者定】**：一条引用求值出多条定理时（如 `four`、`four(3-, 1)`），草稿按书写顺序
  把它们交给 prover。第 2 个发布（与原版相同）是**倒序**：`four` 交出去的是 `four(4)` …
  `four(1)`。原版的倒序是它用 `fold` 加 `cons` 建表的副作用，不是有意的设计。区别只在截断时
  显现：`max_facts` 很小，或 tactic prover 只取 1、2、4、8 条的那些尝试，留下的是前几条还是
  后几条。例：`sledgehammer [max_facts = 2] (four)`，第 2 个发布给 prover 的是 `four(4)`、
  `four(3)`，草稿给的是 `four(1)`、`four(2)`。给用户的证明文本不受影响（那里按名字排序）。
  评审建议保留书写顺序。若作者要保持原版的倒序，代码上是在结果后面加一个 `rev`。
- 属性名带引号（第 2 个发布已如此）。
- 字面事实按原文打印：字符串常量里的空白保留；写成多行的字面事实，名字也是多行。
- 名字是单个数字或符号标识符时不再加引号：`"1"` 变成 `1`。两种写法解析回同一个事实
  【读码，来自评审】。原因是「要不要加引号」由 `Thy_Header.print_name'` 判断，取代了
  `needs_quoting`。

**private tree 里现有的未提交修改**（上表前两处的两行）被本项取代，动手时一并改写。

### 3.2 M2 Try0 打印字面事实

位置：`HOL/Tools/try0_util.ML` 的 `string_of_xref'` 的字面事实分支。`Parse.thm` 读一个
cartouche 得到的字符串带着 YXML 标记，第 2 个发布把它原样打印，文本里有控制字符。

修法：

```ML
cartouche (Input.string_of (Syntax.read_input literal))
```

`Syntax.read_input` 是 `Token.inner_syntax_of` 所用的 `Syntax.implode_input` 的逆运算；
`Input.string_of` 按定义去掉 `Symbol_Pos.implode` 填的 DEL。`Proof_Context.retrieve` 读字面事实
用的是同一对函数【读码，来自第三轮评审】。

经过：第二轮评审给的写法 `cartouche (clean_output literal)` 在草稿里跑出来留着 `\127`（DEL，
`Symbol_Pos.implode` 为保持位置填的占位符）【实测】；草稿先改成 `clean_output` 加原有的
`explode0 |> implode`，能用，但那是拿一个 PIDE 消息清理函数当解码器、靠副作用去掉 DEL。
第三轮评审指出 Pure 有现成的逆运算，现在用的是它【实测：字面事实的检查通过】。

它是字面事实唯一的打印处，Try0 和（经 M1）Sledgehammer 共用。M1、M4 依赖它。

### 3.3 M3 按整条事实的长度展开选择

`Try0_Util` 里新增一个纯函数：

```ML
(*the indexes that a selection denotes in a fact of n theorems, in the order of the selection*)
val indexes_of_selection : int -> Facts.interval list -> int list
```

`FromTo (i, j)` 给 `i..j`，`From i` 给 `i..n`，`Single i` 给 `[i]`。它是没有导出的
`Facts.interval` 的对应物，M1 和 M5 共用。【实测】`indexes_of_selection 4` 对 `(3-, 1)` 给
`[3, 4, 1]`。

### 3.4 M4 归纳规则实例化的名字

位置：`sledgehammer_fact.ML` 的 `instantiate_induct_rule`。`induction_rules = instantiate`
（非默认）时，它在原名字后面拼一段 `[where P = "…"]`。原名字是 `nat.induct` 时结果合法；
原名字自己已带属性时（只可能来自 `fact_of_ref`，即用户在事实列表里写了带属性的归纳规则）
得到两组方括号，解析不了。

走到这里的名字有三种来源：`all_facts` 起的普通名字；`fact_of_ref` 起的名字；
`HOL/TPTP/mash_eval.ML` 传进来的 MaSh 编码名字（不是 Isar 事实引用）【读码，来自评审】。
触发器给出的名字走不到这里（归纳规则实例化在 MePo 之前）。

【已定】只在原名字已带属性时才重新打印；其余情况逐字节保持今天的文本。

修法：`sledgehammer_util.ML` 新增

```ML
(*name is the text of a fact reference, attribs the text of attributes without brackets; a name
  without attributes keeps its text*)
val add_attribs_to_name : Proof.context -> string -> string -> string
```

实现：先算出今天的结果 `appended = name ^ "[" ^ attribs ^ "]"`。然后在**一个** `\<^try>` 里：
用 `xref_of_name` 解析 `name`；没有属性就返回 `appended`；有属性就用 `Parse.attribs` 解析
`"[" ^ attribs ^ "]"`。两次解析共用一个不进签名的辅助函数 `parse_name parser ctxt text`
（分词，要求读到 `Parse.eof`），`xref_of_name` 改为 `parse_name Parse.thm`。返回
`Try0_Util.string_of_xref' ctxt (xref, srcs @ srcs')`。任何异常都返回 `appended`。

为什么必须不抛异常：名字是惰性的（`fn () => …`），在 `fact_of_lazy_fact` 里才被求值，那里在
`instantiate_if_induct_rule` 的 `try (Timeout.apply …)` 之外，异常会一路传出去。

【实测】

| 原名字 | 结果 |
|---|---|
| `nat.induct` | `nat.induct[where P = "x"]`（不变） |
| `four(2)`、`"1.IH"(2)`、`‹P 7›` | 各自后面接 `[where P = "x"]`（不变） |
| `nat.induct[case_names Z S]` | `nat.induct["case_names" Z S, "where" P = "x"]` |
| 属性文本里有多余的引号（解析失败） | 退回今天的文本，不抛异常 |

合并后的名字 `nat.induct["case_names" Z S, "where" P = "λn. n + 0 = n"]` 与手写的
`nat.induct[where P = "λn. n + 0 = n"]` 求值出同一条定理。

代价：两种情况下属性名一个带引号、一个不带，风格不统一。

### 3.5 M5 Metis 给方法参数里的定理起名

位置：`HOL/Tools/Metis/metis_tactic.ML`。

第 2 个发布（与原版相同）的做法：`parse_multi_thm` 把一个参数被消耗的 token 逐个
`Token.unparse`、用空格连起来、再在**字符层面**去掉 `[]():,` 两侧的空格，得到一个字符串；
参数求值出多条定理时，`th_name_multi_thm` 在这个字符串后面接 `(k)`。三处错：

| 错 | 输入 | 结果 |
|---|---|---|
| 选择接在属性后面 | `imps[of 7]`（两条定理） | `imps[of 7](1)` |
| 已有选择时再接一个 | `four(3-, 1)` | `four(3-,1)(1)` 一类 |
| 去空格进入 token 内部 | `PQ[of "length ''a, b''"]` | 引号里的 `''a, b''` 变成 `''a,b''`，是另一个项 |

这个名字在每次 `metis` 调用时都会被「Unused theorems」警告用到（`metis_verbose` 默认开启），
不只是 `metis_instantiate` 开启时。所以起名**绝不能抛异常**。

修法：
- 方法的解析器直接用 `ATP_Util.scan_and_trace_multi_thm`，把每个参数的 `(定理, token)` 原样
  传下去；删除 `parse_multi_thm`。
- 新函数（也是测试入口，见 5.1）：

  ```ML
  val th_name_of_multi_thms : Proof.context -> (thm list * Token.T list) list -> thm ->
    string option
  ```

  它是 metis 实际安装的起名函数，取代 `th_name_multi_thm`。名字在被请求时才算。
- 参数只有一条定理：名字是它全部 token 的文本。
- 参数有多条定理，第 k 条的名字是

  ```
  <名字 token> ^ "(" ^ i ^ ")" ^ <属性 token 的文本>
  ```

  做法：第一个 token 是名字；对其余 token 运行
  `Scan.finite Token.stopper (Scan.option Parse.thm_sel)` 得到可选的选择和属性 token；
  `i` 是 `indexes_of_selection` 给出的第 k 个序号（没有选择时就是 k）；整条事实的长度取自
  名字 token 自己带的值 `Token.Fact (_, whole)`。
- token 的文本：逐个 `Token.unparse`；相邻两个 token 之间放一个空格，除非其中一个恰好是
  `[ ] ( ) : ,` 之一。空格的取舍只发生在 token 之间。
- 整个计算在一个 `\<^try>` 里；任何异常（包括名字 token 没有 `Token.Fact` 值）退回今天的文本。

两条不能违反的规则：
- 必须用 `Scan.finite Token.stopper`。裸的 `Scan.option Parse.thm_sel` 在只有一个名字的参数
  上（最常见的输入）会抛 `Scan.MORE`【读码，来自评审；草稿的测试代码里也踩到了同一个异常】。
- 只能用 `Token.unparse`，不能用 `Token.pretty_src` 或 `string_of_xref'`：方法真正运行时参数
  token 带着已求值的值，后者会把一个事实参数印成定理本身。

【实测】token 取自真实的方法调用路径（`Method.read_closure_input`），测试先断言名字 token 确实
带着 `Token.Fact` 值。每个名字都求值回对应的定理：

| 输入 | 名字 |
|---|---|
| `four` | `four(1)` … `four(4)` |
| `four(3-, 1)` | `four(3)`, `four(4)`, `four(1)` |
| `imps[of 7]` | `imps(1)[of 7]`, `imps(2)[of 7]` |
| `imps(2-, 1)[of 7, simplified]` | `imps(2)[of 7,simplified]`, `imps(1)[of 7,simplified]` |
| `PQ[of "length ''a  b''"]` | 原样，两个空格保留 |
| `imps[of "length ''a, b''"]` | `imps(1)[of "length ''a, b''"]`, `imps(2)[…]`，逗号后的空格保留 |

真实调用 `by (metis imps P7 four(3-, 1))`（开着 `metis_instantiate`）给出：

```
Metis: Unused theorems: "four(3)", "four(4)", "four(1)"
Found variable instantiations, try this: by (metis P7 imps(1)[of "7"] imps(2)[of "7"])
```

只改 `metis_tactic.ML`。

### 3.6 M6 Metis 给 `using` 进来的事实起名

位置：同一个起名函数里，定理不属于任何方法参数时的分支。第 2 个发布（与原版相同）用定理的
名字提示配 `Global_Theory.print_thm_name`，四种情况靠不住：

| 情况 | 例子 | 第 2 个发布印出 |
|---|---|---|
| 没有提示 | 属性产生的 `QR[OF a]`；一条定理的实例 `imps(1)[of 7]` | `??.unknown` |
| 局部事实 | `have a: …` | `??.local.a` |
| 提示指向别的定理 | 同一个名字被重新绑定、而旧定理还在手里（如 `calculation` 里） | 那个名字，查回来是另一条【读码，来自评审，未跑】 |
| 被局部事实遮蔽 | 全局 `PQ`，证明里又 `note PQ = …` | `PQ`，实际指向局部那条 |

【已定】用一条规则：把提示里的名字查回来，恰好是这条定理才用，否则不起名。

修法：取提示 `(name, i)`；用 `Proof_Context.markup_extern_fact` 得到在当前上下文里该怎么写这个
名字；构造引用（`i = 0` 时不带选择，否则 `(i)`）；`Proof_Context.get_fact` 查回来恰好是
`[th']` 且 `Thm.eq_thm (th, th')` 时，用 `Try0_Util.string_of_xref'` 打印这个引用；其它情况和
任何异常都返回 `NONE`。

【实测】

| 定理 | 名字 |
|---|---|
| 局部事实 `a` | `a` |
| `QR[OF a]` | 不起名 |
| `imps(1)[of 7]`（实例，没有提示） | 不起名 |
| `QR`，人为把提示设成 `P7` 的名字 | 不起名（查回来不是它） |
| `four(2)`、`P7` | `four(2)`、`P7` |
| 被局部 `PQ` 遮蔽的全局 `PQ` | `Release3_Draft.PQ`（长名字，查回来确是它） |

最后一行比方案原先预计的好：`markup_extern_fact` 会给出不被遮蔽的写法，所以被遮蔽的事实不是
被丢掉，而是用长名字。

真实调用 `using a P7[THEN PQ, THEN QR] by (metis P7 imps(2-, 1))` 给出
`try this: using a[of "7"] by (metis P7 imps(1)[of "7"])`。

用户可见的后果：
- 查不回来的 `using` 事实不出现在建议文本里，建议可能因此不完整。今天这些情况印出的是
  解析不了或指错定理的名字。
- 「Unused theorems」警告里，局部事实从 `??.local.a` 变成 `a`【读码，来自评审】。
- 代价：每起一个这样的名字多一次事实查找。

`NONE` 对每个使用者都安全【读码，来自评审】：`metis_axiom_to_thm` 用 `mapPartial`；警告有
自己的 `the_default`。

## 4. 不在范围内的

### 4.1 M7 `auto`、`fastforce`、`force` 拿到 direct 类事实 【已定：不纳入】

作者 2026-11-11：「走 using 必须依旧走 using，不能擅自改动！这个行为变化会很大的！」

记录事实，供以后单独立项：Sledgehammer 的 tactic prover 把全局事实放进 direct 类；Try0 对这
三个方法把 direct 类的事实写在方法名后面（`auto foo`），它们不接受，报
`Bad arguments for method "auto"`，这个 prover 放弃【实测，仅 `auto`；另两个是读码】。所以这
三个方法作为 Sledgehammer 的 prover，在含全局事实的尝试上必然失败，触发器生成的全局事实对
它们也无效。今天走 `using` 的不受这个问题影响。

若将来改（把 `Try0_Util.full_attrs` 的 `allows_directs` 改为 `false`，让这一格也走 `using`），
影响的是所有默认配置下的 Sledgehammer 调用，不只是用了触发器的【读码，来自评审】：
- `auto` 的 16 条事实那一次尝试、`fastforce` 的 16 和 32 条那两次，在含全局事实时从立刻放弃
  变成真的去跑；
- 成功后还要做最小化，在同一个线程里把方法再跑多次；
- 每次成功立刻计入 `max_proofs`（默认 4）；tactic prover 排在 ATP 和 SMT 之前，后面的尝试
  可能不再启动，用户看到的证明会变；
- MaSh 开着学习时，这些证明用到的事实进入持久状态。

### 4.2 不修的

- **N1 多条定理的事实加会改变上下文的属性。** `foo[simplified, simp]` 的第 2 条是在第 1 条已
  进 simpset 的上下文里得到的；名字 `foo(2)[…]` 在原上下文里求值，可能不同。Isar 没有「先
  施加属性再选择」的写法。
- **N2 `relevant_facts` 同时产出三份名单的分支没有测试。** 两轮评审逐个模式对照过原版；补
  测试要依赖 MaSh 在用户目录里的学习状态。
- **N3 Metis 的 `open_attrib` 对匿名事实拼错。** 只有匿名引用的属性把占位定理变成带
  schematic variable 的规则时才走到（如 `[[THEN thin_rl]]`），没有有意义的输入能到达；修它
  还要给 metis 加一次可能抛异常的解析。`metis_instantiations.ML` 保持原样。这一条放宽了
  「能修的都修」。
- **N4 没有名字的局部事实和 `this` 的名字。** 它是命题打印出来再包一层 cartouche，能否解析
  回来取决于项的打印是否可逆（例如字符串常量里的空白同样会被压缩）。这是项打印的问题；
  相关函数被 Nitpick、Nunchaku 共用。tactic prover 不受影响。

## 5. 文件、签名、测试

### 5.1 被补丁的文件和签名

现有六个加 `HOL/Tools/Metis/metis_tactic.ML`，共七个。

新增签名条目（名字是草稿里用的，需要作者批准）：
- `Try0_Util.indexes_of_selection`
- `Sledgehammer_Util.add_attribs_to_name`
- `Metis_Tactic.th_name_of_multi_thms`

已有签名条目全部不变。动手时重算 `src-HOL-Tools-Metis-metis_tactic.ML.patch` 的 Windows 路径
长度。

### 5.2 测试

草稿的 `Release3_Draft.thy` 里的检查原样搬进测试会话（把打印改成断言），即 3.1 到 3.6 各表
【实测】的那些输入。它们全部是确定性的，不依赖外部 prover。要点：

- 序号用 `four(3-, 1)` 配 4 条定理：对的修法给 `[3,4,1]`；误用「选择之后的条数」给 `[3,1]`，
  取第 3 个时越界；第 2 个发布给出不存在的 `four(5)`。
- M4 对每种名字比对确切的文本，包括「不带属性时逐字节不变」。
- M5 的 token 取自 `Method.read_closure_input`，并断言名字 token 带 `Token.Fact` 值；输入里有
  token 内部含空格和逗号的（`''a  b''`、`''a, b''`）。
- M6 经同一个函数，传 `[]` 作参数表；含局部事实、属性产生的事实、实例、被遮蔽的事实。
- 两次真实的 `by (metis …)`，开着 `metis_instantiate`，守住「起名不抛异常」。

草稿里跑不到、要等 private tree 构建的：现有的 Sledgehammer 端到端检查（e、cvc5、metis），
用来确认 M1、M2 没有破坏第 1、2 个发布的行为。

### 5.3 顺序

第三轮评审（本稿和 `draft.diff` 一起审）→ 作者批准 → 把草稿的修改放进 private tree → 构建 →
报告 → 作者下令后提交、发布第 3 版。

第三轮评审同时审了代码，所以构建之后不再单独对四个 `.ML` 文件做一轮代码评审，除非构建或测试
逼出了与 `draft.diff` 不同的修改。测试会话的改动（`tests/` 下）没有被审过，提交之前要做一次
短的核对：确认每条断言在修错的情况下会失败（对顺序、M3、M5、M6 的判断条件各做一次变异）。

## 6. 草稿相对 rev 2 和第二轮裁决的出入

- M2：裁决给的写法 `cartouche (clean_output literal)` 留下 DEL；最终用 Pure 的逆运算（3.2）。
- M6：裁决预计被遮蔽的事实会被丢掉；实测是用长名字。
- M5：token 之间的空格规则定为「相邻 token 之一是 `[ ] ( ) : ,` 时不加空格」，所以逗号后面
  没有空格（`[of 7,simplified]`），与原版的样子一致。

## 7. 评审记录

rev 1（2026-11-11）：16 条 concern，结论「不通过」。主要错误：说 Metis 看不到 `Try0_Util`
（并据此设计了三选一）；说 Metis 那处只在 `metis_instantiate` 时走到；打算调用没有导出的函数；
说触发器的名字会走到归纳规则实例化。

rev 2（2026-11-11）：8 条 concern，结论「不通过，需再评一轮」。主要错误：`foo(3-, 1)` 一行的
原版行为列错；说引号的判断不变；归纳规则实例化的调用者漏了 `mash_eval.ML`；说警告文本不变；
M5 的拆分在最常见的输入上抛 `Scan.MORE`；M4 的退路只覆盖一种失败；Metis 的测试入口够不到
M6；「不修 N5」的理由不成立。对 M7 的描述被判为方向和数字正确但不完整（4.1 已补）。

rev 3（2026-11-11，方案和草稿代码一起审）：7 条 concern，一条被判为吹毛求疵；结论「修改后
接受，不需要再评」。裁判对照源码确认了草稿在真实加载位置能编译、能过签名关卡。成立的都是
局部修改，已并入：
- M1 悄悄把多条定理的顺序从倒序改成了书写顺序，方案没说，也没有测试钉住顺序 → 写进 3.1 的
  后果，交作者定；草稿的检查改为比对有序列表。
- M2 用 PIDE 消息清理函数当解码器 → 改用 `Input.string_of (Syntax.read_input …)`。
- `fact_of_ref` 重写了已导出的 `Facts.selections`；`add_attribs_to_name` 抄了 `xref_of_name`
  的函数体 → 复用、提出共用的 `parse_name`。
- M6 没有任何检查走到「查回来不是同一条」那个分支，问题表里「实例」一行写错（实例没有名字
  提示）→ 改表，加一条人为设置错误提示的检查。
- M6 有四行实测只是打印、没有断言 → 改成断言。5.3 的豁免范围收窄。
被判为吹毛求疵的：`name_of_nth` 在名字 token 没有事实值时退回旧文本（真实的 metis 调用不会
产生这种输入）。

被否决的做法，别再提：
- 在 Metis 里按 token 的位置把选择插进用户的原文本。
- 在 Metis 里用 `string_of_xref'` 或 `Token.pretty_src` 重新打印方法参数。
- 把 `xref_of_name` 挪到 `ATP_Util` 或 `Try0_Util`。
- 让 `HOL.Metis` 额外导入 `Try0`（它本来就是祖先）。
- 归纳规则实例化的名字一律重新打印（会改变今天正确的文本）。
- 只用 `Thm.has_name_hint` 判断 `using` 事实能否起名（留下指错定理的名字）。
- M7 改走 `simp:` 或 `intro:`；M7 新增一个 `facts_config` 而保留坏的 `full_attrs`。
