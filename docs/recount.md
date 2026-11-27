# 定理 1.1 与七项目标的证明行数复算

定理 1.1 在整条仿射直线上从逐点权上界推出几何 $H_c^1$ 的权上界。能与北大证明逐行比较的是另加逐点纯性或混合性的特例。七个锁定目标可以合并计算新路线的足迹。只有范围和结论均对齐的比较才有“节省多少行”的分母。[七项数学陈述](mathematics.md) · [种子、Lean 特化证明和适用范围](route-roots.json)

## 两种复算

在公开工程的根目录运行。快速复算需要 Python 3.10 以上、Git 和锁定的北大源码。以下命令在本次复算专用的临时目录中保存结果。若已有锁定 checkout，可将 `upstream` 设为其路径，跳过克隆和检出两行。

```sh
run_dir=$(mktemp -d)
upstream="$run_dir/weil-conjectures"
git clone --config core.autocrlf=false https://github.com/formal-arithmetic-geometry/weil-conjectures.git "$upstream"
git -C "$upstream" checkout --detach 497f33d964609973fe4ed9647a1e5d32369f0d09
python3 docs/recount.py --upstream "$upstream" --output "$run_dir/ranges.json"
```

脚本默认读取发行清单。一行可以列出多个比较范围，只有计数和逐行区间完全相同的记录才会合并。只取得四份附录文件时，脚本直接读取种子文件内无损压缩的完整区间。它检查依赖锁、目标名、每个计数模块的源码 SHA-256 及物理行数，再展开三类互斥区间，重算每个模块及总表，并核对每个范围的区间指纹。追加 `--scope pure-degree-one` 可查看一个 1.1 特例，`--scope seven-native` 可查看七项并集。追加 `--export-inventory "$run_dir/route-ranges.tsv"` 可导出每行对应一个比较范围的完整清单，`--inventory "$run_dir/route-ranges.tsv"` 可直接从该表重算。[逐模块清单](module-inventory.tsv) · [复算程序](recount.py)

要让 Lean 从编译输入重新找出每个可达声明，先按公开工程的 `lean-toolchain` 安装 Lean 和 Lake。以下命令也构建测量涉及而正式证明未导入的北大入口。在已有构建的工程中可直接运行 `lake env` 一行。在同一 shell 中沿用前一步的 `run_dir`。单独运行此步骤时先执行 `run_dir=$(mktemp -d)`。

```sh
lake build
lake build @weil-conjectures/+WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper \
           @weil-conjectures/+WeilConjectures.DeligneLaumon.Reduction.AffineCurve \
           @weil-conjectures/+WeilConjectures.DeligneLaumon.Reduction.FormalSteps \
           @weil-conjectures/+WeilConjectures.DeligneLaumon.Reduction.MixedTensor \
           @weil-conjectures/+WeilConjectures.DeligneLaumon.Reduction.MixedStalk \
           @weil-conjectures/+WeilConjectures.ZetaFunction.LissePurity \
           @weil-conjectures/+WeilConjectures.ZetaFunction.Weights
lake env python3 docs/recount.py --closures --output "$run_dir/closures.json"
```

两条路径都输出 `old-only`、`new-WeilII`、`new-PKU`、`shared` 和有符号净差。运行 `cmp "$run_dir/ranges.json" "$run_dir/closures.json"`，退出码 0 表示两份 JSON 逐字节相同。JSON 还列出声明数、缺区间数、整文件足迹、特化声明的行数及含特化代码的净差。完整闭包模式会检查每个种子的内核名称和实际所属模块，并逐根核对包含所有包的闭包指纹。[Lean 查询源文本](route-range-query.txt)

完整查询在一个 Lean 进程中读入所选根的导入并复用依赖边，再按各根核对声明归属。七根预检实测，一次旧实现连续载入七套环境达到 109,478,908 KiB 峰值 RSS（约 104.4 GiB）；采用共享环境和逐根核对后，同一七项并集实测 17,913,188 KiB（约 17.1 GiB），两次均返回 0。低内存机器可用下式逐个根处理并串行映射源码；单个最大导入仍须能装入内存。默认最多四个轻量进程独立处理不同模块的源码区间，Lean 查询依次运行。

```sh
lake env python3 docs/recount.py --closures --batch-size 1 --jobs 1 --output "$run_dir/closures-one-at-a-time.json"
```

## 行号如何分给两条路线

1. 对每个具名声明，Lean 从其类型和证明体或定义体出发，递归读取常量引用。互归纳类型带入同组类型，构造器带入所属类型，递归器带入各归约规则的构造器及右端引用。读取模块时使用 Lean 的 private 可见级别，使封装在定理中的证明也能展开。每个特化的种子是 `witnessLean` 中证明的全部第一层导入声明，包括证明中使用的类型、实例和强制转换。单独的七项目标各取一个根。引理 2.6 的模块有 15 个根，整模块闭包含 35,304 个声明，从指数和定理自身出发则为 35,296 个。
2. 对 WeilII 和 WeilConjectures 两个包，在各可达声明所属模块的 `.ilean` 文件中以完整声明名读取 `decls` 的源码区间。文件按 LF 分行，最后一行没有换行符也算一行。编译器区间从零起算，右端点开。末端列为零时略去末行，其他情形计入。区间内的空行、注释和文档注释按实际位置计入。导入、声明间的空行等也计入“整文件足迹”。找不到精确区间的声明，以及来源位置越界或为空的记录，计入缺区间数。
3. 按（所属模块，物理行号）去重。记旧独用行数为 O、新独用行数为 P+U（项目 P，北大 U），交集为 C。旧路线总量为 O+C，新路线总量为 P+U+C，同结论的净差为 O−P−U，比例用净差除以 O+C。正数表示新路线在这两个包中使用较少的可定位行。Mathlib、Lean 核心和其他包的声明参与追溯，表中不给这些包计源码行。`WeilConjectures.Mathlib` 属于北大包。
4. 特化证明放在种子文件中，可逐条阅读其函数类型、额外假设与证明。主表计库内声明的区间。计入写出特化本身的成本时，每侧加上该侧所有特化定理及私有辅助定理的声明行，包括类型和证明；另列 `:= by` 下一行起的证明体行数。源码中的 `import`、`open`、测量命令均在这些定理之外。

## 固定输入上的核对

实测源码版本为 WeilII `05f448032e7bb13842030e8e69a7f469ee6bdea0`、北大 `497f33d964609973fe4ed9647a1e5d32369f0d09` 和 Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`，工具链为 Lean 4.35.0。ECS 交叉试跑采用公开候选 `b50e3bbf00d10ae30b7714ab1d2fd6c2ada69877`。逐字节核对的 388 个模块及三份 Lake 配置与实测版本一致。[发行索引](../traces/index.json)

前两行对同一个逐点纯层的 $H_c^1$ 分别采用北大的一次根和全次数根。第三行在 1.1 的逐点界之外假设层混合。对于 1.5 与 2.1，`mixed` 行另给外张量幂的混合权上界，`factor` 行从原层的混合权上界推出它。

| 共同范围 | O | P | U | C | 旧分母 | 净差 | 净差 / 旧 |
|---|---|---|---|---|---|---|---|
| pure-degree-one | 51,700 | 17,969 | 7,507 | 1,437,842 | 1,489,542 | +26,224 | +1.76% |
| pure-all-degrees | 51,865 | 17,969 | 7,507 | 1,437,842 | 1,489,707 | +26,389 | +1.77% |
| mixed-1.1 | 60,578 | 17,969 | 7,330 | 1,438,032 | 1,498,610 | +35,279 | +2.35% |
| mixed-1.5 | 61,296 | 9,704 | 5,489 | 1,437,330 | 1,498,626 | +46,103 | +3.08% |
| mixed-2.1 | 156,656 | 3,101 | 2,289 | 1,341,987 | 1,498,643 | +151,266 | +10.09% |
| factor-1.5 | 61,658 | 9,704 | 5,456 | 1,437,363 | 1,499,021 | +46,498 | +3.10% |
| factor-2.1 | 157,037 | 3,101 | 2,275 | 1,342,001 | 1,499,038 | +151,661 | +10.12% |

定理 1.1 的一次纯性特例在早期候选表中记为 O=51,692、P=17,969、U=7,499、C=1,437,850。上表采用逐根核验的完整清单，O 和 U 各增加 8，C 减少 8。两侧总量仍为 1,489,542 和 1,463,318，净差仍为 +26,224。

| 锁定目标 | 项目区间行 | 北大区间行 | 两包合计 | 两包可达声明 / 缺区间 |
|---|---|---|---|---|
| 1.1-native | 17,969 | 1,445,330 | 1,463,299 | 153,684 / 85,325 |
| only-1.5 | 9,729 | 1,442,767 | 1,452,496 | 151,392 / 83,607 |
| only-2.1 | 3,143 | 1,344,207 | 1,347,350 | 135,158 / 74,029 |
| only-2.2 | 1,830 | 1,384,561 | 1,386,391 | 143,657 / 78,821 |
| only-2.4 | 5,105 | 1,272,762 | 1,277,867 | 126,596 / 69,289 |
| only-2.5 | 5,903 | 1,272,707 | 1,278,610 | 126,728 / 69,364 |
| only-2.6 | 112 | 131 | 243 | 26 / 8 |
| seven-native | 18,708 | 1,445,641 | 1,464,349 | 153,771 / 85,374 |

在 ECS 的公开候选临时目录中，复用锁定依赖和 WeilII 的编译文件。`python3 docs/recount.py --output ranges.json`、`lake env python3 docs/recount.py --closures --output closures.json` 和 `cmp ranges.json closures.json` 的退出码依次为 **0、0、0**。27 组种子的完整闭包逐根通过 SHA-256 核对。四个源码进程映射了 12,512 个不同模块，整次实测峰值 RSS 为 18,674,944 KiB（约 17.8 GiB）。

26 个范围的 O、P、U、C、可达声明数、缺区间声明数、整文件足迹及逐模块区间指纹均一致。发行清单的 37,316 条合并记录、种子文件内按范围展开的 275,584 条计量记录和原始逐模块表，各自重算得到的 JSON 逐字节相同。七个同结论特例的净差、旧分母、特化声明和证明体行数及计入特化后的净差也逐项匹配原始报告。[发行清单](module-inventory.tsv) · [路线比较](upstream-replacement.md)

逐根模式也在引理 2.6 上实测。命令 `lake env python3 docs/recount.py --closures --scope only-2.6 --batch-size 1 --jobs 4 --output closures.json` 以 0 退出，四个独立进程处理四个计入源码的模块，得到 WeilII 112 行、北大 131 行。将 `Nat.succ` 故意归到 `Lean` 模块的检索测试以 1 退出。

单侧清单中空种子集的独用行数为 0，JSON 将缺少的路线总量记为 null。四个其余目标涉及带符号的迹恒等式、一般超平面的同时消没、同一个有限扩域截面的光滑性与消没，以及任意链长的指数和界。已识别的北大成分各只给部分步骤。清单中 `seven-vs-partial-anchors` 等范围列出指定集合的重叠，净差与比例留空。上游定理也有其他适用情形与调用者，避用的行数不能据以断定上游整库可删除的行数。

历史纯性试验的原始计量另记 28 个模块、6,197 个整文件物理行。公开树未收录这些归档源码，因此这项历史数值无法从公开树独立复算。两条路线的分子和分母均排除这些文件。

正式冻结源版本为 `1d2a35cad016e9840d47db5143d19573be9999af`。从复算候选到冻结本，388 份公开数学源码、Lake 配置、各模块审计输入及轨迹指纹均吻合，两份目标的独立验收记录更新。公开库自身的根提交可在根目录用 `git rev-list --max-parents=0 HEAD` 查看。上面两组命令分别使用公开库的源码与锁定的北大依赖。[冻结输入与验收](project-report.md) · [依赖锁](../lake-manifest.json)
