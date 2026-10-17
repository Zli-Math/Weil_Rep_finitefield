# Weil Representation over Finite Fields

有限域上的 Heisenberg 群、Schrödinger 模型、伪辛群和 Weil 算子的 Lean 4 研究项目，包含特征 2 下的有限计算例子。

仓库：[lizhe0828/weil-representation](https://gitee.com/lizhe0828/weil-representation)

Git 地址：`https://gitee.com/lizhe0828/weil-representation.git`

默认分支：`master`。英文说明见 [README.en.md](README.en.md)。

**项目仍是研究草稿，含有 `sorry`、`native_decide` 和 `#eval!`。构建成功只表示当前源码能够编译，不表示全部数学结论已有完整证明。** 本次整理保留现有数学定义与证明进度，没有宣称完成 Weil 表示或二重覆盖的构造。

## 环境与运行

- Lean：`leanprover/lean4:v4.15.0-rc1`。
- mathlib：`b2158cc40abd16b858e8aa3b0e6f452789b4b28b`；在 `lakefile.lean` 与 `lake-manifest.json` 中同时固定。
- 其他依赖使用已提交的 `lake-manifest.json`。本次没有升级工具链或依赖。

```sh
git clone https://gitee.com/lizhe0828/weil-representation.git
cd weil-representation
lake exe cache get
./scripts/check.sh
```

使用 VS Code 打开项目目录并安装 `leanprover.lean4` 扩展。主入口是 [WeilRepFinitefield.lean](WeilRepFinitefield.lean)。

只构建主库：

```sh
lake build
```

单独构建计算例子：

```sh
lake build WeilRepFinitefield.Examples.F2 WeilRepFinitefield.Examples.Cocycle
```

`check.sh` 依次检查主库和这两个例子；`archive/` 不在检查范围。两份例子保留各自的全局记号，应分别导入，不应在同一 Lean 文件中同时导入。它们以及主库内保留的计算演示会输出枚举结果；部分计算使用 `#eval!`，不能将这些输出当作消除了 `sorry` 的证明。

## 文件组织

| 文件 | 内容与状态 |
|---|---|
| [Compute.lean](WeilRepFinitefield/Compute.lean) | 有限枚举、矩阵与线性映射、可逆线性群子类型、显示及根式工具。 |
| [Heisenberg.lean](WeilRepFinitefield/Heisenberg.lean) | 双线性型给出的 Heisenberg 群、中心、极化和坐标分解。 |
| [HeisenbergRepresentation.lean](WeilRepFinitefield/HeisenbergRepresentation.lean) | 合并 Schrödinger 函数空间、平移表示、Y 模型与坐标公式；部分同构及公式仍待证。 |
| [QuadForm2.lean](WeilRepFinitefield/QuadForm2.lean) | 二次型的下三角矩阵编码、正交群及有限枚举；编码互逆性仍待证。 |
| [PseudoSymplecticGroup.lean](WeilRepFinitefield/PseudoSymplecticGroup.lean) | 辛群、伪辛群及其 Heisenberg 作用；`comp_associated` 仍待证。 |
| [WeilRep.lean](WeilRepFinitefield/WeilRep.lean) | 平均交织算子、伴随向量、归一化及 cocycle；若干核心步骤仍待证。`DPs` 仅有数据和候选乘法。 |
| [QuadraticRing.lean](WeilRepFinitefield/QuadraticRing.lean) | 二次扩张环及非平方假设下的域结构。 |
| [Quadratictwo.lean](WeilRepFinitefield/Quadratictwo.lean) | 例子使用的精确系数域 `ℚ(√2,i)` 及实例。 |
| [Examples/F2.lean](WeilRepFinitefield/Examples/F2.lean) | 二维辛群、双线性型、正交变换的枚举例子。 |
| [Examples/Cocycle.lean](WeilRepFinitefield/Examples/Cocycle.lean) | 极化、特征及 cocycle 矩阵实验；极化和特征延拓仍有待证项。 |
| [archive/](archive/README.md) | 历史实现和本地旧例子，保留源码供查阅，不作为当前可构建库。 |

主线依赖为：`Compute → Heisenberg / QuadForm2 → HeisenbergRepresentation / PseudoSymplecticGroup → WeilRep`。系数域工具供独立例子使用。各当前 Lean 文件开头均有中文内容说明。

## 本次整理与旧路径迁移

本次以远端 `86652e985c97a0000156262c57fc37a13226835c` 为基础，整合原本地 `76ea196` 上的未提交工作；两者之间的远端提交均保留。

- `SchrodingerModel.lean` 合并进 `HeisenbergRepresentation.lean`，保留 `Schrodinger_Model` 命名空间。旧的直接 import 需改为后者。
- 删除仅转发 import 的 `Basic.lean`。总入口直接导入 `WeilRep`；原先直接导入 `WeilRepFinitefield.Basic` 的代码可改为 `WeilRepFinitefield`。
- `F2.lean` 移至 `Examples/F2.lean`；远端较新的 `F2_example.lean` 移至 `Examples/Cocycle.lean`。相应模块名添加 `.Examples`，后者名称改为 `Cocycle`。
- 五份未被当前主线或例子导入的历史实现移入 `archive/`，没有删除其中的数学代码。
- 本地 cocycle 的修改已经出现在远端最新版中，保留该新版。旧本地例子与远端重写发生冲突，故将本地完整内容保存为 `archive/F2_example_local.lean`，当前例子采用远端新版。其余本地源码改动均保留在对应当前或归档文件中。
- 移除传递冗余导入和当前主库的独立 `#check`、`#print`、`#synth` 调试命令；保留计算演示。停止跟踪 `.DS_Store`，忽略依赖缓存、编译产物和日志。

本次没有修补现有 `sorry`，也没有新增数学公理或降低待证命题的假设来使构建通过。原有定理或算子可能依赖未完成证明，应在后续数学审查中继续核实。

## 同步与审查

日常更新前先检查本地改动；有未提交工作时先提交或妥善保存，再拉取：

```sh
git status --short --branch
git pull --ff-only origin master
```

完成修改并通过检查后，提交并推送。同步状态可用以下命令核对：

```sh
git fetch origin
git rev-list --left-right --count HEAD...origin/master
git status --short
```

在 `master` 上，前者输出 `0 0` 且后者为空，表示当前本地工作区与已获取的远端分支一致；之后远端或本地仍可能继续变化。本项目没有配置自动推送。

本轮独立审查见 [REVIEW.md](REVIEW.md)，交付源码清单见 [docs/REVIEW_TARGET.sha256](docs/REVIEW_TARGET.sha256)。审查范围是同步合并、结构调整、内容保留和构建，不把现有占位证明视为已完成的形式化成果。
