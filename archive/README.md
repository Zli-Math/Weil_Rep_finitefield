# 历史草稿

这里保存未纳入当前库的早期实现和原本地例子。文件内容按整理前的相应版本保留，便于继续研究或查阅；没有将其改造成兼容当前接口的模块，也不保证它们可以单独编译。正常构建及 `scripts/check.sh` 不导入这些文件。

| 文件 | 来源与当前对应内容 |
|---|---|
| `HeisenbergGroup.lean` | 早期以普通函数和自定义 `IsBilinear` 建群的实现；当前主线使用 `WeilRepFinitefield/Heisenberg.lean`。 |
| `Schrodinger_Model.lean` | 早期极化与坐标模型，包含原本地未提交改动；当前主线使用 `HeisenbergRepresentation.lean`。 |
| `QuadForm.lean` | 逐行二次型编码的另一份草稿，包含原本地未提交改动；当前主线使用下三角矩阵版本 `QuadForm2.lean`。 |
| `Quadratic.lean` | 早期正交群及二次型试验；部分接口与当前 `QuadForm2.lean` 重复或不兼容。 |
| `WeilRep_old.lean` | 旧 Weil 算子及求和推导，保留未完成步骤；当前主线为 `WeilRep.lean`。 |
| `F2_example_local.lean` | 整理前本地 `F2_example.lean` 的完整内容，含未提交编辑；远端较新的版本现在位于 `WeilRepFinitefield/Examples/Cocycle.lean`。 |

历史远端基线为 `86652e985c97a0000156262c57fc37a13226835c`；原本地 HEAD 为 `76ea196`（完整版本记录见本轮审查报告）。草稿中的 `sorry`、注释掉的推导和旧接口均属于已有研究状态，不应因归档而被视为已验证。
