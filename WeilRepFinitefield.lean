import WeilRepFinitefield.WeilRep

/-!
# 有限域 Weil 表示研究项目：总入口

本入口导入当前主线：Compute → Heisenberg / QuadForm2 →
HeisenbergRepresentation / PseudoSymplecticGroup → WeilRep。
Schrödinger 函数空间及其表示已集中在 HeisenbergRepresentation。

Examples/F2 与 Examples/Cocycle 是各自独立的计算例子；不要将两者同时导入，
它们保留了各自原有的全局例子记号。archive 保存未纳入当前构建的历史草稿。
此项目仍含未完成证明；构建通过不表示整个 Weil 表示理论已形式化完成。
仓库地址、构建命令、迁移说明及已知限制见 README.md。
-/
