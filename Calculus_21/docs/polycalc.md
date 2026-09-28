# PolyCalc 模块指南

`PolyCalc` 是一个用于构建“表达式多态计算系统”的通用基础模块。它不规定表达式的语法，也不规定某一种具体数学运算，而是解决这类系统共同面对的三个问题：

1. 一个表达式可能得到不同精度的结果，如何形式化“安全地丢失信息”；
2. 哪些结果足够精确，可以恢复为 Lean 的普通等式；
3. 如何在 `calc`、重写和复合表达式中方便地使用上述关系。

`Calculus_21.Limit.Expr` 是当前最完整的实例。它把极限结果表示成有限值、正无穷、负无穷、无符号无穷、发散和未知，并利用 `PolyCalc` 组织这些结果之间的精度关系。本文先介绍通用模块，再逐层分析该实例，最后给出构造新计算系统的完整步骤。

## 1. 模块组成

`PolyCalc` 目录包含三个实现模块和一个统一导入模块：

| 模块 | 作用 |
| --- | --- |
| `Calculus_21.PolyCalc.Defs` | 定义抽象计算域、退化关系 `=.`、proper 值和条件关系 `=?` |
| `Calculus_21.PolyCalc.AutoReflect` | 从复合结果的 proper 性自动反推出子表达式的 proper 性 |
| `Calculus_21.PolyCalc.PolyRw` | 在目标端 proper 时，把 `=.` 转换成普通等式并执行重写 |
| `Calculus_21.PolyCalc` | 统一导入以上三个模块 |

若需要完整功能，通常直接导入：

```lean
import «Calculus_21».PolyCalc
```

只导入 `Calculus_21.PolyCalc.AutoReflect` 会间接获得 `Defs`，但不会获得 `poly_rw`。这一点在 `Limit.Expr.Init` 中可以看到：它能使用 `=.`, `=?` 和 proper 反射，却不能仅凭该导入使用 `poly_rw`。

## 2. 核心思想：结果之间存在精度方向

普通等式要求两边完全相同，但多态计算经常需要表达较弱的结论。例如，一个系统可能知道某结果为正无穷，也可以安全地只报告“无穷”“发散”或“未知”：

```text
正无穷  →  无符号无穷  →  发散  →  未知
```

箭头表示信息丢失。左边更精确，右边更不精确，但右边仍然是一个正确结论。

`PolyCalc` 将这种关系记为：

```lean
A =. B
```

其含义是：

> `A` 可以经过零步或多步合法退化得到 `B`；等价地，`A` 至少和 `B` 一样精确。

因此，尽管记号类似等式，`=.` 通常不是对称关系。若有 `A =. B`，一般不能推出 `B =. A`。

从抽象解释的角度，也可以把 `=.` 看作一个“从更精确到更抽象”的精度预序。不过，当前 `PolyCalc` 类本身只保存生成这项关系所需的数据，并不要求反对称性或无环性。

## 3. `PolyCalc`：定义一个抽象结果域

核心类型类定义在 `Calculus_21/PolyCalc/Defs.lean`：

```lean
class PolyCalc (ExprValue : Type u) where
  fallbackCore : ExprValue → ExprValue → Prop
  unknown : ExprValue
```

一个实例只需要给出两项数据。

### 3.1 `fallbackCore`

`fallbackCore A B` 表示领域特有的一步信息退化。例如极限系统声明：

```lean
posInfty      → unsignedInfty
negInfty      → unsignedInfty
unsignedInfty → divergence
```

它只是一步生成关系，不需要调用者自行加入自反边或传递边。

### 3.2 `unknown`

`unknown` 是领域指定的完全未知值。框架自动允许任意结果一步退化到它：

```text
A → unknown
```

所以领域实现者不需要在 `fallbackCore` 中重复声明这些边。

### 3.3 类中没有隐含的序性质

`PolyCalc` 没有要求 `fallbackCore` 自反、传递、反对称或无环，也没有要求任意运算保持该关系。这些都不是类型类自动提供的性质：

- 自反性和传递性由后面的闭包构造提供；
- 反对称性并不总是成立，也没有被要求；
- 运算兼容性必须由具体领域单独证明；
- `fallbackCore` 的数学健全性由实例作者负责。

这使该接口非常轻量，但也意味着实现新领域时必须认真设计退化方向。

## 4. `FallbackStep` 与多态等式 `=.`

### 4.1 一步退化

框架先把领域边和通用未知边合并成 `PolyCalc.FallbackStep`：

```lean
inductive PolyCalc.FallbackStep [PolyCalc ExprValue] :
    ExprValue → ExprValue → Prop where
  | core : fallbackCore A B → FallbackStep A B
  | unknown (A : ExprValue) : FallbackStep A unknown
```

其中：

- `FallbackStep.core` 注入领域定义的 `fallbackCore`；
- `FallbackStep.unknown` 允许任何值退化到 `unknown`。

### 4.2 自反传递闭包

真正对外使用的关系是：

```lean
def PolyCalc.PolyEq [PolyCalc ExprValue] :
    ExprValue → ExprValue → Prop :=
  ReflTransGen (FallbackStep (ExprValue := ExprValue))

infix:50 " =. " => PolyCalc.PolyEq
```

`ReflTransGen` 是自反传递闭包，因此 `A =. B` 允许：

- 零步：`A =. A`；
- 一步：一个 core 退化或退化到 unknown；
- 多步：若干合法退化的组合。

### 4.3 基本构造定理

公开 API 提供三种常用的引入方式：

```lean
PolyCalc.pe_unknown
  (A : ExprValue) : A =. PolyCalc.unknown

PolyCalc.pe_of_fallbackCore
  (h : PolyCalc.fallbackCore A B) : A =. B

PolyCalc.pe_of_eq
  (h : A = B) : A =. B
```

例如：

```lean
example [PolyCalc α] (a : α) : a =. PolyCalc.unknown :=
  PolyCalc.pe_unknown a
```

自反和传递定理在实现中是 private 声明，但通过 `@[refl]`、`@[trans]` 和 `Trans` 实例注册。用户应依赖 `rfl`、`calc` 和关系自动化，而不是依赖 private 定理名。

### 4.4 与普通等式混合使用

模块提供下列 `Trans` 实例：

```lean
Trans PolyEq PolyEq PolyEq
Trans Eq PolyEq PolyEq
Trans PolyEq Eq PolyEq
```

所以可以在同一个 `calc` 中混合 `=` 和 `=.`：

```lean
calc
  A = B := hAB
  _ =. C := hBC
  _ = D := hCD
```

整条链的结论是 `A =. D`。普通等式步骤不会改变精度关系的方向。

## 5. `ProperClass`：哪些结果可以恢复普通等式

`=.` 允许丢失信息，因此通常不能用于任意位置的普通重写。为此，模块引入 proper 值：

```lean
class ProperClass (ExprValue : Type u) [PolyCalc ExprValue] where
  isProper : ExprValue → Prop
  rigid : ∀ a b : ExprValue, a =. b → isProper b → a = b
```

核心公理是 `rigid`：

> 如果 `a` 可以退化到 proper 值 `b`，那么这次退化实际上没有丢失信息，故 `a = b`。

注意 proper 性出现在关系的右端。已知左端 proper 并不能阻止它退化到一个不 proper 的结果。例如 proper 值仍然可以退化到 `unknown`。

### 5.1 设计 proper 谓词的约束

若某个值 `b` 被标记为 proper，则所有满足 `a =. b` 的 `a` 都必须等于 `b`。因此不能随意扩大 `isProper`。

例如，若 `fallbackCore x b` 且 `x ≠ b`，那么 `b` 就不能被标记为 proper，否则无法证明 `rigid`。

### 5.2 `eq_of_proper`

`Calculus_21.PolyCalc.PolyRw` 提供最常用的消去定理：

```lean
theorem PolyCalc.PolyEq.eq_of_proper
    (h : A =. B)
    (hB : ProperClass.isProper B) :
    A = B
```

它只是 `ProperClass.rigid` 的方便封装。若自动重写不适用，可以显式使用此定理：

```lean
have hEq : A = B :=
  PolyCalc.PolyEq.eq_of_proper h hB
rw [hEq]
```

## 6. 条件多态等式 `=?`

有些计算公式只在右侧结果足够精确时才成立。例如乘法法则、除法法则或链式法则的符号右式可能计算为 `unknown`。模块用 `EqualIfProper` 表达这种规则：

```lean
def EqualIfProper (A B : ExprValue) : Prop :=
  ProperClass.isProper B → A =. B

infix:50 " =? " => EqualIfProper
```

因此：

```lean
A =? B
```

应读作：

> 如果右式 `B` 是 proper 的，那么 `A =. B`。

证明一个 `=?` 目标通常从引入右式 proper 性开始：

```lean
theorem someRule : lhs =? rhs := by
  intro h_rhs_proper
  -- 目标变为 lhs =. rhs
  ...
```

### 6.1 `=?` 不是无条件等式

如果 `B` 不 proper，那么 `ProperClass.isProper B → A =. B` 可以空真。因此仅有 `A =? B` 并不能无条件推出 `A =. B`，更不能无条件推出 `A = B`。

只有再得到 `hB : ProperClass.isProper B` 后，才能应用关系：

```lean
have hPoly : A =. B := h hB
have hEq : A = B := PolyCalc.PolyEq.eq_of_proper hPoly hB
```

这项空真性不是缺陷，而是 `=?` 用来延迟 side condition 的关键。

### 6.2 `calc` 中的组合

模块为 `=?` 注册了与 `=`、`=.` 和自身的传递实例，包括：

```text
=?  后接  =   得到  =?
=   后接  =?  得到  =?
=?  后接  =?  得到  =?
=.  后接  =?  得到  =?
=?  后接  =.  得到  =?
```

这些实例的证明都依赖最终右端 proper 时的刚性。例如在 `B =? C` 且 `C` proper 时，先得到 `B =. C`，再由刚性得到 `B = C`，从而把前一段关系运输到 `C`。

## 7. `AutoProperReflect`：从复合结果反推子结果

证明 `lhs =? rhs` 时，首先得到的是整个 `rhs` proper。但后续证明往往需要知道 `rhs` 中某个子表达式也 proper。`AutoProperReflect` 为这种逆向传播提供类型类接口：

```lean
class AutoProperReflect
    (A B : ExprValue)
    (cond : outParam Prop) : Prop where
  reflect :
    cond →
    ProperClass.isProper A →
    ProperClass.isProper B
```

参数含义如下：

| 参数 | 含义 |
| --- | --- |
| `A` | 已知 proper 的源表达式，通常是一个复合结果 |
| `B` | 希望证明 proper 的目标表达式，通常是某个子表达式 |
| `cond` | 反射所需的附加条件，由实例搜索作为 `outParam` 推导 |

### 7.1 终止实例

框架自带自反实例：

```lean
instance properReflect_refl :
  AutoProperReflect A A True
```

当递归遍历抵达目标本身时，实例搜索由此终止。

### 7.2 两个基础引理

```lean
autoProperReflect
autoProperReflectTo
```

两者都调用找到的实例。区别是 `autoProperReflectTo` 显式接收目标值，便于 tactic 宏生成项。

### 7.3 `script_proper_reflect` 宏

当前支持的准确语法是：

```lean
script_proper_reflect target as hTarget (source := hSource)
```

展开后大致等价于：

```lean
have hTarget : ProperClass.isProper target := by
  exact autoProperReflectTo target hSource (by trivial)
```

例如：

```lean
script_proper_reflect D f x₀ as hDf (source := h_proper)
```

### 7.4 为运算注册反射实例

假设某领域能证明：

```lean
isProper (A + B) → isProper A
isProper (A + B) → isProper B
```

便可把这些性质与已有递归实例组合：

```lean
instance [AutoProperReflect A C cond] :
    AutoProperReflect (A + B) C cond := ...

instance [AutoProperReflect B C cond] :
    AutoProperReflect (A + B) C cond := ...
```

于是实例搜索能够沿加法树递归寻找任意嵌套目标。

### 7.5 限制

`AutoProperReflect` 不是自动理解任意表达式语法的通用遍历器。只有领域显式注册过实例的运算才能被穿透。

此外，`script_proper_reflect` 固定使用 `(by trivial)` 证明 `cond`。如果附加条件不能由 `trivial` 解决，应直接调用 `autoProperReflect` 或 `autoProperReflectTo` 并显式提供证明。

反射性质也不能凭运算的正向单调性自动得到。它是关于“结果 proper 时输入必须满足什么”的逆向性质，必须单独证明，而且并非对所有参数都成立。

## 8. `poly_rw`：安全地用 `=.` 重写

普通 `rw` 需要 Lean 等式，但 `A =. B` 通常只是定向精度关系。`poly_rw` 的做法不是直接按 `=.` 重写，而是先利用右端 proper 性把它转换为真正的等式：

```lean
poly_rw [h]
poly_rw [← h]
poly_rw [h₁, h₂] at location
```

对于规则 `h : A =. B`，宏生成：

```lean
PolyCalc.PolyEq.eq_of_proper h (by trivial)
```

然后交给普通 `rw`。所以它可以安全地在任意上下文中重写。

### 8.1 示例

若某领域中的 `B` 可由 `trivial` 证明 proper：

```lean
example [PolyCalc α] [ProperClass α]
    {A B : α} (h : A =. B)
    (hB : ProperClass.isProper B) :
    some A = some B := by
  have hEq := PolyCalc.PolyEq.eq_of_proper h hB
  rw [hEq]
```

当 `hB` 对 `trivial` 可见时，可简写为：

```lean
poly_rw [h]
```

### 8.2 反向重写仍检查原右端

对于：

```lean
poly_rw [← h]
```

宏先用 `h` 的右端 proper 性证明 `A = B`，再把这个普通等式反向交给 `rw`。它不是要求 `A` proper。

### 8.3 限制和额外行为

- 每条规则的 `=.` 右端必须能由 `trivial` 证明 proper；
- 若 proper 证明较复杂，应先显式调用 `eq_of_proper`，再使用 `rw`；
- 宏目前支持普通规则和 `←` 规则，不支持所有可能的 `rwRule` 扩展形式；
- 执行 `rw` 后还会运行 `try rfl`，所以它可能直接关闭目标。

## 9. `Limit.Expr` 实例概览

`Limit.Expr` 展示了一个完整系统如何在 `PolyCalc` 之上分层构建：

```text
具体极限命题
    ↓ GenericExprLaws
GenericExpr 语义分类器
    ↓
LimitValue 抽象结果
    ↓ PolyCalc / ProperClass
=.、=?、poly_rw、script_proper_reflect
    ↓
极限运算法则、复合规则、自动化以及导数表达式
```

相关文件的职责是：

| 文件 | 职责 |
| --- | --- |
| `Limit/Expr/Init.lean` | 结果域、运算、`PolyCalc`/`ProperClass` 实例、分类器和语义桥 |
| `Limit/Expr/GCongr.lean` | 证明抽象运算保持 `=.`，注册 `gcongr` 规则 |
| `Limit/Expr/ProperReflect.lean` | 注册算术表达式的 proper 逆向传播实例 |
| `Limit/Expr/BasicRules.lean` | 极限表达式的同余和基本计算法则 |
| `Limit/Expr/Elementary.lean` | 初等函数及复合函数的表达式法则 |

## 10. `LimitValue`：极限计算的抽象结果域

`Limit.Expr.Init` 定义：

```lean
inductive LimitValue
  | finite (a : ℝ)
  | unknownLimit
  | posInfty
  | negInfty
  | unsignedInfty
  | divergence
```

对应的表面记号为：

| 构造子 | 记号 | 含义 |
| --- | --- | --- |
| `LimitValue.finite a` | `the a` | 精确有限值 `a` |
| `LimitValue.posInfty` | `pos_infty` | 正无穷 |
| `LimitValue.negInfty` | `neg_infty` | 负无穷 |
| `LimitValue.unsignedInfty` | `infty` | 无穷但符号未知 |
| `LimitValue.divergence` | `diverg` | 不有限收敛 |
| `LimitValue.unknownLimit` | `unknown` | 当前计算没有更多信息 |

这里的 `unknown` 表示信息不足，而不是一个任意垃圾值；`diverg` 则仍携带“不有限收敛”这一语义事实，所以它比 `unknown` 更精确。

## 11. 极限域的 fallback 图

领域特有的一步退化定义为：

```lean
inductive LimitFallbackCore : LimitValue → LimitValue → Prop
  | infty_divergence :
      LimitFallbackCore .unsignedInfty .divergence
  | pos_infty_infty :
      LimitFallbackCore .posInfty .unsignedInfty
  | neg_infty_infty :
      LimitFallbackCore .negInfty .unsignedInfty
```

实例为：

```lean
instance : PolyCalc LimitValue where
  fallbackCore := LimitFallbackCore
  unknown := .unknownLimit
```

结合框架自动加入的 unknown 边，完整方向可画成：

```text
the a ───────────────────────────────────→ unknown

pos_infty ─┐
           ├→ infty → diverg → unknown
neg_infty ─┘
```

由自反传递闭包还可得到：

```lean
pos_infty =. diverg
neg_infty =. unknown
infty =. unknown
```

但反方向通常不成立，例如 `infty =. pos_infty` 不成立，因为无符号无穷不能安全恢复出符号。

## 12. 极限域对 `=.` 的直接刻画

为了避免所有下游证明都分析 `ReflTransGen` 路径，实例定义了模式匹配关系：

```lean
LimitValue.LessPreciseThan : LimitValue → LimitValue → Prop
```

并证明：

```lean
LimitValue.polyEq_iff_lessPreciseThan :
  A =. B ↔ LimitValue.LessPreciseThan A B
```

这个定理是具体领域的重要实现技巧。它把路径关系转换为可通过构造子分类和 `simp` 处理的命题，随后被以下部分复用：

- `ProperClass` 的刚性分析；
- 抽象运算的 `gcongr` 证明；
- `GenericExprBridge` 的语义证明；
- 有限结果的精确性定理。

对于新领域，也建议证明一个类似的直接刻画定理，避免下游代码长期依赖 `ReflTransGen` 的内部表示。

## 13. 极限域中的 proper 值

极限系统只把有限值视为 proper：

```lean
def LimitValue.isProper : LimitValue → Prop
  | .finite _ => True
  | _ => False
```

并安装：

```lean
instance : ProperClass LimitValue
```

其语义是：若某个抽象极限结果可以退化到 `the a`，则它原本只能就是 `the a`。对应的领域定理为：

```lean
LimitValue.finite_iff :
  A =. the a ↔ A = the a
```

它是极限表达式系统中大量普通重写的基础。

另外还提供：

```lean
LimitValue.isProper.getEqual :
  A.isProper → ∃ a : ℝ, A =. the a

LimitValue.isProper.getEqual! :
  A.isProper → ∃ a : ℝ, A = the a
```

前者适合继续留在多态计算关系中，后者直接提取普通等式。

## 14. 抽象运算：总函数化而不是逐步暴露 side condition

`LimitValue` 安装了 `Add`、`Neg`、`Sub`、`Mul`、`Inv`、`Div` 和 `Pow LimitValue LimitValue` 实例。每个运算都是总函数；无法确定更精确结果时返回 `unknown`。

例如乘法包含：

```text
the a * the b       = the (a * b)
the a * pos_infty   = pos_infty，若 a > 0
the a * pos_infty   = neg_infty，若 a < 0
the 0 * pos_infty   = unknown
the a * infty       = infty，若 a ≠ 0
the 0 * infty       = unknown
```

逆运算包含：

```text
(the a)⁻¹ = the a⁻¹，若 a ≠ 0
(the 0)⁻¹ = infty
pos_infty⁻¹ = the 0
neg_infty⁻¹ = the 0
infty⁻¹ = the 0
```

这种设计允许表达式计算持续进行，而不必在每个中间步骤立即要求 `a ≠ 0`、符号条件等 side condition。若最终要求 proper 结果，相关条件再通过 `=?` 和逆向分析出现。

必须区分两件事：

- 定义一个抽象运算，只说明如何计算抽象结果；
- 证明运算保持 `=.`，才允许在关系上下文中安全替换参数。

后者不是 `PolyCalc` 自动提供的。

## 15. `GCongr`：证明运算关于精度关系单调

`Limit/Expr/GCongr.lean` 为下列运算证明并注册 `@[gcongr]` 定理：

- 加法；
- 取负；
- 减法；
- 乘法；
- 逆；
- 除法；
- 幂。

典型逻辑形式为：

```lean
A =. A' → B =. B' → A + B =. A' + B'
```

或：

```lean
A =. B → A⁻¹ =. B⁻¹
```

这些定理本身是 private，但 `@[gcongr]` 属性使 `gcongr` tactic 可以使用它们。证明过程先通过 `polyEq_iff_lessPreciseThan` 把 `=.` 化为直接关系，再按 `LimitValue` 构造子穷举。

于是可以证明嵌套上下文中的关系：

```lean
example (h₁ : limₙ a =. limₙ b)
    (h₂ : limₙ c =. limₙ d) :
    -(limₙ a - limₙ c) =. -(limₙ b - limₙ d) := by
  gcongr
```

这展示了构造新系统时的必要步骤：每个希望支持上下文替换的运算，都要证明其关于 `=.` 的单调性，并按需要注册给 `gcongr`。

## 16. 极限域的 proper 反射

`Limit/Expr/ProperReflect.lean` 先证明复合结果有限时，其必要子结果也有限：

```text
isProper (A + B) → isProper A
isProper (A + B) → isProper B
isProper (A * B) → isProper A
isProper (A * B) → isProper B
isProper (-A)    → isProper A
```

再将这些引理包装成递归 `AutoProperReflect` 实例。因此从：

```lean
h : ProperClass.isProper ((A * B + C) / the b)
```

可以沿已注册路径反推出 `B` proper。

当前支持的结构包括：

- 加法的左右参数；
- 乘法的左右参数；
- 取负的参数；
- 减法的左右参数；
- 分母语法上为 `the b` 时，除法的分子。

最后一项的限制很重要。系统没有注册任意 `A / B` 的通用反射，因为抽象逆运算可能把无穷值映到有限的 `the 0`，因此从商有限并不能朴素推出任意分母有限。反射实例必须依据具体运算表证明，而不能机械地为每个参数生成。

## 17. 从具体极限语义构造表达式结果

`Limit.Expr` 不只是定义一个抽象值类型，还给出了把数学语义分类成抽象值的完整方法。

### 17.1 `GenericExprLaws`

```lean
class GenericExprLaws (C P N U : Prop) where
  finitePred : ℝ → Prop
  evC : C → ℝ
  evC_spec : ∀ hC, finitePred (evC hC)
  finite_exists : ∀ {L}, finitePred L → C
  finite_unique : ∀ {L₁ L₂},
    finitePred L₁ → finitePred L₂ → L₁ = L₂
  pos_not_finite : P → ¬ C
  neg_not_finite : N → ¬ C
  infty_not_finite : U → ¬ C
  neg_not_pos : N → ¬ P
  pos_to_infty : P → U
  neg_to_infty : N → U
```

四个命题参数分别描述：

| 参数 | 极限实例中的意义 |
| --- | --- |
| `C` | 存在有限极限 |
| `P` | 趋于正无穷 |
| `N` | 趋于负无穷 |
| `U` | 绝对值趋于无穷，符号可以未知 |

`finitePred` 给出带具体实数结果的有限极限命题；`evC` 从存在性证明中选择唯一有限值。其余字段编码唯一性、互斥关系和有符号无穷到无符号无穷的蕴含。

库分别为数列极限、有限点函数极限、左右极限、正负无穷处极限以及双侧无穷处极限安装实例。

### 17.2 `GenericExpr`

```lean
def GenericExpr (C P N U : Prop)
    [laws : GenericExprLaws C P N U] : LimitValue :=
  if h : C then the (laws.evC h)
  else if P then pos_infty
  else if N then neg_infty
  else if U then infty
  else diverg
```

分类优先级为：

1. 有限收敛；
2. 正无穷；
3. 负无穷；
4. 无符号无穷；
5. 发散。

`GenericExpr` 不直接产生 `unknown`。`unknown` 主要来自抽象运算中的不定情况，或来自任意值到 unknown 的退化。

### 17.3 七种极限表达式

在 `GenericExpr` 上，库定义：

```lean
SeqLimitExpr
FuncLimitExpr
LeftLimitExpr
RightLimitExpr
NegInftyLimitExpr
PosInftyLimitExpr
InftyLimitExpr
```

并提供记号：

```lean
limₙ a
lim x₀ f
lim₋ x₀ f
lim₊ x₀ f
lim pos_infty f
lim neg_infty f
lim infty f
```

## 18. `GenericExprBridge`：统一语义表示定理

抽象结果的语义解释定义为：

```lean
def GenericExprSem ... : LimitValue → Prop
  | the L     => laws.finitePred L
  | pos_infty => P
  | neg_infty => N
  | infty     => U
  | diverg    => ¬ C
  | unknown   => True
```

核心桥接定理是：

```lean
GenericExprBridge :
  GenericExpr C P N U =. A ↔ GenericExprSem C P N U A
```

这一定理精确说明了 `=.` 在该实例中的作用：表达式结果能够退化到某个观察值，当且仅当对应的具体语义命题成立。

典型对应关系为：

```text
GenericExpr ... =. the L     ↔ 有限极限为 L
GenericExpr ... =. pos_infty ↔ 趋于正无穷
GenericExpr ... =. neg_infty ↔ 趋于负无穷
GenericExpr ... =. infty     ↔ 无符号无穷
GenericExpr ... =. diverg    ↔ 不存在有限极限
GenericExpr ... =. unknown   ↔ True
```

注意 `diverg` 的语义是“不有限收敛”。正无穷、负无穷和无符号无穷都可以进一步退化到 `diverg`，与此解释一致。

## 19. 具体命题与表达式命题之间的桥

`GenericExprBridge` 被包装成大量用户友好的双向定理。例如：

```lean
SeqLimit.toSeqLimitExpr
SeqLimit.fromSeqLimitExpr

FuncLimit.toFuncLimitExpr
FuncLimit.fromFuncLimitExpr

LeftLimit.toLeftLimitExpr
LeftLimit.fromLeftLimitExpr

RightLimit.toRightLimitExpr
RightLimit.fromRightLimitExpr
```

使用方式如下：

```lean
example (h : FuncLimit ⟨f, dom⟩ x₀ L) :
    lim x₀ f =. the L :=
  h.toFuncLimitExpr

example
    (h_dom : ∃ δ > 0, Nbhd x₀ δ ⊆ dom)
    (h : lim x₀ f =. the L) :
    FuncLimit ⟨f, dom⟩ x₀ L :=
  FuncLimit.fromFuncLimitExpr h_dom h
```

反向定理需要邻域包含于具体函数定义域的证明，因为表达式层使用全域函数 `⟨f, Iii⟩`，而命题层的 `RFunction` 可以携带任意定义域。

相同模式还覆盖：

- 正、负、无符号无穷结果；
- 左右极限；
- 正负无穷及双侧无穷处的极限；
- `diverg` 与“不存在有限极限”之间的转换。

例如：

```lean
FuncLimitExpr.ofNotConverges
FuncLimitExpr.toNotConverges
InftyLimitExpr.ofNotConverges
InftyLimitExpr.toNotConverges
```

## 20. 为什么基本计算法则返回 `=.`

典型极限法则写成：

```lean
theorem FuncLimitExpr.Add :
  lim x₀ (f + g) =. lim x₀ f + lim x₀ g
```

而不是普通等式。原因是分别计算子极限再做抽象运算可能丢失信息。

例如，若两个子表达式分别只知道为 `pos_infty` 和 `neg_infty`，抽象加法返回 `unknown`；但原函数之和可能由于消去而具有更精确的有限极限。因此通常只能保证：

> 原表达式的直接语义结果至少和“子结果经过抽象运算”一样精确。

这正是 `=.` 的方向：

```text
直接计算结果 =. 组合计算结果
```

同理，`BasicRules.lean` 中的加、减、乘、除、取负、逆和幂规则都采用 `=.`。

## 21. 表达式同余、局部计算和复合

### 21.1 最终相同函数的普通同余

若两个函数在相关邻域内相同，它们的语义分类完全相同，所以 `FuncLimitExpr.Congr` 等定理返回普通等式：

```lean
FuncLimitExpr.Congr :
  (∃ δ > 0, ∀ x ∈ Nbhd x₀ δ, f x = g x) →
  lim x₀ f = lim x₀ g
```

这与抽象运算法则的 `=.` 不同：最终相同不是信息近似，而是真正保持全部极限语义。

### 21.2 `gcongr` 支持局部变换

领域运算的单调性允许规则在更大表达式内部应用。例如 `lim_add` 可以把嵌套位置中的：

```lean
lim x₀ (f + g)
```

替换为：

```lean
lim x₀ f + lim x₀ g
```

而周围可能还有加法、取负、减法或逆运算。其底层依赖 `GCongr.lean` 注册的规则。

### 21.3 复合函数桥接

`FuncLimitExpr.CompSV` 展示了表达式定理如何转回具体命题、应用命题层定理，再转换回表达式关系：

```lean
theorem FuncLimitExpr.CompSV
    (h_u₀ : lim x₀ g =. the u₀)
    (h_f_cont : lim u₀ f =. the (f u₀)) :
    lim x₀ (f ∘ g) =. the (f u₀)
```

证明流程为：

1. 用 `FuncLimit.fromFuncLimitExpr` 得到 `g` 的具体极限；
2. 用同一桥得到 `f` 在 `u₀` 的具体连续性所需极限；
3. 应用命题层复合定理；
4. 用 `FuncLimit.toFuncLimitExpr` 返回表达式层。

这种“表达式层计算，命题层证明，桥接层运输”的模式可复用于其他计算任务。

## 22. 导数乘法法则：`=?`、proper 反射与 `poly_rw` 的完整协作

`Differential/Expr.lean` 把导数表达式定义为差商的极限表达式，因此直接复用 `LimitValue` 和整套 `PolyCalc` 设施。导数乘法法则写成：

```lean
theorem DerivExpr.Mul :
  D (f * g) x₀ =?
    D f x₀ * the (g x₀) +
    D g x₀ * the (f x₀)
```

这段证明集中展示了模块的设计目的。

### 22.1 引入最终结果 proper 性

因为目标是 `=?`，证明首先执行：

```lean
intro h_proper
```

此时 `h_proper` 表示整个乘法法则右式是有限值。

### 22.2 反射得到子导数 proper

证明需要从 `D f x₀` 有限推出 `f` 连续，因此先写：

```lean
script_proper_reflect D f x₀ as h_finite (source := h_proper)
```

类型类搜索沿右式的加法和乘法结构逆向传播，得到 `D f x₀` proper。

### 22.3 用 `=.` 进行表达式计算

证明把差商代数变形后，使用 `lim_add`、`lim_smul` 和 `lim_mul` 得到一串 `=.`：

```lean
calc
  ...
  _ =. ... := by lim_add
  _ =. ... := by lim_smul
  _ =. ... := by lim_mul
```

每一步允许抽象计算降低精度。

### 22.4 在 proper 端点恢复普通等式

由 `h_finite` 可以提取：

```lean
h_finite.getEqual : ∃ a, D f x₀ =. the a
```

再由导数有限推出连续性表达式：

```lean
DerivExpr.toCont h_finite.getEqual
```

其结论右端是有限值，所以最后使用：

```lean
poly_rw [DerivExpr.toCont h_finite.getEqual]
```

把 `lim x₀` f 精确重写成 `the (f x₀)`。

完整模式可以概括为：

```text
最终右式 proper
    ↓ script_proper_reflect
所需子表达式 proper
    ↓ 领域定理
得到指向 proper 值的 =.
    ↓ poly_rw / eq_of_proper
普通等式重写
```

除法法则和链式法则也采用同一模式，并展示了额外 side condition 可能仍需领域专用分析。例如导数除法法则需要从最终商 proper 推出 `g x₀ ≠ 0`，当前实现通过显式分类证明，而不是由通用 `AutoProperReflect` 自动产生。

## 23. 构造一个新的 PolyCalc 计算系统

下面给出推荐的完整实现步骤。假设新领域的结果类型为 `Value`。

### 第一步：定义结果类型

结果类型应表达对该计算任务有意义的观察，而不是用任意占位值掩盖失败：

```lean
inductive Value
  | exact (x : α)
  | coarse ...
  | failure ...
  | unknown
```

需要先明确每个构造子的语义和精度方向。

### 第二步：定义一步退化关系

```lean
inductive ValueFallbackCore : Value → Value → Prop
  | ...
```

只放领域特有的基本边；无需加入自反、传递或任意值到 unknown 的边。

### 第三步：安装 `PolyCalc` 实例

```lean
instance : PolyCalc Value where
  fallbackCore := ValueFallbackCore
  unknown := .unknown
```

此时自动获得 `=.`, `pe_unknown`, `pe_of_fallbackCore` 和混合 `calc` 支持。

### 第四步：给出精度关系的直接刻画

推荐定义一个可模式匹配或易于化简的关系：

```lean
def Value.LessPreciseThan : Value → Value → Prop := ...

theorem Value.polyEq_iff_lessPreciseThan :
  A =. B ↔ Value.LessPreciseThan A B := ...
```

这不是框架强制要求，但通常会显著简化后续证明。

### 第五步：定义 proper 值并证明刚性

```lean
def Value.isProper : Value → Prop
  | .exact _ => True
  | _ => False

instance : ProperClass Value where
  isProper := Value.isProper
  rigid := ...
```

这里是整个系统最重要的健全性义务：任何以 proper 值结束的退化路径都必须是普通等式。

### 第六步：定义抽象运算

按领域需要安装 `Add`、`Mul` 或自定义运算。无法确定结果时可以返回保守值，如 `unknown`，以保持运算总函数化。

每个运算表都应从语义上检查：返回值是否确实覆盖所有可能情况，尤其是零、无穷、错误状态或未定义分支。

### 第七步：证明运算保持 `=.`

为希望支持上下文变换的运算证明单调性：

```lean
@[gcongr] theorem op_congr :
  A =. A' → B =. B' → op A B =. op A' B' := ...
```

可以像 `Limit.Expr.GCongr` 一样将定理设为 private，只通过属性暴露给 tactic。

### 第八步：证明 proper 逆向性质

分析哪些复合结果 proper 会强制哪些参数 proper：

```lean
private theorem op_left_proper :
  isProper (op A B) → isProper A := ...
```

然后注册递归实例：

```lean
instance [AutoProperReflect A C cond] :
    AutoProperReflect (op A B) C cond := ...
```

不要为不成立的参数机械注册实例。若逆向性质需要非零、正性等附加条件，应放进 `cond`，或使用领域专用引理显式提取。

### 第九步：建立计算语义与桥接定理

定义从具体数学命题到抽象值的分类器，并证明一个统一表示定理。`Limit.Expr` 中对应的是：

```lean
GenericExpr
GenericExprSem
GenericExprBridge
```

尽量先证明统一桥，再从它派生面向用户的 `toExpr`/`fromExpr` 定理，避免每种结果重复展开分类器。

### 第十步：设计领域法则的关系强度

选择结论时应区分：

- 完全保持语义，使用普通 `=`；
- 计算可能降低精度，使用 `=.`；
- 只在符号右式 proper 时可靠，使用 `=?`。

这是使用 `PolyCalc` 时最重要的 API 设计判断。

### 第十一步：补充自动化与测试

至少测试以下行为：

- 每条 core fallback 和预期的传递路径；
- 不应成立的反向 fallback；
- proper 端点的刚性；
- 混合 `=`、`=.`、`=?` 的 `calc`；
- `gcongr` 在嵌套表达式中的传播；
- `script_proper_reflect` 的左右分支和深层路径；
- `poly_rw` 的正向、反向和多规则重写；
- 非 proper 右端不能被 `poly_rw` 错误重写；
- 抽象运算的不定分支确实返回保守结果。

## 24. 一个最小骨架

下面的代码集中展示新领域的基本形状。证明部分留作领域实现者填写：

```lean
import «Calculus_21».PolyCalc

inductive MyValue
  | exact (n : Nat)
  | coarse
  | unknown

inductive MyFallbackCore : MyValue → MyValue → Prop
  | exact_coarse (n) : MyFallbackCore (.exact n) .coarse

instance : PolyCalc MyValue where
  fallbackCore := MyFallbackCore
  unknown := .unknown

def MyValue.isProper : MyValue → Prop
  | .exact _ => True
  | _ => False

instance : ProperClass MyValue where
  isProper := MyValue.isProper
  rigid := by
    intro a b hab hb
    -- 分析 hab，并利用 b proper 排除非平凡退化。
    sorry

example (n : Nat) :
    MyValue.exact n =. MyValue.coarse :=
  PolyCalc.pe_of_fallbackCore (.exact_coarse n)

example (v : MyValue) :
    v =. MyValue.unknown :=
  PolyCalc.pe_unknown v
```

该例中 `exact n` proper，而 `coarse` 和 `unknown` 不 proper。因而指向 `exact n` 的 `=.` 可以恢复为普通等式，指向 `coarse` 或 `unknown` 的关系则不能用于 `poly_rw`。

## 25. 常见误区

### 25.1 把 `=.` 当成对称等式

`=.` 的默认语义是定向信息退化。若需要反向关系，必须单独证明，不能使用普通等式的对称性直觉。

### 25.2 认为 `unknown =. A` 总成立

框架提供的是：

```lean
A =. unknown
```

而不是反方向。`unknown` 通常是最不精确的终点。

### 25.3 认为 `=?` 已经给出 `=.`

`A =? B` 是一个函数，仍需 `isProper B` 才能得到 `A =. B`。当 `B` 不 proper 时它可能空真。

### 25.4 用 `poly_rw` 重写非 proper 端点

`poly_rw` 的 soundness 来自 `eq_of_proper`。例如极限域中的 `pos_infty`、`infty`、`diverg` 和 `unknown` 都不 proper，不能因为存在 `A =. infty` 就把 `A` 当作等于 `infty` 任意重写。

### 25.5 认为定义运算后自动获得同余

Lean 的 `Add` 或自定义运算实例只给出函数，不会自动证明它保持 `=.`。必须单独提供单调性或 `@[gcongr]` 定理。

### 25.6 为所有运算参数盲目注册 proper 反射

从结果 proper 反推参数 proper 是领域相关命题，可能因吸收元、逆运算或错误折叠而失败。`LimitValue` 对除法的保守处理就是例子。

### 25.7 假设自动化会解决任意 side condition

当前 `script_proper_reflect` 和 `poly_rw` 都使用 `by trivial`。非平凡条件需要显式证明，或先调用底层引理再使用普通 tactic。

### 25.8 直接依赖 private 定理名

自反、传递及 `LimitValue` 的 `gcongr` 定理中有多项 private 声明。稳定用法是依赖 `rfl`、`calc`、`gcongr` 和公开 API，而不是生成的内部名字。

## 26. 当前实现边界

阅读和扩展当前仓库时还应注意：

- `PolyCalc` 当前只提供精度关系的生成式定义，没有标准 `Preorder` 实例或 concretization 接口；
- 运算健全性、单调性和 proper 逆向分析没有统一记录在一个 transformer 结构中；
- `AutoProperReflect` 只能返回一个 proper 结论，不能自然收集除数非零等多项附加事实；
- `Limit.Expr.BasicRules` 和 `Limit.Expr.Elementary` 中仍有不少定理使用 `sorry`，它们展示了预期 API，但证明尚未全部完成；
- 仓库部分测试保留了旧命名或旧宏语法。当前权威接口以 `Calculus_21/PolyCalc/*.lean` 和生产代码中的用法为准；
- 当前 `script_proper_reflect` 语法是 `script_proper_reflect target as h (source := source)`，不是旧式的 `script_proper_reflect target from source as h`；
- 当前公开名称位于根命名空间，如 `PolyCalc.pe_unknown`、`ProperClass` 和 `AutoProperReflect`，不是旧的 `Expr.*` 名称。

这些边界不影响理解核心设计，但在编写新代码和示例时应避免引用过时 API。

## 27. API 速查

### 27.1 核心定义

```lean
PolyCalc
PolyCalc.FallbackStep
PolyCalc.PolyEq
ProperClass
EqualIfProper
```

### 27.2 记号

```lean
A =. B   -- A 可以安全退化到 B
A =? B   -- B proper 时，A =. B
```

### 27.3 `=.` 构造与消去

```lean
PolyCalc.pe_unknown
PolyCalc.pe_of_fallbackCore
PolyCalc.pe_of_eq
PolyCalc.PolyEq.eq_of_proper
```

### 27.4 proper 自动化

```lean
AutoProperReflect
autoProperReflect
autoProperReflectTo
script_proper_reflect target as h (source := source)
```

### 27.5 重写

```lean
poly_rw [h]
poly_rw [← h]
poly_rw [h₁, h₂] at location
```

### 27.6 `LimitValue` 关键定理

```lean
LimitValue.polyEq_iff_lessPreciseThan
LimitValue.finite_iff
LimitValue.isProper.getEqual
LimitValue.isProper.getEqual!
GenericExprBridge
```

## 28. 总结

`PolyCalc` 的核心不是一种新的相等关系，而是一套面向多精度表达式计算的证明协议：

- `PolyCalc` 定义领域特有的信息退化边和统一 unknown；
- `=.` 是这些边的自反传递闭包，方向从更精确到更不精确；
- `ProperClass` 指定不能通过非平凡退化到达的刚性结果；
- `=?` 把计算规则的有效性延迟到右式 proper 时；
- `AutoProperReflect` 从复合结果 proper 逆向恢复必要的子结果 proper 性；
- `poly_rw` 只在刚性保证下把 `=.` 转换为普通等式；
- 具体领域负责定义抽象运算、证明关于 `=.` 的单调性、提供 proper 反射，并建立抽象结果与数学语义之间的桥。

`Limit.Expr` 说明了这些组件如何组合成一套实际可用的计算系统：`LimitValue` 承载多态结果，fallback 图表达精度层级，`GenericExprBridge` 连接具体极限命题，`gcongr` 负责正向精度传播，`script_proper_reflect` 和 `poly_rw` 则在最终要求有限精确结果时恢复普通数学推理。对新的导数、积分、渐近或其他符号计算系统，最值得复用的正是这一分层方法。
