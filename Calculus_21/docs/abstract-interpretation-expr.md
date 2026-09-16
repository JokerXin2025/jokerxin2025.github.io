# 从抽象解释看表达式计算系统

本文讨论 `Calculus_21/Expr/` 与 `Calculus_21/Limit/Expr/Init.lean` 所展示的表达式计算架构，并尝试回答一个工程问题：如何把这套“不引入垃圾值、不在每一步暴露 side condition、支持多态结果与 `EqualIfProper`”的机制，稳定地推广到极限以外的计算任务，同时减少手写桥接引理、分类引理和 proper 传播引理。

这里的目标不是把库改写成传统程序分析器，也不是强行要求一个完整的 Galois connection。更合适的方向是：把当前隐含的抽象域、精度序、具体化关系和抽象转移函数显式封装，再让通用定理和自动化从这些结构中派生出来。

## 1. 当前架构的抽象解释读法

### 1.1 `LimitValue` 是结果的抽象域

`LimitValue` 将极限可能表现出的语义分类压缩为有限表示：

```lean
inductive LimitValue where
| finite : ℝ → LimitValue
| unknown
| posInfty
| negInfty
| unsignedInfty
| divergence
```

它不是把所有情况塞进一个带错误值的具体数值类型。每个构造子都表达一个有数学意义的观察结果：

| 抽象值 | 可理解为 |
| --- | --- |
| `finite a` | 唯一的有限结果 `a` |
| `posInfty` | 正无穷 |
| `negInfty` | 负无穷 |
| `unsignedInfty` | 无穷，但符号未知 |
| `divergence` | 不收敛，但原因或形态未知 |
| `unknown` | 当前抽象无法给出更多信息 |

因此 `unknown` 不是垃圾值，而是抽象域的顶元素；`divergence` 也不是运算失败，而是比 `unknown` 更精确的语义事实。

### 1.2 `PolyEqual` 实际上是精度关系

`LimitFallbackCore` 给出基本的信息遗忘边：

```text
finite a  ───────────────→ unknown
posInfty  → unsignedInfty → divergence → unknown
negInfty  → unsignedInfty → divergence → unknown
```

`PolyEqual` 是这些边的自反传递闭包。于是

```lean
A =. B
```

更准确的含义不是“`A` 与 `B` 相等”，而是：

> `A` 至少和 `B` 一样精确；或者，`A` 可以安全退化为 `B`。

若记精度序为 `A ⊑ B`，其中左边更精确、右边更抽象，那么当前 `A =. B` 正对应 `A ⊑ B`。例如：

```text
posInfty ⊑ unsignedInfty ⊑ divergence ⊑ unknown
```

这个方向与常见抽象解释文献中“集合包含越大越不精确”的方向一致：若 `γ` 是 concretization，则应有

```text
A ⊑ B  →  γ(A) ⊆ γ(B).
```

名称 `PolyEqual` 对用户书写 `calc` 很友好，但内核设计中最好同时显式承认它是一个 preorder/precision relation。否则分类、单调性和 proper 传播都只能从 `ReflTransGen` 的路径结构反复手工恢复。

### 1.3 运算实例是抽象转移函数

`Add LimitValue`、`Mul LimitValue`、`Inv LimitValue` 等实例把抽象输入映射到抽象输出。例如：

```lean
finite a * posInfty =
  if a > 0 then posInfty
  else if a < 0 then negInfty
  else unknown
```

这正是抽象解释中的 abstract transformer。返回 `unknown` 表示当前抽象信息不足以唯一决定更精确的结果，而不是在逻辑上偷偷选择一个任意值。

当前规则的主要优点是总函数化：计算链可以继续，而 side condition 被推迟到最终需要精确结论的位置。主要缺口是，每个运算的健全性、单调性、proper 逆向传播性质还没有由统一接口记录。

### 1.4 `genericExpr` 是语义分类器

`genericExpr C P N U evC` 依次检查有限、正无穷、负无穷、无符号无穷等语义谓词，并构造相应抽象值。`SeqLimitExpr`、`FuncLimitExpr` 等只是在替换这些谓词。

从抽象解释角度看，它接近一个 abstraction/classification 函数：将一个计算任务的具体语义事实映射到 `LimitValue`。`GenericExprLaws` 则证明这些语义类别之间满足抽象域所要求的互斥和蕴含关系。

不过，当前分类器和抽象域是按构造子位置硬编码耦合的。于是每增加一种任务，就需要：

- 构造一组 `GenericExprLaws`；
- 手写每个具体语义谓词与 `=. finite/posInfty/...` 之间的桥；
- 为不同 domain 包装重复做正反向转换；
- 在使用运算时继续补 proper 反射引理。

### 1.5 `ProperClass` 与 `EqualIfProper` 表达 singleton 精确性

对 `LimitValue`，proper 值就是 `finite a`。`ProperClass.eq_of_proper` 表明：

```text
A ⊑ B 且 B proper  →  A = B.
```

这是一个很强的抽象域性质：proper 元素没有比自己更精确但不同的表示。若使用 concretization，可将 proper 理解为 singleton 抽象值，并要求 singleton 表示规范或可分离。

`A =? B` 定义为：

```lean
isProper B → A =. B
```

其数学含义可以读为：

> 只要右式确实落在需要的精确区域，当前计算规则就给出足够精确的结论。

因此 `EqualIfProper` 很适合保留为面向用户的证明接口。优化重点不应是删除它，而应是让 `isProper B` 的生成、分解和最终消去来自抽象域的一般理论，而不是每个运算手写一个 `AutoProperReflect_*`。

## 2. 当前重复劳动的根源

### 2.1 精度关系只有生成路径，没有语义接口

`PolyEqual` 被定义为 `fallbackCore` 的自反传递闭包。这适合快速添加退化边，也让 `poly_fallback` 能做有限搜索，但它没有直接提供：

- preorder 实例；
- 与 concretization 的对应；
- 构造子的下闭包或 principal ideal；
- 可判定的精度比较；
- 运算关于精度序的单调性。

因此 `finite_classify`、`posInfty_classify`、`unsignedInfty_classify`、`divergence_classify` 都在手工分析同一张有限图。抽象域一旦扩展，这些证明也要同步修改。

### 2.2 具体语义按多个布尔谓词展开

`genericExpr` 使用 `C P N U` 四个命题和一组关系定律描述语义。这个设计对极限足够直接，但它不是可扩展的通用计算接口：

- 类别数量固定在函数参数中；
- 类别蕴含关系通过专用字段编码；
- 优先级由嵌套 `if` 隐式决定；
- 分类完备性和唯一性没有成为统一结构；
- `evC : C → ℝ` 将“精确结果携带数据”作为特例处理。

这导致 `GenericExprLaws` 更像 `LimitValue` 的一次性适配器，而不是任意表达式系统可复用的基础设施。

### 2.3 桥接定理没有从一个表示定理生成

当前 `toXExpr`/`fromXExpr` 桥本质上都在证明两件事：

```text
具体语义关系成立  ↔  表达式结果精确到某抽象观察值。
```

有限结果还额外依赖唯一性。若先建立一个统一表示定理，例如

```text
Sem task result ↔ denotes (eval task) result
```

或更一般的

```text
Sem task concrete → concrete ∈ γ (eval task),
```

则大部分桥接引理应成为一两行的投影或 `simpa`，而不是每种极限方向分别展开 `genericExpr`。

### 2.4 proper 反射由表达式语法路径驱动，而非抽象语义驱动

`AutoProperReflect A B` 表示“根表达式 proper 可推出子表达式 proper”。目前加、乘、负、减、除分别注册实例。这种做法有两个问题：

- 实例数量随运算和参数位置相乘；
- 某些逆向性质依赖额外事实，例如除法结果 finite 不仅要求分子 finite，还要求分母对应的实数非零。

严格说，proper 逆向传播不是普通的单调性，而是抽象转移函数关于某个观察谓词的 backward transformer。只用一个 `Prop → Prop` 类型类路径无法自然返回额外约束，因此最终仍会出现专门的 `isProper_div_finite` 一类引理。

### 2.5 一个枚举同时承载多个分析维度

`LimitValue` 同时编码：

- 是否有限；
- 若有限，精确实数值；
- 是否无穷；
- 无穷的符号；
- 是否发散；
- 是否完全未知。

这在早期很实用，但随着任务扩展，枚举的笛卡尔爆炸会出现。例如以后若还要记录趋近方向、振荡、定义域条件、符号区间或可导阶数，把所有组合都加入同一 inductive 会使运算表和分类引理迅速膨胀。

## 3. 建议的核心抽象：带 concretization 的精度域

建议新增一个比 `PolyExpr` 更有语义的信息域接口。以下代码是设计草图，不要求逐字采用。

```lean
class AbstractDomain (A : Type u) (C : outParam (Type v)) where
  le : A → A → Prop
  le_refl : Reflexive le
  le_trans : Transitive le
  gamma : A → Set C
  gamma_mono : ∀ {a b}, le a b → gamma a ⊆ gamma b
```

可以继续保留 `=.` 记号，并令它指向 `AbstractDomain.le`；也可以暂时让现有 `PolyEqual` 实现 `le`，以降低迁移成本。

这里不应一开始就强制完整格结构。当前主要需求是有限精度序、具体化及其单调性。只有在确实需要合并分支、循环不动点或多分析组合时，再增加 `JoinSemilattice`、widening 等结构。

### 3.1 为 `LimitValue` 定义 concretization

关键选择是“具体域”是什么。对极限计算，单纯使用 `ℝ` 不够，因为正负无穷和发散也是有意义的具体观察。可以定义一个不含 `unknown` 的语义结果类型：

```lean
inductive LimitOutcome where
| finite : ℝ → LimitOutcome
| posInfty
| negInfty
| oscillatoryOrOtherDivergence
```

然后给出：

```text
γ(finite a)       = {finite a}
γ(posInfty)       = {posInfty}
γ(negInfty)       = {negInfty}
γ(unsignedInfty)  = {posInfty, negInfty}
γ(divergence)     = 所有非有限 outcome
γ(unknown)        = 所有 outcome
```

这里有一个需要明确的数学决策：当前 `divergence` 由 `unsignedInfty` 退化而来，因此它必须包含无符号无穷的两种可能；但它是否只表示“不收敛”，以及 `unknown` 是否允许“语义未定义”，都应在 `LimitOutcome` 中明确，而不要仅由构造子名称暗示。

一旦 `γ` 被定义，当前 fallback 图的正确性就化为每条边的集合包含，`PolyEqual.map` 之外还能得到统一的 `gamma_mono`。

### 3.2 proper 应由 concretization 的精确性解释

建议将 `ProperClass` 的语义拆为两个概念：

```lean
def IsSingleton (a : A) : Prop := ∃ c, gamma a = {c}

class ProperDomain (A C) [AbstractDomain A C] where
  isProper : A → Prop
  proper_singleton : isProper a → ∃ c, gamma a = {c}
  proper_rigid : a ≤ b → isProper b → a = b
```

如果不同抽象表示可能对应同一 singleton，则 `proper_rigid` 太强，应改成语义等价；当前系统依赖真正的 Lean 等式做 rewrite，因此 `LimitValue` 最好保持 proper 表示规范化，使 rigid 性成立。

`ProperClass` 可以作为兼容层继续暴露：

```lean
instance [ProperDomain A C] : ProperClass A (· ≤ ·) := ...
```

如此 `EqualIfProper`、现有 `calc` 风格和 `poly_rw` 均可保留。

### 3.3 从有限 poset 自动生成分类结论

若抽象域可判定且有限，应提供：

```lean
class FiniteAbstractDomain (A C) extends AbstractDomain A C where
  decLe : DecidableRel le
  finite : Fintype A
```

但 `LimitValue` 含任意 `ℝ`，整体不是有限类型。更实用的结构是“有限形状 + payload”：

```lean
inductive LimitShape where
| finite | posInfty | negInfty | unsignedInfty | divergence | unknown

def shape : LimitValue → LimitShape
```

对 payload 构造子单独声明注入性和原子性，对有限 shape 图自动计算下闭包。目标是让以下事实由通用定理或 `decide` 得到：

```text
x ≤ finite a       → x = finite a
x ≤ posInfty       → x = posInfty
x ≤ unsignedInfty  → x = posInfty ∨ x = negInfty ∨ x = unsignedInfty
```

这样 `*_classify` 不再逐个手写。实现路径有三种：

1. 直接定义可判定的 `LimitValue.le`，证明它与旧 `PolyEqual` 等价。
2. 保留生成关系，用元编程读取无 payload 的构造图并生成分类定理。
3. 将 shape order 定义成 `Finset LimitShape` 的 membership，再把 payload 情况单独提升。

建议优先采用第 1 种。`LimitValue` 很小，直接模式匹配定义 `le` 通常比在核心 API 中长期暴露 `ReflTransGen` 更稳定；原来的 `LimitFallbackCore` 可以保留为便捷的生成证明，并证明 `fallbackCore a b → a ≤ b`。

## 4. 把计算任务与抽象域解耦

### 4.1 用统一语义关系替代固定的 `C P N U`

任意计算任务可抽象为：

```lean
class AbstractComputation (Task : Type u) (Concrete : Type v) (A : Type w)
    [AbstractDomain A Concrete] where
  sem : Task → Concrete → Prop
  eval : Task → A
  sound : ∀ {t c}, sem t c → c ∈ gamma (eval t)
```

这给出最基本的健全性：所有真实结果都被抽象结果覆盖。

若任务的数学语义保证唯一结果，可增加：

```lean
class FunctionalSemantics ... where
  sem_unique : sem t x → sem t y → x = y
```

若希望从抽象 singleton 反推出原始关系，还需 completeness/realization：

```lean
class ExactComputation ... extends AbstractComputation ... where
  complete : ∀ {t c}, gamma (eval t) = {c} → sem t c
```

实际字段可以按各任务的语义调整，但原则是只证明一次总表示定理，然后派生所有桥。

### 4.2 极限的桥接可由 membership 定理派生

例如把各类极限统一为 `LimitOutcome` 后，可以定义：

```lean
def FuncLimitSem (f x₀) : LimitOutcome → Prop
| .finite L => FuncLimit ... x₀ L
| .posInfty => FuncLimitPosInfty ... x₀
| .negInfty => FuncLimitNegInfty ... x₀
| .oscillatoryOrOtherDivergence => ...
```

然后只为 `FuncLimitExpr` 证明一次：

```lean
theorem funcLimitExpr_spec :
  FuncLimitSem f x₀ o ↔ o ∈ gamma (FuncLimitExpr f x₀)
```

现有桥可统一派生：

```lean
FuncLimit ... L              ↔ finite L ∈ γ (lim f x₀)
FuncLimitPosInfty ...        ↔ posInfty ∈ γ (lim f x₀)
FuncLimitInfty ...           ↔ γ (lim f x₀) ⊆ {posInfty, negInfty}
¬ FuncConvergesAt ...        ↔ γ (lim f x₀) ⊆ nonFinite
```

需要注意：`A =. unsignedInfty` 表示 `A` 比 `unsignedInfty` 精确，语义上对应 `γ(A) ⊆ γ(unsignedInfty)`，而不是某个具体 outcome 属于 `γ(A)`。因此桥接 API 应明确区分两种查询：

- `c ∈ γ(A)`：某个具体结果与抽象结果相容；
- `A ≤ observation`：抽象结果足以证明某个观察性质。

当前 `=. infty`、`=. diverg` 主要属于第二类。这一差别是设计通用接口时最重要的细节之一。

### 4.3 用 observation 表述用户查询

可以把“有限”“正无穷”“不收敛”等视为对 concrete outcome 的性质：

```lean
def Proves (a : A) (P : C → Prop) : Prop :=
  ∀ c ∈ gamma a, P c
```

若某个抽象值 `obs` 恰好满足 `gamma obs = {c | P c}`，则：

```text
a ≤ obs  ↔  Proves a P
```

于是 `=. infty` 和 `=. diverg` 不再依赖专门分类引理，而是通用的抽象断言。对新任务，只需定义 outcome 与 observation，不必重建一套 `generic_*_iff`。

## 5. 抽象运算：从运算表提升为已验证 transformer

### 5.1 每个运算至少记录健全性和单调性

对二元运算建议采用类似接口：

```lean
structure SoundBinaryOp (A C : Type*) [AbstractDomain A C] where
  concrete : C → C → Set C
  abstract : A → A → A
  sound : ∀ {a b x y z},
    x ∈ gamma a → y ∈ gamma b → z ∈ concrete x y →
    z ∈ gamma (abstract a b)
  monotone : Monotone₂ abstract
```

这里 concrete 使用关系或 `Set C`，而不必是总函数。这一点保留了当前“不造垃圾具体值”的理念：例如 `0 * ∞` 可以在具体语义层面没有唯一运算结果，抽象 transformer 仍然总是返回安全近似 `unknown`。

如果某运算在 concrete outcome 上确实是总函数，可提供简化版本。

### 5.2 最佳抽象与仅健全抽象应分开

抽象解释区分：

- sound：结果不会遗漏真实可能性；
- complete/best：在当前抽象域中已经尽可能精确。

当前运算表有些分支可能是最佳抽象，有些只是保守返回 `unknown`。接口不应要求所有运算一开始就证明最佳性，否则会提高扩展成本。建议分层：

```lean
class SoundOp ...
class BestOp extends SoundOp ...
```

计算系统的可靠性只依赖 sound；化简质量、分类能力和 `EqualIfProper` 的可用性则受 best/complete 性影响。

### 5.3 从 transformer 的 preimage 自动生成 proper 反射

对抽象运算 `op#`，根结果 proper 时需要知道输入满足什么条件。抽象解释中这是 backward analysis：

```text
preProper_op(a, b) 近似描述 IsProper(op# a b) 的必要条件。
```

建议不要继续为每个参数位置直接声明 `AutoProperReflect`，而是给运算提供一个统一的逆向规格：

```lean
class ProperBackward₂ (op : A → A → A) where
  pre : A → A → Prop
  necessary : IsProper (op a b) → pre a b
```

例如：

```text
pre_add a b       = IsProper a ∧ IsProper b
pre_mul a b       = IsProper a ∧ IsProper b
pre_divFinite a b = IsProper a ∧ b ≠ 0
```

然后自动化递归分解 `pre`，既得到子表达式 proper，也保留 `b ≠ 0` 这类额外事实。相比 `AutoProperReflect A target`，这种接口不会把有用 side condition 丢掉。

对构造有限且运算可计算的抽象域，`pre` 甚至可由枚举/符号化求 preimage 自动生成：找出所有使 `op a b` proper 的输入 shape，再化简成命题。对带 `ℝ` payload 的分支，仍需用户提供算术判别条件，但只需在运算定义处提供一次。

### 5.4 正向精度传播由单调性统一处理

如果有 `a₁ ≤ a₂` 与 `b₁ ≤ b₂`，单调性自动给出：

```text
op# a₁ b₁ ≤ op# a₂ b₂.
```

这可替代未来大量“把 `=.` 放进上下文”的 congruence 引理，也能使 `gcongr` 或专用 tactic 直接工作。当前 `PolyEqual.map` 只处理一元映射且要求逐步证明 preservation；将单调性作为运算接口后，复合表达式的精度证明可由类型类自动合成。

## 6. `EqualIfProper` 的一般化与保留方式

### 6.1 保持当前表面语法

当前定义简洁且实用：

```lean
def EqualIfProper (A B : ExprValue) : Prop :=
  isProper B → A =. B
```

建议保留 `=?`。它解决的是 API 表述问题：某公式只在右式为 ordinary/proper value 时声称精确，而不要求调用者在应用定理前显式携带 side condition。

### 6.2 在内核中解释为条件完备性

若 `≤` 是精度序，则 `A =? B` 是：

```text
IsProper(B) → A ≤ B.
```

结合 proper rigid 性可得 `A = B`。因此 `EqualIfProper` 不需要自己的复杂理论，它应由以下三件事支撑：

- 抽象域的 precision preorder；
- proper/singleton 的规范性；
- backward transformer 自动产生右式 proper 所蕴含的事实。

### 6.3 可考虑更通用的 `ExactUnder`

对于新任务，“proper”未必只有一个概念。例如区间计算可能关心 singleton interval，符号计算可能关心非零，矩阵计算可能关心可逆。可增加一般形式：

```lean
def ExactUnder (Q : A → Prop) (lhs rhs : A) : Prop :=
  Q rhs → lhs ≤ rhs
```

并令：

```lean
EqualIfProper := ExactUnder isProper
```

这使同一计算架构可以表达：

- `EqualIfFinite`；
- `EqualIfNonzero`；
- `EqualIfDefined`；
- `EqualIfInvertible`。

但不要立即用大量新记号替换 `=?`。先在内核中提供一般定义，用户层继续保持当前接口即可。

## 7. 用归约积避免抽象值枚举膨胀

当系统扩展到更多计算任务时，最值得借鉴的抽象解释技术不是 widening，而是 reduced product。

### 7.1 将独立信息拆成小域

例如极限结果可以拆成：

- `FinitenessDomain`：finite / nonfinite / top；
- `InfinitySignDomain`：positive / negative / either / notInfinity / top；
- `ExactRealDomain`：exact `a` / top；
- `ConvergenceDomain`：convergent / divergent / top。

朴素乘积会包含不一致组合，例如“finite 且 positive infinity”。归约函数 `reduce` 消除这些组合并传播信息：

```text
exact a          ⇒ finite, convergent, notInfinity
positiveInfinity ⇒ nonfinite, divergent
finite ∧ nonfinite ⇒ bottom/inconsistent
```

### 7.2 是否需要 bottom

当前 `LimitValue` 没有 bottom，因为表达式计算返回的都是可实现或保守的结果。引入归约积后，内部约束传播可能产生不可能组合，此时 bottom 很有用。

但 bottom 不应作为用户可见的“垃圾计算结果”。建议：

- 内部分析域允许 `⊥` 表示无 concrete outcome；
- 顶层已验证 evaluator 证明其结果非 bottom；
- 公共表达式 API 可继续隐藏 bottom，或把它解释为假设不一致而非运行错误。

这保持“不使用垃圾值”的设计目标，同时允许标准格论工具工作。

### 7.3 归约积最适合渐进式扩展

新计算任务可以复用已有域：

- 导数计算复用 limit outcome，再增加 differentiability/continuity 信息；
- 定积分复用 exact real、definedness、integrability；
- 不定积分增加 quotient representative 与 existence 信息；
- 方程求解增加解集基数、区间和符号信息；
- 渐近阶计算增加 growth-rate domain。

每个 primitive operation 只声明自己影响的分量，通用 reduction 负责跨分量传播。这比为每个任务新造一个 `FooValue` 大枚举更稳定。

## 8. 自动生成分类和桥接的两条路线

### 8.1 纯 Lean 结构化路线

这是优先建议的路线。核心做法是：

1. 定义显式 `≤` 与 `γ`。
2. 为 observation 证明 `gamma obs = {x | P x}`。
3. 提供通用定理 `a ≤ obs ↔ Proves a P`。
4. 每个计算任务只证明一个 `eval_spec`。
5. 用 `simpa` 从 `eval_spec` 和 observation 定理得到桥接 API。

优点是 kernel-visible、错误信息稳定、不依赖声明命名约定。缺点是初次重构工作较多。

### 8.2 Deriving/元编程路线

如果大量抽象域仍以 inductive + fallback graph 表达，可以写命令自动生成：

- 自反传递闭包的 preorder 实例；
- 每个 constructor 的 classify theorem；
- `unknown_always`；
- shape-level `DecidableRel`；
- 简单运算的 proper preimage 定理。

例如概念上：

```lean
deriving abstract_domain for LimitValue using LimitFallbackCore
```

元编程路线适合减少模板代码，但不应替代 `γ` 和 soundness 规格。只从图生成的定理能证明“哪些构造子能走到哪里”，不能证明这些边在数学语义上是安全的。

## 9. 推荐的分层架构

建议最终形成四层，而不是让 `Expr` 同时承担所有职责。

### 9.1 Domain 层

职责：

- precision preorder；
- concretization；
- proper/singleton；
- top、可选 bottom、join；
- 有限 shape 分类；
- observation 与 `Proves`。

可能的模块：

```text
Expr/Domain/Basic.lean
Expr/Domain/Proper.lean
Expr/Domain/Observation.lean
Expr/Domain/Product.lean
```

### 9.2 Transformer 层

职责：

- 抽象一元/二元运算；
- soundness；
- monotonicity；
- 可选 best abstraction；
- proper backward specification。

可能的模块：

```text
Expr/Transformer/Basic.lean
Expr/Transformer/ProperBackward.lean
```

### 9.3 Computation 层

职责：

- task 类型；
- concrete semantic relation；
- evaluator；
- 唯一的总规格定理 `eval_spec`。

极限、导数、积分分别实现这一层，不再各自复制通用桥结构。

### 9.4 Surface 层

职责：

- `=.`、`=?` 等便于教材书写的记号；
- `calc` transitivity；
- `poly_rw`；
- 自动 proper 分解 tactic；
- 领域专用 tactic，如 `lim_add`、`lim_mul`。

这一层可以维持当前用户体验，即使内核从 `ReflTransGen` 迁移到显式 preorder。

## 10. 对现有组件的具体建议

### 10.1 `PolyExpr` / `PolyEqual`

短期：

- 为 `PolyEqual` 增加 `Preorder` 风格的标准接口或适配定理；
- 把“更精确到更抽象”的方向写入文档和命名；
- 为每个实例证明 `fallbackCore` 的 semantic soundness。

中期：

- 将主要 API 改为显式 `le`；
- 证明 `PolyEqual ↔ le`，保留 `=.` 记号；
- 避免下游直接依赖 `ReflTransGen.cases_tail`。

直接依赖路径表示是当前分类引理脆弱的首要原因。

### 10.2 `poly_fallback`

`solve_by_elim` 的 bounded search 适合当前小图，但 `maxDepth := 12` 是经验参数，域扩展后可能出现不透明失败。

建议在有 `DecidableRel le` 后，让 tactic 先规范化并执行可判定比较；只有用户自定义的 symbolic edge 才回退到 theorem search。这样失败表示“精度关系不成立”或“缺少实例”，而不是搜索深度偶然不足。

### 10.3 `ProperClass`

保留兼容接口，但将其实现建立在 `ProperDomain` 上。`eq_of_proper` 不应由每个 domain 对 fallback 路径做低层 case analysis，而应来自通用的 proper rigid 定理。

`ProperClass.isProper.getEqual` 当前命名和类型较特殊：它从 proper 抽象值提取 `∃ a, A =. finite a`。在新接口中更自然的是返回 singleton witness：

```lean
IsProper a → ∃ c, gamma a = {c}
```

极限专用版本再将 witness 转成 `ℝ`。

### 10.4 `AutoProperReflect`

短期可以保留 tactic 语法，但后端改为：

1. 识别表达式根部运算；
2. 应用该运算的 `ProperBackward` 规格；
3. 递归拆解合取和结构化约束；
4. 将非零、正性等事实留在上下文中。

这样 `DerivExpr.Div` 中对 `g x₀ ≠ 0` 的提取不再依赖一个极限域专用引理名称，而是除法 transformer 的统一 backward 结果。

### 10.5 `genericExpr` / `GenericExprLaws`

短期可把它重写为由一个分类结构驱动：

```lean
structure Classifier (Task Concrete A) where
  classify : Task → A
  spec : ...
```

中期应让 `SeqLimitExpr`、`FuncLimitExpr` 等分别证明统一 `eval_spec`，然后删除大部分 `generic_pos_iff`、`generic_neg_iff` 等手写证明。

`GenericExprLaws` 中真正领域相关的事实，例如“正无穷极限不可能有限收敛”，仍然需要数学证明；优化的目标不是消灭这些事实，而是：

- 每个事实只证明一次；
- 它们用于证明总规格，而不是在每个桥接和分类定理中反复展开；
- 能从已有层级关系自动推出的字段不再手写。

例如若 `PosInfty` 的 concrete outcome 定义本身蕴含 `UnsignedInfty` observation，则 `pos_to_infty` 应来自 observation 包含，而不是每个极限种类都注册一个字段。

### 10.6 导数与积分模块

`DerivExpr` 已通过极限表达式复用结果域，这是正确方向。它目前重复的主要是 relation-expression 桥和 domain 包装。可以把“导数是差商极限”实现为 computation morphism：

```text
DerivativeTask → LimitTask
```

再由通用的 evaluator composition 定理自动运输 soundness、bridges 和 observations。

积分模块当前使用 `Except IntegralError α`，与 `LimitValue` 的信息域风格不同。`Except` 会固定选择一个错误并丢失其他信息，也没有自然精度序。若希望统一到新系统，可考虑：

- concrete outcome：`integral value` 或带语义的失败原因；
- abstract domain：exact value、nonintegrable、undefined、unknown；
- 若多个失败原因可同时相容，使用小 powerset/错误信息域而非 `Except`；
- `Except` 仅作为确定性且错误互斥时的表面表示。

这不是必须立即迁移的部分。应先验证通用 domain/computation 接口能完整覆盖极限和导数，再决定积分的错误语义。

## 11. 一个最小原型

建议先做一个不会扰动现有 API 的实验模块。原型只需覆盖以下内容：

```lean
namespace Expr.Experimental

class Precision (A : Type u) where
  le : A → A → Prop
  refl : Reflexive le
  trans : Transitive le

class Concretization (A : Type u) (C : outParam (Type v)) [Precision A] where
  gamma : A → Set C
  mono : ∀ {a b}, Precision.le a b → gamma a ⊆ gamma b

def Proves [Precision A] [Concretization A C]
    (a : A) (P : C → Prop) : Prop :=
  ∀ c ∈ Concretization.gamma a, P c

class Proper (A : Type u) (C : outParam (Type v))
    [Precision A] [Concretization A C] where
  proper : A → Prop
  rigid : Precision.le a b → proper b → a = b

end Expr.Experimental
```

然后为 `LimitValue`：

1. 定义 `LimitOutcome` 和 `gamma`。
2. 定义直接可判定的 precision relation。
3. 证明它与 `PolyEqual` 等价。
4. 由通用定理重新证明现有五个 classify lemma。
5. 为 `Add` 和 `Mul` 证明 monotonicity 与 soundness。
6. 为 `Mul` 提供一个 proper backward 规格，并在一个导数乘法定理中替换 `AutoProperReflect`。

若这六步能显著缩短证明，接口方向基本成立；若不能，应先调整抽象层，而不是继续加入元编程。

## 12. 分阶段迁移路线

### 阶段一：显式化而不改用户 API

- 新增 experimental `Precision`、`Concretization`、`Proves`、`Proper`。
- 为 `LimitValue` 实例化。
- 证明 `A =. B ↔ Precision.le A B`。
- 用新接口重写分类引理的证明，但保留原定理名。
- 保留 `poly_fallback`、`=?` 和现有 tactic。

验收标准：下游文件无需改动，且分类证明不再直接分析 `ReflTransGen`。

### 阶段二：统一桥接规格

- 引入 `LimitOutcome` 与各类极限的统一 semantic relation。
- 每种 evaluator 只证明一个 `eval_spec`。
- 从通用 observation theorem 派生现有 `to...Expr`/`from...Expr` API。
- 将 domain 替换相关内容抽成 task morphism 或语义 congruence。

验收标准：新增一种极限方向时，不再手写有限、正无穷、负无穷、无符号无穷、发散的整套桥。

### 阶段三：验证抽象 transformer

- 为算术运算增加 soundness 和 monotonicity。
- 将 congruence 自动化接到这些实例上。
- 引入 structured proper backward 规格。
- 让 `proper_reflect` 返回所有必要条件。

验收标准：新增一个二元运算时，只在定义处证明一次规格，不再为每个参数位置手写传播实例。

### 阶段四：跨任务复用与归约积

- 选择第二个真正不同的任务验证抽象，例如定积分或方程求解。
- 识别可复用的小域，并实现一个最小 reduced product。
- 只有出现 join/分支合并需求后，再引入 lattice 和 widening。

验收标准：第二个任务主要通过组合既有 domain/transformer 建成，而不是复制 `LimitValue + GenericExprLaws`。

## 13. 不建议的方向

### 13.1 不要一开始要求完整 Galois connection

本库的 concrete semantics 多为 Prop 关系、唯一性定理和不可计算选择，未必有方便的 `α : Set C → A`。仅有 concretization、precision 和 soundness 已足以统一大部分证明。若后来能定义最佳抽象，再补 Galois insertion 即可。

### 13.2 不要把所有 side condition 塞回结果类型

`0 * ∞`、除零、幂的底数限制等条件如果全部变成 dependent result，会破坏当前密集计算的优势。更好的做法是：

- 正向 evaluator 保持总函数并返回保守抽象；
- 只在要求 proper/exact 结论时运行 backward analysis；
- backward analysis 产生结构化前置条件，交给自动化或调用者消解。

这正是当前 `EqualIfProper` 思路的系统化版本。

### 13.3 不要把 `unknown` 与异常混为一谈

`unknown` 表示信息不足，异常表示任务语义中确实存在失败。两者 concretization 不同：前者通常是 top，后者是 concrete outcome 的一个或一组真实类别。统一框架应能同时表达它们，但不能合并语义。

### 13.4 不要过早依赖复杂 tactic

如果核心结构仍不清楚，tactic 只会掩盖重复证明。优先让分类、桥接和传播成为短小的普通定理；之后再把稳定模式封装为 tactic。

## 14. 预期收益

若按上述方向演进，可以获得：

- 稳定性：下游不再依赖 fallback 路径的具体表示。
- 自动分类：由 precision order 的下闭包或 concretization 自动产生。
- 自动桥接：由每个 computation 的单一规格定理派生。
- 自动 side condition 恢复：由 backward transformer 统一生成 proper、非零、正性等条件。
- 可组合性：多个小抽象域通过 product/reduction 组合，而非枚举爆炸。
- 可验证性：每个运算明确区分 soundness、monotonicity 和 completeness。
- API 连续性：`=.`, `=?`, `poly_rw` 与现有 `calc` 风格可以继续保留。

## 15. 总结

当前表达式系统已经具备抽象解释的核心直觉：

- `LimitValue` 是抽象结果域；
- `unknown` 是 top，而非垃圾值；
- `PolyEqual` 是信息遗忘方向的精度序；
- 算术实例是抽象转移函数；
- `genericExpr` 是语义分类器；
- `ProperClass` 描述 singleton/规范精确值；
- `EqualIfProper` 表达在精确区域上的条件完备性。

真正缺少的不是更多专用引理，而是把这些隐含结构提升为一等接口。最有价值的第一步是引入 `precision + concretization + proper rigidity`，并为 `LimitValue` 证明它与当前 `PolyEqual` 的等价。随后用统一 `eval_spec` 取代成组桥接引理，用 verified transformer 取代散落的运算分类与 proper 反射，最后再通过 reduced product 支持跨任务组合。

这条路线保持现有系统最重要的优点：计算过程总函数化、无任意垃圾值、side condition 延迟出现、结果可按信息精度多态退化；同时把目前依赖人工维护的部分转化为可复用的抽象域理论和机械派生。
