# 特征约束下分类器公平性（P1–P7）完整自然语言数学证明（Rocq 对齐修订版）

> [!IMPORTANT]
> 本文档基于 5 份 **Rocq (Coq 9.0)** 源码（`rocq_proofs/verify_pi2p.v`、`verify_p1.v`、`verify_p2_p3.v`、`verify_p5.v`、`verify_p4.v`，0 `Admitted`、0 自定义公理）完整整理并修订，闭合 **Cooper & Bousdira (CP 2026)** *《Fairness of Classifiers in the Presence of Constraints Between Features》* 第 6–7 节（Propositions 27, 28, 31）遗留的全部 **7 个复杂度下界开放问题（P1–P7）**。

---

## 1. 形式化预备知识与核心定义

### 1.1 基本设定与计算模型

设布尔特征全集为 $\mathcal{F} = \{1, \dots, n\}$，划分为互不相交的**非保护特征集** $\mathcal{N}$ 与**受保护（敏感）特征集** $\mathcal{P}$（$\mathcal{F} = \mathcal{N} \cup \mathcal{P}$，$\mathcal{N} \cap \mathcal{P} = \emptyset$）。特征空间为有限布尔超立方体 $\mathbb{F} = \{0, 1\}^n$。

- **特征约束与有效实例空间**：多项式时间可判定的布尔公式/电路 $\mathcal{C} : \mathbb{F} \to \{0, 1\}$ 定义了有效实例空间 $\mathbb{F}[\mathcal{C}] = \{x \in \mathbb{F} \mid \mathcal{C}(x) = 1\}$。
- **分类器**：多项式时间可计算的布尔函数 $\kappa : \mathbb{F} \to \{0, 1\}$（遵循原论文第 7 节第 12–13 页设定）。
  - *表示强度说明*：本文对 **P1–P5** 构造的 $(\mathcal{C}, \kappa)$ 为多项式规模布尔公式/电路；对 **P6–P7** 构造的 $\mathcal{C}_{\text{red}}$ 直接是多项式规模的**纯 5-CNF 公式**，$\kappa_d$ 仅为**单特征投影分类器**（深度为 1 的决策树）。
  - *与 Rocq 有限域编码的对应*：在 Rocq 源码中，向量坐标虽采用 `nat -> bool`，但所有定理均带有 `cnf_bounded` / `dnf_bounded` 有界前提，且所有谓词仅读取有限前缀坐标，因此与有限超立方体 $\{0,1\}^N$ 严格同构。

### 1.2 解释与公平性定义（对齐 Cooper & Bousdira, CP 2026）

1. **覆盖集（Coverage，原论文 Section 2 第 3 页）**：对有效实例 $x \in \mathbb{F}[\mathcal{C}]$ 与特征子集 $S \subseteq \mathcal{F}$，定义 $S$ 在 $x$ 处的覆盖集为
   $$\text{cov}_S(x) = \{y \in \mathbb{F}[\mathcal{C}] \mid \forall i \in S,\ y_i = x_i\}.$$
2. **弱溯因解释（Weak AXp）与溯因解释（AXp，Definition 3）**：
   - $S \subseteq \mathcal{F}$ 是 $\langle \kappa, x \rangle$ 的 **Weak AXp**，若 $\forall y \in \text{cov}_S(x),\ \kappa(y) = \kappa(x)$。
   - $S \subseteq \mathcal{F}$ 是 **AXp**，若 $S$ 是关于集合包含关系 $\subseteq$ 极小的 Weak AXp。
3. **严格包含与主蕴涵解释（PI-explanation，Definition 4）**：
   - 称 $T \subseteq \mathcal{F}$ 在 $x$ 处**严格包含（strictly subsumes）** $S \subseteq \mathcal{F}$，记作 $\text{cov}_S(x) \subsetneq \text{cov}_T(x)$，若 $\text{cov}_S(x) \subseteq \text{cov}_T(x)$ 且存在 $v \in \text{cov}_T(x) \setminus \text{cov}_S(x)$。
   - $S \subseteq \mathcal{F}$ 是 **PI-explanation**，若 $S$ 是 AXp 且不存在任何 AXp $T$ 在 $x$ 处严格包含 $S$。
4. **单决策公平性（Definition 5）**：
   - 子集 $S \subseteq \mathcal{F}$ 是**公平的（fair）**，若 $S \cap \mathcal{P} = \emptyset$（即 $S \subseteq \mathcal{N}$）；否则称**不公平的（unfair）**。
   - **决策存在性公平（P1）**：$\langle \kappa, x \rangle$ 存在至少一个公平 PI-explanation。
   - **不公平 PI-解释存在性（P2）**：$\langle \kappa, x \rangle$ 存在至少一个不公平 PI-explanation。
   - **决策普遍性公平（P3）**：$\langle \kappa, x \rangle$ 的所有 PI-explanation 均公平（即 P2 的补问题）。
5. **分类器整体公平性（Definitions 14 & 15）**：
   - **受约束的无意识公平（Constrained FTU，Def 14）**：$\forall u, v \in \mathbb{F}[\mathcal{C}],\ u|_{\mathcal{N}} = v|_{\mathcal{N}} \implies \kappa(u) = \kappa(v)$。
   - **分类器存在性公平（P4，Def 15）**：$\forall x \in \mathbb{F}[\mathcal{C}]$，$\langle \kappa, x \rangle$ 存在公平 PI-explanation。
   - **分类器普遍性公平（P5，Def 15）**：$\forall x \in \mathbb{F}[\mathcal{C}]$，$\langle \kappa, x \rangle$ 的所有 PI-explanation 均公平。
6. **约束松弛性与分类器解耦性（Definitions 22 & 25）**：
   - **松弛性（Looseness，P6，Def 22）**：$\forall x \in \mathbb{F}[\mathcal{C}],\ \forall p \in \mathcal{P}$，$\{p\}$ 在 $x$ 处不严格包含 $\mathcal{N}$（即 $\text{cov}_{\mathcal{N}}(x) \not\subsetneq \text{cov}_{\{p\}}(x)$）。
   - **解耦性（Disentangledness，P7，Def 25）**：$\forall x \in \mathbb{F}[\mathcal{C}]$，$\mathcal{N}$ 是 $\langle \kappa, x \rangle$ 的 Weak AXp，且不被任何不公平 Weak AXp $Q$ 严格包含。

### 1.3 关键桥接引理

> **引理 1.1（Weak AXp 覆盖极大性刻画）**  
> *对应 Rocq：`weak_axp_has_axp`、`weak_fair_to_pi_fair` / `dec_exist_fair_at_to_pi`*
>
> 在有限特征集 $\mathcal{F}$ 上，对任意有效实例 $x \in \mathbb{F}[\mathcal{C}]$：
> 1. 若 $S$ 是 Weak AXp，则存在 AXp $S' \subseteq S$ 满足 $\text{cov}_S(x) \subseteq \text{cov}_{S'}(x)$；
> 2. $\langle \kappa, x \rangle$ 存在公平的 PI-explanation，当且仅当**存在公平 Weak AXp $S \subseteq \mathcal{N}$，不被任何不公平 Weak AXp $T$（$T \cap \mathcal{P} \neq \emptyset$）严格包含**。

**证明**：
- (1) 因 $\mathcal{F}$ 有限，对 $S$ 的基数 $|S|$ 施归纳，若 $S$ 非极小则取其真子集 Weak AXp 递降即得，且 $S' \subseteq S \implies \text{cov}_S(x) \subseteq \text{cov}_{S'}(x)$。
- (2) **($\Rightarrow$)** 若 $S \subseteq \mathcal{N}$ 是公平 PI-explanation，它必是公平 Weak AXp；若存在不公平 Weak AXp $T$ 满足 $\text{cov}_S(x) \subsetneq \text{cov}_T(x)$，由 (1) 取 AXp $T' \subseteq T$，则 $\text{cov}_S(x) \subsetneq \text{cov}_T(x) \subseteq \text{cov}_{T'}(x)$，与 $S$ 是 PI-explanation 矛盾。
- (2) **($\Leftarrow$)** 设公平 Weak AXp $S \subseteq \mathcal{N}$ 不被任何不公平 Weak AXp 严格包含。在有限空间 $\mathbb{F}[\mathcal{C}]$ 中，取所有满足 $\text{cov}_S(x) \subseteq \text{cov}_{\hat{S}}(x)$ 的公平 Weak AXp $\hat{S} \subseteq \mathcal{N}$ 中覆盖集基数 $|\text{cov}_{S^*}(x)|$ 极大者 $S^*$，再由 (1) 取 AXp $S' \subseteq S^* \subseteq \mathcal{N}$。由于 $\text{cov}_{S^*}(x) \subseteq \text{cov}_{S'}(x)$ 且 $S^*$ 极大，必有 $\text{cov}_{S'}(x) = \text{cov}_{S^*}(x) \supseteq \text{cov}_S(x)$。于是 $S'$ 既不能被任何公平 AXp 严格包含（违背 $S^*$ 极大性），也不能被任何不公平 AXp $T$ 严格包含（否则 $\text{cov}_S(x) \subseteq \text{cov}_{S'}(x) \subsetneq \text{cov}_T(x)$，违背对 $S$ 的假设）。故 $S'$ 是公平 PI-explanation。 $\blacksquare$

---

## 2. 七大问题（P1–P7）复杂度全景总表

| 编号 | 问题名称 | 原论文出处 | 归约源问题（标准完全问题） | 精确复杂度 | Rocq 文件与核心定理 | Rocq 公理依赖 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **P1** | 决策存在性公平 | Def 5, Prop 27 | $\exists X\forall Y\exists Z\ \Phi_{\text{3-CNF}}$ | **$\Sigma_3^P$-complete** | `verify_p1.v`<br>`p1_sigma3p_equiv_literal` | 仅标准排中律 |
| **P2** | 不公平 PI-解释存在性 | Def 4–5, Prop 27 | $\exists X\forall Y\exists Z\ \Phi_{\text{3-CNF}}$ | **$\Sigma_3^P$-complete** | `verify_p2_p3.v`<br>`p2_sigma3p_equiv` | 仅标准排中律 |
| **P3** | 决策普遍性公平 | Def 5, Prop 27 | $\forall X\exists Y\forall Z\ \neg\Phi_{\text{3-CNF}}$ | **$\Pi_3^P$-complete** | `verify_p2_p3.v`<br>`p3_pi3p_equiv` | 仅标准排中律 |
| **P4** | 分类器存在性公平 | Def 15, Prop 28 | $\forall W\exists X\forall Y\exists Z\ \Phi_{\text{3-CNF}}$ | **$\Pi_4^P$-complete** | `verify_p4.v`<br>`p4_pi4p_equiv_literal` | 仅标准排中律<br>(`p4_constrained_ftu` **0 公理**) |
| **P5** | 分类器普遍性公平 | Def 15, Prop 28 | $\forall X\exists Y\forall Z\ \neg\Phi_{\text{3-CNF}}$ | **$\Pi_3^P$-complete** | `verify_p5.v`<br>`p5_pi3p_equiv` | 仅标准排中律<br>(`p5_constrained_ftu` **0 公理**) |
| **P6** | 约束松弛性判定 | Def 22, Prop 31 | $\forall X\exists Z\ \neg\Phi_{\text{3-DNF}}$ | **$\Pi_2^P$-complete** | `verify_pi2p.v`<br>`looseness_pi2p_equiv` | **0 公理（完全构造性）** |
| **P7** | 分类器解耦性判定 | Def 25, Prop 31 | $\forall X\exists Z\ \neg\Phi_{\text{3-DNF}}$ | **$\Pi_2^P$-complete** | `verify_pi2p.v`<br>`disentangled_pi2p_equiv` | **0 公理（完全构造性）** |

---

## 3. P6（松弛性）与 P7（解耦性）的 $\Pi_2^P$-完全性证明

> **核心直觉**：在松弛性（Def 22）中，要阻断 $\{p^*\}$ 严格包含 $\mathcal{N}$，并不要求“只翻转 $p^*$ 而不动其他特征”，而是允许**同步调整其余受保护特征 $Z \in \mathcal{P}\setminus\{p^*\}$** 以维持约束成立。将 2-QBF 的外层变量 $X$ 放入 $\mathcal{N}$、内层变量 $Z$ 放入 $\mathcal{P}$，再加一个门控特征 $d \in \mathcal{N}$ 使 $d=0$ 成为无约束自由区，即可用单一纯 CNF 公式同时归约 P6 与 P7。

**对应 Rocq 文件**：`verify_pi2p.v`（定理 `looseness_pi2p_equiv` 与 `disentangled_pi2p_equiv`，完全构造性、0 公理）。

### 定理 3.1
判定约束松弛性（P6）与分类器解耦性（P7）均是 **$\Pi_2^P$-complete**（即使约束限制为多项式规模纯 5-CNF、分类器限制为单特征投影）。

### 归约构造
从 $\Pi_2\text{SAT}$ 的对偶形式归约：给定 3-DNF 公式 $\Phi_{\text{DNF}}(X, Z)$（变量 $X \in \{0,1\}^r, Z \in \{0,1\}^s$，设 $r \ge 1$），判定
$$\neg\exists X \in \{0,1\}^r\ \forall Z \in \{0,1\}^s\ \Phi_{\text{DNF}}(X, Z) = 1 \quad \Longleftrightarrow \quad \forall X \in \{0,1\}^r\ \exists Z \in \{0,1\}^s\ \neg\Phi_{\text{DNF}}(X, Z) = 1.$$
注意 $\neg\Phi_{\text{DNF}}(X, Z)$ 为多项式规模 3-CNF 公式。

- **特征划分**：
  - 非保护特征 $\mathcal{N} = \{d, X_0, \dots, X_{r-1}\}$；
  - 受保护特征 $\mathcal{P} = \{p^*, Z_0, \dots, Z_{s-1}\}$。
- **特征约束与分类器**：
  $$\mathcal{C}_{\text{red}}(d, X, p^*, Z) \equiv (\neg d) \lor p^* \lor \neg\Phi_{\text{DNF}}(X, Z), \qquad \kappa_d(d, X, p^*, Z) = d.$$
  若 $\neg\Phi_{\text{DNF}} = \bigwedge_\ell C_\ell$，则 $\mathcal{C}_{\text{red}} \equiv \bigwedge_\ell (\neg d \lor p^* \lor C_\ell)$，为多项式规模纯 5-CNF。

### 证明

**上界**：$\text{P6}, \text{P7} \in \Pi_2^P$ 已由 Cooper & Bousdira (CP 2026) Proposition 31 证明。

#### 一、P6（松弛性）双向等价性
- **($\Rightarrow$) 假设 $\forall X \exists Z\ \neg\Phi_{\text{DNF}}(X, Z) = 1$**：
  任取有效实例 $x \in \mathbb{F}[\mathcal{C}_{\text{red}}]$ 与受保护特征 $p \in \mathcal{P}$。只需构造有效点 $z \in \mathbb{F}[\mathcal{C}_{\text{red}}]$ 满足 $z|_{\mathcal{N}} = x|_{\mathcal{N}}$ 且 $z_p \neq x_p$（从而 $\text{cov}_{\mathcal{N}}(x) \not\subseteq \text{cov}_{\{p\}}(x)$）：
  1. 若 $d(x) = 0$：所有 $d=0$ 的实例均满足 $\mathcal{C}_{\text{red}}$，直接翻转 $p$ 即可；
  2. 若 $d(x) = 1$ 且 $p = Z_j$：令 $z = (d=1, X(x), p^*=1, Z(x)[Z_j := \neg Z_j(x)])$，因 $p^*=1$ 故 $\mathcal{C}_{\text{red}}(z)=1$；
  3. 若 $d(x) = 1$ 且 $p = p^*$：
     - 当 $p^*(x) = 0$ 时，令 $z = (d=1, X(x), p^*=1, Z(x))$，满足 $\mathcal{C}_{\text{red}}(z) = 1$；
     - 当 $p^*(x) = 1$ 时，由 $\forall X \exists Z\ \neg\Phi_{\text{DNF}}(X, Z) = 1$ 取使 $\neg\Phi_{\text{DNF}}(X(x), Z) = 1$ 的 $Z$，令 $z = (d=1, X(x), p^*=0, Z)$，满足 $\mathcal{C}_{\text{red}}(z) = 1$。
  
  故 $\{p\}$ 绝不严格包含 $\mathcal{N}$，$\mathcal{C}_{\text{red}}$ 松弛。

- **($\Leftarrow$) 假设存在 $X \in \{0,1\}^r$ 使 $\forall Z\ \Phi_{\text{DNF}}(X, Z) = 1$**：
  考察有效实例 $x = (d=1, X, p^*=1, \vec{0})$（因 $p^*=1$ 有效）。
  - 对任意 $z \in \text{cov}_{\mathcal{N}}(x)$，有 $d(z)=1$ 且 $X(z)=X$，从而 $\neg\Phi_{\text{DNF}}(X, Z(z))=0$，故 $\mathcal{C}_{\text{red}}(z)=1$ 强制 $p^*(z) = 1 = p^*(x)$，即 $\text{cov}_{\mathcal{N}}(x) \subseteq \text{cov}_{\{p^*\}}(x)$；
  - 另一方面，有效点 $y = (d=0, X, p^*=1, \vec{0})$ 属于 $\text{cov}_{\{p^*\}}(x)$ 却因 $d(y)=0 \neq 1$ 不属于 $\text{cov}_{\mathcal{N}}(x)$。
  
  故 $\{p^*\}$ 在 $x$ 处严格包含 $\mathcal{N}$，$\mathcal{C}_{\text{red}}$ 不松弛。

#### 二、P7（解耦性）双向等价性（$r \ge 1$）
因 $\kappa_d(w) = d(w)$ 且 $d \in \mathcal{N}$，$\mathcal{N}$ 在每个有效实例处自动是 $\kappa_d$ 的 Weak AXp。
- **($\Rightarrow$) 假设 $\forall X \exists Z\ \neg\Phi_{\text{DNF}}(X, Z) = 1$**：
  若存在不公平 Weak AXp $Q$ 在某 $x$ 处严格包含 $\mathcal{N}$，任取 $p \in Q \cap \mathcal{P}$，则 $\text{cov}_{\mathcal{N}}(x) \subsetneq \text{cov}_Q(x) \subseteq \text{cov}_{\{p\}}(x)$，推出 $\{p\}$ 严格包含 $\mathcal{N}$，与已证的 P6 矛盾。故 $\kappa_d$ 解耦。
- **($\Leftarrow$) 假设存在 $X$ 使 $\forall Z\ \Phi_{\text{DNF}}(X, Z) = 1$**：
  取 $x = (d=1, X, p^*=1, \vec{0}) \in \mathbb{F}[\mathcal{C}_{\text{red}}]$ 及不公平子集 $Q = \{d, p^*\}$（$p^* \in Q \cap \mathcal{P}$）。
  - 因 $d \in Q$ 且 $\kappa_d(w) = d(w)$，$Q$ 是 $\langle \kappa_d, x \rangle$ 的 Weak AXp；
  - 同 P6 反方向，任何 $z \in \text{cov}_{\mathcal{N}}(x)$ 均有 $d(z)=1, p^*(z)=1$，即 $\text{cov}_{\mathcal{N}}(x) \subseteq \text{cov}_Q(x)$；
  - 因 $r \ge 1$，取 $y = (d=1, X[X_0 := \neg X_0], p^*=1, \vec{0})$，因 $p^*=1$ 有效，满足 $y \in \text{cov}_Q(x) \setminus \text{cov}_{\mathcal{N}}(x)$。
  
  故不公平 Weak AXp $Q$ 严格包含 $\mathcal{N}$，$\kappa_d$ 不解耦。 $\blacksquare$

---

## 4. P1（决策存在性公平）的 $\Sigma_3^P$-完全性证明

> **核心直觉**：为模拟 $\exists X \forall Y \exists Z\ \Phi(X, Y, Z) = 1$，我们将特征空间以门控位 $d$ 分为上下两层：
> - **上层（$d=1$）** 负责编码 $\exists X$：目标点 $x^* = \vec{1}$ 在上层，任何公平 Weak AXp $S \subseteq \mathcal{N}$ 必须包含 $d=1$ 并在每对双轨特征 $(X_i^+, X_i^-)$ 中选出至少一条轨，从而刻画一个赋值 $X$。约束在上层强迫 $p=1$ 且所有 $Y_j^+=Y_j^-=1$。
> - **下层（$d=0, p=1$）** 负责编码 $\forall Y \exists Z$：约束要求 $(X_i^+, X_i^-)$ 和 $(Y_j^+, Y_j^-)$ 满足互斥编码，分类器输出 $\neg\Phi(X^+, Y^+, Z)$。若存在“坏 $Y^*$”使 $\forall Z\ \Phi(X, Y^*, Z)=0$，则不公平子集 $T$ 可丢弃 $d=1$、携带 $p=1$ 与 $Y^*$ 的正文字“跳入下层”且仍恒得 $\kappa=1$，从而严格包含 $S$！

**对应 Rocq 文件**：`verify_p1.v`（定理 `p1_sigma3p_equiv_literal`，经 `weak_fair_to_pi_fair` / `pi_fair_to_weak_fair` 对齐字面 Definition 5）。

### 定理 4.1（闭合 CP 2026 第 12 页 / Proposition 27 开放问题 P1）
判定给定决策 $\langle \mathcal{C}, \kappa, x^* \rangle$ 是否存在公平 PI-explanation（P1）是 **$\Sigma_3^P$-complete**。

### 归约构造
从标准 $\Sigma_3\text{SAT}$ 实例 $\Psi = \exists X \in \{0,1\}^r\ \forall Y \in \{0,1\}^q\ \exists Z \in \{0,1\}^s\ \Phi(X, Y, Z) = 1$ 归约，其中 $\Phi$ 为 3-CNF 公式（从而 $\neg\Phi$ 为多项式规模 3-DNF）。

- **特征划分**：
  - 非保护特征 $\mathcal{N} = \{d\} \cup \{X_i^+, X_i^-\}_{i<r}$；
  - 受保护特征 $\mathcal{P} = \{p\} \cup \{Y_j^+, Y_j^-\}_{j<q} \cup \{Z_k\}_{k<s}$。
- **目标实例**：$x^* = \vec{1}$（全部特征取值为 $1$）。
- **辅助谓词**：
  $$x\_ok(w) \equiv \bigwedge_{i<r} (X_i^+ \lor X_i^-), \quad x\_uniq(w) \equiv \bigwedge_{i<r} (X_i^+ \oplus X_i^-),$$
  $$y\_uniq(w) \equiv \bigwedge_{j<q} (Y_j^+ \oplus Y_j^-), \quad all\_Y(w) \equiv \bigwedge_{j<q} (Y_j^+ \land Y_j^-).$$
- **特征约束 $\mathcal{C}_{P1}$ 与分类器 $\kappa_{P1}$**：
  $$\mathcal{C}_{P1}(w) \equiv \begin{cases}
    p \land all\_Y(w) & \text{若 } d = 1 \land x\_ok(w),\\
    1 & \text{若 } d = 1 \land \neg x\_ok(w),\\
    x\_uniq(w) \land y\_uniq(w) & \text{若 } d = 0 \land p = 1,\\
    1 & \text{若 } d = 0 \land p = 0,
  \end{cases}
  \qquad
  \kappa_{P1}(w) \equiv \begin{cases}
    x\_ok(w) & \text{若 } d = 1,\\
    \neg\Phi(X^+, Y^+, Z) & \text{若 } d = 0 \land p = 1,\\
    0 & \text{若 } d = 0 \land p = 0.
  \end{cases}$$

易验 $\mathcal{C}_{P1}(x^*) = 1$ 且 $\kappa_{P1}(x^*) = 1$。

### 证明

**上界**：$\text{P1} \in \Sigma_3^P$ 见原论文 Proposition 27。由引理 1.1，只需证 $\Psi$ 成立当且仅当存在公平 Weak AXp $S \subseteq \mathcal{N}$ 不被任何不公平 Weak AXp $T$ 严格包含。

#### 1. ($\Rightarrow$) 若 $\Psi$ 成立，则 $x^*$ 存在性公平
取见证 $\forall Y \exists Z\ \Phi(X, Y, Z) = 1$ 的赋值 $X \in \{0,1\}^r$，构造公平子集
$$S_X = \{d\} \cup \{X_i^+ \mid X_i = 1\} \cup \{X_i^- \mid X_i = 0\} \subseteq \mathcal{N}.$$
显然 $S_X$ 是 $x^*$ 的公平 Weak AXp（$d=1$ 且 $x\_ok = 1 \implies \kappa_{P1}=1$）。

反证法：假设存在不公平 Weak AXp $T$ 严格包含 $S_X$，即 $\text{cov}_{S_X}(x^*) \subsetneq \text{cov}_T(x^*)$，并取见证 $v \in \text{cov}_T(x^*) \setminus \text{cov}_{S_X}(x^*)$。
1. **由 $\text{cov}_{S_X}(x^*) \subseteq \text{cov}_T(x^*)$ 排除冗余特征**：
   - 将 $x^*$ 中任一 $Z_k$ 置 $0$ 仍在 $\text{cov}_{S_X}(x^*)$ 中，故 $\forall k < s,\ Z_k \notin T$；
   - 对每个 $i < r$，将 $x^*$ 中未被 $S_X$ 选中的那一轨（若 $X_i=1$ 则置 $X_i^-=0$；若 $X_i=0$ 则置 $X_i^+=0$）置 $0$ 仍在 $\text{cov}_{S_X}(x^*)$ 中，故该未选中轨不在 $T$ 中。
2. **分两种情形讨论 $d \in T$**：
   - **情形 A：$d \in T$**。则对任意 $u \in \text{cov}_T(x^*)$ 有 $d(u) = 1$。若 $T$ 遗漏了 $S_X$ 中某对 $(X_i^+, X_i^-)$ 的选中轨（此时 $X_i^+, X_i^-$ 均不在 $T$ 中），则将 $x^*$ 的 $(X_i^+, X_i^-)$ 同置为 $(0,0)$ 所得的 $d=1, \neg x\_ok$ 实例有效、属于 $\text{cov}_T(x^*)$ 且 $\kappa_{P1}=0 \neq 1$，与 $T$ 是 Weak AXp 矛盾！故 $T$ 包含 $S_X$ 的全部特征，推出 $v \in \text{cov}_{S_X}(x^*)$，矛盾。
   - **情形 B：$d \notin T$**。
     - **先证 $p \in T$**：考察实例 $w^{(0,0)} = (d=0, p=0, X^+=X^-=\vec{1}, Y^+=Y^-=\vec{1}, Z=\vec{1})$。易验 $\mathcal{C}_{P1}(w^{(0,0)})=1$ 且 $\kappa_{P1}(w^{(0,0)})=0 \neq 1$；因其除 $d, p$ 外全为 $1$，由 $d \notin T$ 及 $T$ 为 Weak AXp 必得 **$p \in T$**。
     - **再证 $\forall j < q,\ \neg(Y_j^+ \in T \land Y_j^- \in T)$**：若存在 $j_0 < q$ 使 $Y_{j_0}^+, Y_{j_0}^- \in T$，则因 $p \in T$ 排除了 $d=0, p=0$，而 $Y_{j_0}^+=Y_{j_0}^-=1$ 违背 $y\_uniq$ 排除了 $d=0, p=1$，故 $\text{cov}_T(x^*)$ 被迫全部留在 $d=1$（特别地 $d(v)=1$）。同情形 A，为避开 $d=1, \neg x\_ok$（$\kappa=0$），$T$ 必包含 $S_X$ 中每对的选中轨，从而 $v \in \text{cov}_{S_X}(x^*)$，矛盾！
     - **构造下层反例**：令 $Y^*_j := \neg(Y_j^- \in T)$（即若 ^- \in T$ 则 $Y^*_j=0$，否则 $Y^*_j=1$）。由 $X$ 的性质，存在 $Z^*$ 使 $\Phi(X, Y^*, Z^*) = 1$。考察 $d=0, p=1$ 上的实例
       $$w_{(X, Y^*, Z^*)} = (d=0, p=1, X^+=X, X^-=\neg X, Y^+=Y^*, Y^-=\neg Y^*, Z=Z^*).$$
       易验 $\mathcal{C}_{P1}(w_{(X,Y^*,Z^*)})=1$ 且 $w_{(X,Y^*,Z^*)} \in \text{cov}_T(x^*)$（每对 $Y_j^+, Y_j^-$ 不同时在 $T$ 中，故 $Y^*_j$ 满足 $T$ 的所有 $Y^+/Y^-$ 约束），但 $\kappa_{P1}(w_{(X,Y^*,Z^*)}) = \neg\Phi(X, Y^*, Z^*) = 0 \neq 1$，与 $T$ 是 Weak AXp 矛盾！

#### 2. ($\Leftarrow$) 若 $x^*$ 存在性公平，则 $\Psi$ 成立
设 $S \subseteq \mathcal{N}$ 是不被任何不公平 Weak AXp 严格包含的公平 Weak AXp。
1. **$d \in S$**：因 $w^{(0,0)} = (d=0, p=0, \vec{1})$ 有效、$\kappa_{P1}=0 \neq 1$ 且在 $\mathcal{N}\setminus\{d\}$ 上全为 $1$，故 $d \in S$。
2. **$\forall i < r,\ X_i^+ \in S \lor X_i^- \in S$**：否则将 $x^*$ 的 $(X_i^+, X_i^-)$ 同置为 $(0,0)$ 得有效点且 $\kappa_{P1}=0 \neq 1$，矛盾。
3. 定义 $X_i := (X_i^+ \in S)$（当 $X_i=0$ 时必有 $X_i^- \in S$）。断言对任意 $Y \in \{0,1\}^q$ 存在 $Z$ 使 $\Phi(X, Y, Z) = 1$：
   否则若对某个 $Y$ 恒有 $\forall Z,\ \Phi(X, Y, Z) = 0$，构造不公平子集（$p \in T$）：
   $$T = \{p\} \cup \{X_i^+ \mid X_i = 1\} \cup \{X_i^- \mid X_i = 0\} \cup \{Y_j^+ \mid Y_j = 1\} \cup \{Y_j^- \mid Y_j = 0\}.$$
   - **$T$ 是 Weak AXp**：在 $d=1$ 上 $T$ 保证 $x\_ok=1$（$\kappa=1$）；在 $d=0$ 上 $p \in T$ 排除 $p=0$，而 $x\_uniq \land y\_uniq$ 配合 $T$ 强制 $X^+=X, Y^+=Y$，从而 $\kappa_{P1} = \neg\Phi(X, Y, Z) = 1$。
   - **$\text{cov}_S(x^*) \subsetneq \text{cov}_T(x^*)$**：任意 $u \in \text{cov}_S(x^*)$ 满足 $d(u)=1, x\_ok(u)=1$，由 $\mathcal{C}_{P1}(u)=1$ 自动推出 $p(u)=1, all\_Y(u)=1$，故 $u \in \text{cov}_T(x^*)$；而下层点 $w_{(X, Y, \vec{0})} \in \text{cov}_T(x^*) \setminus \text{cov}_S(x^*)$（因 $d \in S$）。
   
   这与 $S$ 不被不公平 Weak AXp 严格包含矛盾！故 $\Psi$ 成立。 $\blacksquare$

---

## 5. P2（不公平 PI-解释存在性）与 P3（决策普遍性公平）的完全性证明

> **核心直觉**：复用 P1 的全部约束与分类器，仅将**唯一受保护特征设为门控位 $\mathcal{P} = \{d\}$**。此时“含 $d$ 的上层解释”立刻变成**不公平解释**，而“跳过 $d$、携 $p=1$ 的下层解释”立刻变成**公平解释**——存在性公平与不公平解释存在性实现完美对偶！

**对应 Rocq 文件**：`verify_p2_p3.v`（定理 `p2_sigma3p_equiv` 与 `p3_pi3p_equiv`，直接对接字面 Definitions 3–5）。

### 定理 5.1（闭合 CP 2026 第 12 页 / Proposition 27 开放问题 P2 & P3）
判定决策是否存在不公平 PI-explanation（P2）是 **$\Sigma_3^P$-complete**；其补问题决策普遍性公平（P3）是 **$\Pi_3^P$-complete**。

### 归约构造
令 $\mathcal{C}_{P2} = \mathcal{C}_{P1}$，$\kappa_{P2} = \kappa_{P1}$，目标实例 $x^* = \vec{1}$，但将特征划分为：
$$\mathcal{P} = \{d\}, \qquad \mathcal{N} = \{X_i^+, X_i^-\}_{i<r} \cup \{p\} \cup \{Y_j^+, Y_j^-\}_{j<q} \cup \{Z_k\}_{k<s}.$$
此时子集 $T \subseteq \mathcal{F}$ 不公平当且仅当 $d \in T$。

### 证明

**上界**：$\text{P2} \in \Sigma_3^P,\ \text{P3} \in \Pi_3^P$ 见原论文 Proposition 27。以下证 $\Psi \iff x^*$ 存在不公平 PI-explanation：

- **($\Rightarrow$) 若 $\Psi$ 成立**：取见证 $X \in \{0,1\}^r$，令
  $$T_X = \{d\} \cup \{X_i^+ \mid X_i = 1\} \cup \{X_i^- \mid X_i = 0\}.$$
  1. **不公平性**：$d \in T_X \cap \mathcal{P}$。
  2. **极小性（$T_X$ 是 AXp）**：$T_X$ 是 Weak AXp。若删去 $d$，会被 $w^{(0,0)} = (d=0, p=0, \vec{1})$（$\kappa=0$）证伪；若删去第 $i$ 对的选中轨，会被 $x^*[X_i^+:=0, X_i^-:=0]$（$d=1, \neg x\_ok, \kappa=0$）证伪。故 $T_X$ 是极小 AXp。
  3. **覆盖极大性（$T_X$ 是 PI-explanation）**：设任意 AXp（甚至任意 Weak AXp）$S \subseteq \mathcal{F}$ 严格包含 $T_X$。与定理 4.1 方向 ($\Rightarrow$) 逐字相同（先排除 $Z_k$ 与未选中轨，再按 $d \in S$ 或 $d \notin S \implies p \in S$ 分情形），均导矛盾！故 $T_X$ 是不公平 PI-explanation。

- **($\Leftarrow$) 若存在不公平 PI-explanation $T$**：
  因 $T$ 不公平知 $d \in T$；因 $T$ 是 Weak AXp 且 $d=1, \neg x\_ok$ 无额外约束，对每个 $i < r$ 必有 $X_i^+ \in T \lor X_i^- \in T$（实际上由 $T$ 极小性还恰有一个为真）。令 $X_i := (X_i^+ \in T)$。
  若存在 $Y \in \{0,1\}^q$ 使 $\forall Z\ \Phi(X, Y, Z) = 0$，则同定理 4.1 构造的
  $$S = \{p\} \cup \{X_i^+ \mid X_i = 1\} \cup \{X_i^- \mid X_i = 0\} \cup \{Y_j^+ \mid Y_j = 1\} \cup \{Y_j^- \mid Y_j = 0\}$$
  是 Weak AXp 且严格包含 $T$（$\text{cov}_T(x^*) \subsetneq \text{cov}_S(x^*)$）。由引理 1.1(1)，存在 AXp $S' \subseteq S$ 同样严格包含 $T$，与 $T$ 是 PI-explanation 矛盾！故 $\Psi$ 成立。

因为 P3 是 P2 的精确补问题（`p3_pi3p_equiv`），立得 P3 是 **$\Pi_3^P$-complete**。 $\blacksquare$

---

## 6. P5（分类器普遍性公平）的 $\Pi_3^P$-完全性证明

> **核心障碍与破局技巧——「$(0,0)$-吸收态非互斥编码」**：
> 与单实例问题 P3 不同，分类器普遍性公平（P5）要求**整个有效空间 $\mathbb{F}[\mathcal{C}]$ 中的每一个实例 $x$**（包括下层 $d=0$ 区域！）都**没有任何不公平 PI-explanation**。
>
> 若沿用 P3 在下层 $d=0, p=1$ 的互斥编码 $Y_j^+ \oplus Y_j^- = 1$，则在下层会出现“文字 $Y_j^+=1$ 与 ^-=0$ 覆盖集完全相等”的平局，导致含 $d=0$ 的不公平 AXp 与不含 $d$ 的公平 AXp 覆盖相等而无法被严格包含！
>
> **破局方案**：在下层 $d=0, p=1$ 放弃互斥编码，改用**禁止双 1 约束** $x\_not11 \land y\_not11$（每对允许 $(1,0), (0,1), (0,0)$ 三态），并将 $(0,0)$ 设为**分类器输出 $\kappa = 0$ 的吸收态**！于是当 $x \in \{d=0, p=1\}$ 且 $\kappa(x)=0$ 时，把不公平 AXp 中的正文字 $Y_j^+=1$ 对偶替换为负文字 $Y_j^-=0$、并用 $p=1$ 替换 $d=0$，所得公平 Weak AXp 会**严格多覆盖 $(0,0)$ 吸收态**，彻底打破下层平局！

**对应 Rocq 文件**：`verify_p5.v`（定理 `p5_constrained_ftu` 0 公理，主定理 `p5_pi3p_equiv`）。

### 定理 6.1（闭合 CP 2026 Section 7 / Proposition 28 开放问题 P5）
判定整个分类器是否满足普遍性公平（P5）是 **$\Pi_3^P$-complete**。

### 归约构造
设 $r \ge 1, q \ge 1$，从 $\Pi_3\text{SAT}$ 实例 $\neg\Psi \equiv \forall X \in \{0,1\}^r\ \exists Y \in \{0,1\}^q\ \forall Z \in \{0,1\}^s\ \neg\Phi_{\text{3-CNF}}(X, Y, Z) = 1$ 归约。

- **特征划分**：唯一受保护特征 $\mathcal{P} = \{d\}$；非保护特征 $\mathcal{N} = \{X_i^+, X_i^-\}_{i<r} \cup \{p\} \cup \{Y_j^+, Y_j^-\}_{j<q} \cup \{Z_k\}_{k<s}$。
- **新增辅助谓词**：
  $$x\_not11(w) \equiv \bigwedge_{i<r} \neg(X_i^+ \land X_i^-), \qquad y\_not11(w) \equiv \bigwedge_{j<q} \neg(Y_j^+ \land Y_j^-),$$
  $$\text{dummy\_body}(w) \equiv \Big(\bigwedge_{i<r}(X_i^+ \land X_i^-)\Big) \land \Big(\bigwedge_{j<q}(\neg Y_j^+ \land \neg Y_j^-)\Big) \land \Big(\bigwedge_{k<s} \neg Z_k\Big).$$
- **特征约束 $\mathcal{C}_{P5}$ 与分类器 $\kappa_{P5}$**：
  $$\mathcal{C}_{P5}(w) \equiv \begin{cases}
    all\_Y(w) \land p & \text{若 } d = 1 \land x\_ok(w),\\
    all\_Y(w) & \text{若 } d = 1 \land \neg x\_ok(w),\\
    x\_not11(w) \land y\_not11(w) & \text{若 } d = 0 \land p = 1,\\
    \text{dummy\_body}(w) & \text{若 } d = 0 \land p = 0 \quad (\text{唯一 } \texttt{inst\_dummy}),
  \end{cases}$$
  $$\kappa_{P5}(w) \equiv \begin{cases}
    x\_ok(w) & \text{若 } d = 1,\\
    0 & \text{若 } d = 0 \land p = 1 \land \big(\exists i,\ \neg X_i^+ \land \neg X_i^- \ \lor\ \exists j,\ \neg Y_j^+ \land \neg Y_j^-\big),\\
    \neg\Phi(X^+, Y^+, Z) & \text{若 } d = 0 \land p = 1 \land x\_uniq(w) \land y\_uniq(w),\\
    0 & \text{若 } d = 0 \land p = 0.
  \end{cases}$$

### 证明

**上界**：$\text{P5} \in \Pi_3^P$ 见原论文 Proposition 28。

#### 性质 0（Constrained FTU 无条件成立，`p5_constrained_ftu`）
因 $q \ge 1$，当 $d=1$ 时约束强制 $(Y_0^+, Y_0^-) = (1, 1)$；当 $d=0$ 时，无论 $p=1$（$y\_not11$）还是 $p=0$（$\text{dummy\_body}$）均有 $\neg(Y_0^+ \land Y_0^-)$。故受保护特征 $d$ 被非保护特征 $(Y_0^+, Y_0^-)$ 唯一决定，Constrained FTU 恒成立。

#### 方向 1（$\neg\Psi \implies$ 分类器满足 P5）
假设 $\forall X \exists Y^* \forall Z\ \Phi(X, Y^*, Z) = 0$。任取有效实例 $x \in \mathbb{F}[\mathcal{C}_{P5}]$ 与任意不公平 Weak AXp $T$（含 $d \in T$），分 4 类完备情形证明 $T$ 不是 PI-explanation（要么 $T$ 非极小 AXp，要么存在 Weak AXp $S$ 严格包含 $T$，再由引理 1.1(1) 蕴涵存在 AXp $S' \subseteq S$ 严格包含 $T$）：

- **情形 1：$d(x)=1 \land x\_ok(x)=1$（$\kappa(x)=1, p(x)=1, all\_Y(x)=1$，`neg_three_qbf_case_d1_true`）**  
  对每个 $i < r$，$T$ 必包含至少一个在 $x$ 上取值为 $1$ 的特征 $X_i^+$ 或 $X_i^-$（否则把 $(X_i^+, X_i^-)$ 置 $(0,0)$ 得 $d=1, \neg x\_ok$，有效且 $\kappa=0 \neq 1$）。定义 $X_i := (X_i^+ \in T \land X_i^+(x)=1)$（当 $X_i=0$ 时必有 $X_i^- \in T \land X_i^-(x)=1$）。由 $\neg\Psi$ 取 $Y^*$ 使 $\forall Z\ \Phi(X, Y^*, Z)=0$，构造公平子集：
  $$S = \{p\} \cup \{X_i^+ \mid X_i = 1\} \cup \{X_i^- \mid X_i = 0\} \cup \{Y_j^+ \mid Y^*_j = 1\} \cup \{Y_j^- \mid Y^*_j = 0\} \subseteq \mathcal{N}.$$
  - **$S$ 是 Weak AXp**：在 $d=1$ 上 $S$ 保证 $x\_ok=1$（$\kappa=1$）；在 $d=0$ 上 $p \in S$ 强制 $p=1$，配合 $x\_not11 \land y\_not11$ 与 $S$ 中的 $1$-文字自动强制 $x\_uniq \land y\_uniq$ 且 $X^+=X, Y^+=Y^*$，故 $\kappa_{P5} = \neg\Phi(X, Y^*, Z) = 1$。
  - **$\text{cov}_T(x) \subsetneq \text{cov}_S(x)$**：任意 $u \in \text{cov}_T(x)$ 有 $d(u)=1, x\_ok(u)=1$，由约束强制 $p(u)=1, all\_Y(u)=1$，故 $u \in \text{cov}_S(x)$；且下层点 $w_{(X, Y^*, \vec{0})} \in \text{cov}_S(x) \setminus \text{cov}_T(x)$（因 $d \in T$）。故 $T$ 非 PI-explanation。

- **情形 2：$d(x)=1 \land x\_ok(x)=0$（$\kappa(x)=0$，`neg_three_qbf_case_d1_false`）**  
  证 $T$ 不是极小 AXp：
  - **子情形 2a（$p \in T \land p(x)=0$）**：真子集 $S_p = \{p\} \subsetneq T$（不含 $d$）在全空间恒得 $\kappa_{P5}=0$（$d=1, p=0 \implies \neg x\_ok$；$d=0, p=0 \implies \kappa=0$），违背 $T$ 极小性；
  - **子情形 2b（否则：$p \notin T$ 或 $p(x)=1$）**：则必存在 $i_0 < r$ 使得 $X_{i_0}^+, X_{i_0}^- \in T$ 且 $X_{i_0}^+(x) = X_{i_0}^-(x) = 0$（否则对每对 $i$ 将未固定为 $0$ 的位设为 $1$ 并取 $p=1$，可得有效点 $w \in \text{cov}_T(x)$ 满足 $d=1, x\_ok=1, \kappa=1 \neq 0$，矛盾）。此时真子集 $S_{i_0} = \{X_{i_0}^+, X_{i_0}^-\} \subsetneq T$ 在全空间恒得 $\kappa_{P5}=0$（在 $d=1$ 违反 $x\_ok$，在 $d=0, p=1$ 进入 $(0,0)$ 吸收态，在 $d=0, p=0$ 亦为 $0$），违背 $T$ 极小性。

- **情形 3：$d(x)=0 \land p(x)=0$（唯一 `inst_dummy` 点，$\kappa(x)=0$，`neg_three_qbf_case_d0_p0`）**  
  - **子情形 3a（$T$ 固定了某个 $Y_{j_0}^+$ 或 {j_0}^-$）**：在 `inst_dummy` 上该特征取值为 $0$，已排斥 $d=1$（要求 $all\_Y$），故真子集 $T \setminus \{d\} \subsetneq T$ 仍是 Weak AXp，违背极小性；
  - **子情形 3b（$T$ 不含任何 $Y_j^+, Y_j^-$）**：令公平子集 $S_p = \{p\} \subseteq \mathcal{N}$（在 $x$ 处 $p(x)=0$）。同情形 2a，$S_p$ 是 Weak AXp。断言 $\text{cov}_T(x) \subseteq \text{cov}_{S_p}(x)$：
    反设存在 $u \in \text{cov}_T(x)$ 使 $p(u)=1$（则 $p \notin T$，且 $d(u)=0$）。因 $u$ 满足 $x\_not11(u)$ 而 `inst_dummy` 满足 $X_i^+=X_i^-=1$，故 $T$ 不可能同时包含某对 $(X_i^+, X_i^-)$！于是令 $X_i := (X_i^+ \in T)$ 并由 $\neg\Psi$ 取 $Y^*$，得下层点 $w_{(X, Y^*, \vec{0})} \in \text{cov}_T(x)$（注意 $Z(\text{dummy})=\vec{0}$），其 $\kappa_{P5} = \neg\Phi(X, Y^*, \vec{0}) = 1 \neq 0$，矛盾！
    又由 $r \ge 1$，点 $(d=1, p=0, X^+=X^-=\vec{0}, Y^+=Y^-=\vec{1}, Z=\vec{0})$ 属于 $\text{cov}_{S_p}(x) \setminus \text{cov}_T(x)$，故 $S_p$ 严格包含 $T$。

- **情形 4：$d(x)=0 \land p(x)=1$（`neg_three_qbf_case_d0_p1`）**  
  - **子情形 4a（$T$ 包含某个在 $x$ 上取 $0$ 的 $Y_{j_0}^+$ 或 {j_0}^-$）**：该 $0$-文字已阻止 $d=1$，直接删去 $d$ 得 $T \setminus \{d\} \subsetneq T$ 仍是 Weak AXp，违背极小性；
  - **子情形 4b（否则，且 $\kappa_{P5}(x)=1$）**：因 $\kappa_{P5}(x)=1$，对每对 $i < r$，$T$ 必固定了在 $x$ 上取 $1$ 的那一轨（否则将其置 $0$ 进入 $(0,0)$ 吸收态得 $\kappa=0 \neq 1$）。故直接删去 $d$ 得真子集 $T \setminus \{d\} \subsetneq T$ 在 $d=1$ 上亦自动保证 $x\_ok=1$（$\kappa=1$），仍是 Weak AXp，违背极小性；
  - **子情形 4c（否则，且 $\kappa_{P5}(x)=0$）**：此时 $T$ 中所有 $Y^+/Y^-$ 在 $x$ 上均取 $1$（由 $y\_not11(x)$，其对偶位在 $x$ 上取 $0$）。
    1. *若 $T$ 含某个 $Y_{j_0}^+$ 或 {j_0}^-$*：构造对偶公平子集
       $$S = (T \setminus (\{d\} \cup \{Y_j^+, Y_j^-\}_{j<q})) \cup \{p\} \cup \{Y_j^- \mid Y_j^+ \in T\} \cup \{Y_j^+ \mid Y_j^- \in T\} \subseteq \mathcal{N}.$$
       - **$\text{cov}_T(x) \subseteq \text{cov}_S(x)$**：对任意 $u \in \text{cov}_T(x)$，$d(u)=0$ 且 $Y_{j_0}^+=1$（或 {j_0}^-=1$）排除了 `inst_dummy`，故 $p(u)=1$；再由 $y\_not11(u)$ 推出 $Y_j^+(u)=1 \implies Y_j^-(u)=0 = Y_j^-(x)$（对偶亦然），故 $u \in \text{cov}_S(x)$。
       - **$S$ 是 Weak AXp**：任意 $w \in \text{cov}_S(x)$ 含至少一个 $0$-值 $Y^+/Y^-$（排除 $d=1$）且 $p(w)=1$。若 $w$ 在 $T$ 的所有 $Y^+/Y^-$ 上均与 $x$ 一致则 $w \in \text{cov}_T(x) \implies \kappa(w)=0$；否则必有某对在 $w$ 上取 $(0,0)$，进入吸收态得 $\kappa(w)=0$！
       - **严格包含**：将 $x$ 的 $(Y_{j_0}^+, Y_{j_0}^-)$ 改为 $(0,0)$ 得有效点 $v \in \text{cov}_S(x) \setminus \text{cov}_T(x)$！
    2. *若 $T$ 不含任何 $Y_j^+, Y_j^-$*：若存在 $i_0 < r$ 使 $X_{i_0}^+, X_{i_0}^- \in T \land X_{i_0}^+(x)=X_{i_0}^-(x)=0$，则真子集 $\{X_{i_0}^+, X_{i_0}^-\} \subsetneq T$ 在全空间恒得 $\kappa=0$，违背极小性；否则令 $X_i := (X_i^+(x) \text{ 若 } X_i^+ \in T \text{ 否则 } \neg X_i^-(x))$，由 $\neg\Psi$ 取 $Y^*$，得有效点 $w_{(X, Y^*, Z(x))} \in \text{cov}_T(x)$ 且 $\kappa_{P5} = \neg\Phi(X, Y^*, Z(x)) = 1 \neq 0$，矛盾！

#### 方向 2（$\Psi \implies$ 分类器不满足 P5，`three_qbf_implies_not_cls_univ_fair`）
若 $\Psi$ 成立，取见证 $X$，考察目标点 $x^* = \vec{1}$ 与不公平子集 $T_X = \{d\} \cup \{X_i^+ \mid X_i=1\} \cup \{X_i^- \mid X_i=0\}$。
- **极小性**：删去 $d$ 会被唯一 `inst_dummy` $= (d=0, p=0, X^+=X^-=\vec{1}, Y^+=Y^-=\vec{0}, Z=\vec{0})$ 证伪（因 $T_X \setminus \{d\}$ 只含 $X^+, X^-$ 特征，不含 $p, Y^+, Y^-, Z$，故 `inst_dummy` $\in \text{cov}_{T_X \setminus \{d\}}(x^*)$ 且 $\kappa_{P5}=0 \neq 1$）；删去任一 $X_i^+/X_i^-$ 会被 $d=1, X_i^+=X_i^-=0$ 证伪。
- **覆盖极大性**：设任意 AXp $S$ 严格包含 $T_X$。同定理 4.1 排除 $Z_k$ 与未选中轨；若 $d \in S$ 或存在 $j_0$ 使 $Y_{j_0}^+, Y_{j_0}^- \in S$，则 $S$ 被迫留在 $d=1$（因 $y\_not11$ 排除 $d=0, p=1$，而 `inst_dummy` 上 $Y_{j_0}^+=0$ 排除 $d=0, p=0$），推出 $\text{cov}_S(x^*) \subseteq \text{cov}_{T_X}(x^*)$ 矛盾；否则令 $Y_j = \neg(Y_j^- \in S)$ 并由 $\Psi$ 取 $Z$，得 $w_{(X, Y, Z)} \in \text{cov}_S(x^*)$ 且 $\kappa_{P5}=0 \neq 1$，矛盾！

故 $T_X$ 是 $x^*$ 的不公平 PI-explanation，违反 P5。 $\blacksquare$

---

## 7. P4（分类器存在性公平）的 $\Pi_4^P$-完全性证明

> **核心障碍与破局技巧——「松弛护盾（Looseness Shield）」**：
> 为匹配四重量词 $\forall W \exists X \forall Y \exists Z\ \Phi(W, X, Y, Z) = 1$，外层 $\forall x \in \mathbb{F}[\mathcal{C}]$ 需遍历上层 $d=1$ 的一族目标点 $\{x_W\}_{W \in \{0,1\}^t}$，并在目标点 $x_W$ 处通过“不公平子集 $T$ 跨层跳入下层 $d=0, \Phi$ 区”来检验 $\exists X \forall Y \exists Z\ \Phi$。
>
> **双向跳跃障碍**：若 $T$ 是覆盖 $x_W$ 与下层某 $\Phi=0$ 点 $x_\phi$ 的不公平 Weak AXp，则按对称性 $T$ 也是 $x_\phi$ 的不公平 Weak AXp，极易在 $x_\phi$ 处反过来吞并 $x_\phi$ 的所有公平解释！
>
> **破局方案（松弛护盾）**：仅设**唯一受保护特征 $\mathcal{P} = \{p^*\}$**，令分类器 $\kappa_{P4}$ **完全不读取 $p^*$**（故 Constrained FTU 无条件成立），并令**下层 $d=0, is\_phi$ 区域对 $p^* \in \{0,1\}$ 完全自由**！于是对下层 $is\_phi$ 区的每个点 $x$，公平集 $S = \mathcal{N}$ 覆盖 $\{x, x[\neg p^*]\}$，而任何不公平集 $T$ 必含 $p^*$ 故绝不包含 $x[\neg p^*]$，彻底免疫反向跳跃攻击！与此同时，上层 $d=1$ 强制 $p^*=1$，仍允许不公平 $T$ 携 $p^*=1$ 跳入下层 $is\_phi$ 的 $p^*=1$ 分支完成归约。

**对应 Rocq 文件**：`verify_p4.v`（定理 `p4_constrained_ftu` 0 公理，主定理 `p4_pi4p_equiv_literal` 经有限覆盖计数桥接对齐字面 Definitions 3, 4, 15）。

### 定理 7.1（闭合 CP 2026 Section 7 / Proposition 28 最终开放问题 P4）
判定整个分类器是否满足存在性公平（P4）是 **$\Pi_4^P$-complete**。

### 归约构造
设 $t \ge 1, r \ge 1$，从标准 $\Pi_4\text{SAT}$ 实例 $\Omega = \forall W \in \{0,1\}^t\ \exists X \in \{0,1\}^r\ \forall Y \in \{0,1\}^q\ \exists Z \in \{0,1\}^s\ \Phi_{\text{3-CNF}}(W, X, Y, Z) = 1$ 归约。

- **特征划分**：
  - 受保护特征 $\mathcal{P} = \{p^*\}$（仅 1 个布尔特征）；
  - 非保护特征 $\mathcal{N} = \{d, q_B, z_0\} \cup \{W_k^+, W_k^-\}_{k<t} \cup \{X_i^+, X_i^-\}_{i<r} \cup \{Y_j^+, Y_j^-\}_{j<q} \cup \{Z_m\}_{m<s}$。
- **辅助谓词**：$w\_ok, w\_uniq, x\_ok, x\_uniq, y\_uniq, all\_Y$ 定义同前，并设
  $$all\_X(w) \equiv \bigwedge_{i<r} (X_i^+ \land X_i^-),$$
  $$is\_dummy(w) \equiv (\neg p^*) \land w\_ok(w) \land all\_X(w) \land all\_Y(w),$$
  $$is\_phi(w) \equiv w\_uniq(w) \land x\_uniq(w) \land y\_uniq(w).$$
  *注意 $is\_phi$ 不依赖 $p^*$（松弛护盾），且因 $r \ge 1$，$is\_dummy$ 与 $is\_phi$ 互斥。*
- **特征约束 $\mathcal{C}_{P4}$ 与分类器 $\kappa_{P4}$**：
  $$\mathcal{C}_{P4}(w) \equiv \begin{cases}
    p^* \land all\_Y(w) \land (\neg q_B) & \text{若 } d = 1 \land (w\_ok \land x\_ok) \land (w\_uniq \land all\_X),\\
    p^* \land all\_Y(w) \land q_B & \text{若 } d = 1 \land (w\_ok \land x\_ok) \land \neg(w\_uniq \land all\_X),\\
    p^* \land all\_Y(w) \land (\neg q_B) & \text{若 } d = 1 \land \neg(w\_ok \land x\_ok),\\
    (\neg q_B) \land \big(is\_dummy(w) \lor is\_phi(w)\big) & \text{若 } d = 0,
  \end{cases}$$
  $$\kappa_{P4}(w) \equiv \begin{cases}
    w\_ok(w) \land x\_ok(w) & \text{若 } d = 1,\\
    1 & \text{若 } d = 0 \land is\_phi(w) \land z_0 = 0,\\
    \neg\Phi(W^+, X^+, Y^+, Z) & \text{若 } d = 0 \land is\_phi(w) \land z_0 = 1,\\
    0 & \text{若 } d = 0 \land \neg is\_phi(w).
  \end{cases}$$

### 证明

**上界**：$\text{P4} \in \Pi_4^P$ 见原论文 Proposition 28。且因 $\kappa_{P4}$ 完全不含 $p^*$，Constrained FTU 无条件成立（`p4_constrained_ftu`）。

#### 方向 1（$\Omega \implies$ 分类器满足 P4）
由引理 1.1，只需对全体有效实例 $x \in \mathbb{F}[\mathcal{C}_{P4}]$ 的 6 类完备分区，逐一给出不被任何不公平 Weak AXp $T$（即 $p^* \in T$）严格包含的公平 Weak AXp $S \subseteq \mathcal{N}$：

1. **区 1（松弛护盾区：$d(x)=0, is\_phi(x)=1$，`case_d0_phi`）**  
   取 $S = \mathcal{N}$。由 Constrained FTU，$S$ 是公平 Weak AXp。翻转 $p^*$ 得有效实例 $u = x[p^* := \neg p^*(x)] \in \text{cov}_{\mathcal{N}}(x)$；任何不公平 $T$ 必含 $p^*$ 故 $u \notin \text{cov}_T(x)$，即 $\text{cov}_{\mathcal{N}}(x) \not\subseteq \text{cov}_T(x)$！

2. **区 2（Dummy 区：$d(x)=0, is\_phi(x)=0$，即 $is\_dummy(x)=1, p^*(x)=0, \kappa(x)=0$，`case_d0_dummy`）**  
   由 $r \ge 1$，取 $S_{\text{dummy}} = \{d, X_0^+, X_0^-\} \subseteq \mathcal{N}$（值 $0, 1, 1$）。因 $X_0^+=X_0^-=1$ 破坏 $x\_uniq$，故 $S_{\text{dummy}}$ 是 Weak AXp。若不公平 Weak AXp $T$（$p^* \in T$）严格包含 $S_{\text{dummy}}$：
   - 翻转 $z_0(x)$ 仍在 $\text{cov}_{S_{\text{dummy}}}(x)$ 中，故 $z_0 \notin T$；
   - 取 $v \in \text{cov}_T(x) \setminus \text{cov}_{S_{\text{dummy}}}(x)$：因 $p^*(v)=p^*(x)=0$ 排除 $d=1$，必有 $d(v)=0$；又 $v \notin \text{cov}_{S_{\text{dummy}}}(x)$ 破坏 $all\_X$，从而 $is\_dummy(v)=0$，由约束强制 $is\_phi(v)=1$！
   - 令 $v_0 = v[z_0 := 0]$，则 $v_0 \in \text{cov}_T(x)$ 有效且 $\kappa_{P4}(v_0)=1 \neq 0$，矛盾！

3. **区 3a（无效门区：$d(x)=1, w\_ok(x)=0, \kappa(x)=0$，`case_d1_w_not_ok`）**  
   取使 $W_{k_0}^+(x)=W_{k_0}^-(x)=0$ 的 $k_0 < t$，令 $S_{w0} = \{W_{k_0}^+, W_{k_0}^-\} \subseteq \mathcal{N}$。任何 $w \in \text{cov}_{S_{w0}}(x)$ 均有 $w\_ok(w)=0, is\_phi(w)=0 \implies \kappa(w)=0$。若 $T$ 严格包含 $S_{w0}$，则 $T$ 必遗漏 $W_{k_0}^+$ 或 $W_{k_0}^-$ 之一（不妨设 $W_{k_0}^+ \notin T$）。取基底点
   $$u_{\text{base}} = (d=1, q_B=0, z_0(x), W_{k_0}^+=0, W_{k\neq k_0}^+=1, W^-=\vec{0}, X^+=X^-=Y^+=Y^-=\vec{1}, Z(x), p^*=1) \in \text{cov}_{S_{w0}}(x) \subseteq \text{cov}_T(x),$$
   将 $u_{\text{base}}$ 的 $W_{k_0}^+$ 改为 $1$ 得 $w_{\text{hit}}$，则 $w_{\text{hit}}$ 满足 $w\_uniq \land all\_X$（故 $q_B=0$ 有效）、属于 $\text{cov}_T(x)$ 且 $\kappa_{P4}(w_{\text{hit}})=1 \neq 0$，矛盾！

4. **区 3b（无效门区：$d(x)=1, w\_ok(x)=1, x\_ok(x)=0$，从而 $q_B(x)=0, p^*(x)=1, \kappa(x)=0$，`case_d1_x_not_ok`）**  
   取使 $X_{i_0}^+(x)=X_{i_0}^-(x)=0$ 的 $i_0 < r$，令 $S_{x0} = \{d, q_B, X_{i_0}^+\} \subseteq \mathcal{N}$（值 $1, 0, 0$）。在 $d=1, q_B=0$ 上，$X_{i_0}^+=0$ 导致 $all\_X=0$，而 $w\_ok \land x\_ok \land \neg all\_X$ 要求 $q_B=1$，故 $\text{cov}_{S_{x0}}(x)$ 恒有 $\neg(w\_ok \land x\_ok)$ 即 $\kappa=0$。
   设不公平 Weak AXp $T$（$p^* \in T$）严格包含 $S_{x0}$，取 $v \in \text{cov}_T(x) \setminus \text{cov}_{S_{x0}}(x)$：
   - 翻转 $z_0(x)$ 仍在 $\text{cov}_{S_{x0}}(x)$ 中，故 $z_0 \notin T$；
   - **引理 `unfair_weak_axp_kappa0_p1_forces_d1`**：因 $p^*(v)=p^*(x)=1, \kappa(x)=0, z_0 \notin T$，必有 $d(v)=1$（若 $d(v)=0$，则 $p^*=1$ 排除 $is\_dummy$ 强制 $is\_phi(v)=1$，置 $z_0=0$ 即得 $\kappa=1 \neq 0$，矛盾）；
   - 由 $d(v)=1$ 及 $v \notin \text{cov}_{S_{x0}}(x)$，必有 $q_B \notin T$ 或 $X_{i_0}^+ \notin T$；
   - **双基底拼合构造**（对应 `verify_p4.v` 中的 `u_base_A` 与 `u_base_B`）：在 $\text{cov}_{S_{x0}}(x) \subseteq \text{cov}_T(x)$ 中取两个有效基底点：
     $$u_{\text{base}, A} = (d=1, q_B=0, z_0(x), W^+=\vec{1}, W^-=\vec{0}, X_{i_0}^+=X_{i_0}^-=0, X_{i\neq i_0}^+=X_{i\neq i_0}^-=1, Y^+=Y^-=\vec{1}, Z(x), p^*=1),$$
     $$u_{\text{base}, B} = (d=1, q_B=0, z_0(x), W^+=\vec{0}, W^-=\vec{0}, X_{i_0}^+=0, X_{i\neq i_0}^+=1, X^-=\vec{1}, Y^+=Y^-=\vec{1}, Z(x), p^*=1)$$
     （$u_{\text{base}, A}$ 因 $\neg x\_ok$ 有效；$u_{\text{base}, B}$ 依赖 $t \ge 1$ 因 $\neg w\_ok$ 有效）。于是 $T$ 同时与 $u_{\text{base}, A}$ 在 $(d, z_0, W^+, W^-, X^+, Y^+, Y^-, Z, p^*)$ 上一致，且与 $u_{\text{base}, B}$ 在 $X^-=\vec{1}$ 上一致！将这两组一致的坐标拼合起来：
     - 若 $q_B \notin T$：令 $w_{\text{hit}}$ 取 $u_{\text{base}, A}$ 的其余坐标，同时将 $B$ 替换为 $u_{\text{base}, B}$ 的 $\vec{1}$、并将 $q_B$ 置为 $1$。此时 $w_{\text{hit}}$ 满足 $w\_ok \land x\_ok \land \neg all\_X$（因 $X_{i_0}^+=0$），故 $q_B=1$ 有效，$w_{\text{hit}} \in \text{cov}_T(x)$ 且 $\kappa_{P4}(w_{\text{hit}})=1 \neq 0$，矛盾！
     - 若 $X_{i_0}^+ \notin T$：令 $w_{\text{hit}}$ 取 $u_{\text{base}, A}$ 的其余坐标，同时将 $X^-$ 替换为 $u_{\text{base}, B}$ 的 $\vec{1}$、并将 $X_{i_0}^+$ 置为 $1$（保持 $q_B=0$）。此时 $w_{\text{hit}}$ 满足 $w\_uniq \land all\_X$，故 $q_B=0$ 有效，$w_{\text{hit}} \in \text{cov}_T(x)$ 且 $\kappa_{P4}(w_{\text{hit}})=1 \neq 0$，矛盾！

5. **区 4（辅助 $q_B=1$ 区：$d(x)=1, w\_ok \land x\_ok=1, \neg(w\_uniq \land all\_X)$，故 $q_B(x)=1, \kappa(x)=1$，`case_d1_qB1`）**  
   取单特征集 $S_{qB} = \{q_B\} \subseteq \mathcal{N}$。全空间中 $q_B=1$ 仅出现在本区，恒得 $\kappa=1$。若 $T$ 严格包含 $S_{qB}$，则 $q_B \notin T$；在 $\text{cov}_{S_{qB}}(x)$ 中令 $X_0^+=0, X_0^-=1$（利用 $r \ge 1$ 使 $all\_X=0$），则 $WA_0$ 与 $WB_0$（利用 $t \ge 1$）均可自由翻转，故 $WA_0 \notin T \land WB_0 \notin T$。将 $x$ 的 $(q_B, W_0^+, W_0^-)$ 同置为 $(0,0,0)$ 得有效点 $w_{\text{bad}} \in \text{cov}_T(x)$，满足 $\neg w\_ok \implies \kappa_{P4}=0 \neq 1$，矛盾！

6. **区 5（目标族 $x_W$：$d(x)=1, w\_uniq \land all\_X = 1$，故 $q_B(x)=0, p^*(x)=1, all\_Y(x)=1, \kappa(x)=1$，`case_d1_target_W`）**  
   令 $W_k := W_k^+(x)$（由 $w\_uniq$ 有 $WB_k(x) = \neg W_k$）。由 $\Omega$ 取 $X \in \{0,1\}^r$ 使 $\forall Y \exists Z\ \Phi(W, X, Y, Z)=1$，构造公平 Weak AXp：
   $$S_{W, X} = \{d\} \cup \{W_k^+ \mid W_k=1\} \cup \{W_k^- \mid W_k=0\} \cup \{X_i^+ \mid X_i=1\} \cup \{X_i^- \mid X_i=0\} \subseteq \mathcal{N}.$$
   设不公平 Weak AXp $T$（$p^* \in T$）严格包含 $S_{W,X}$，取 $v \in \text{cov}_T(x) \setminus \text{cov}_{S_{W,X}}(x)$：
   - **见证 1（$u_{\text{all1}} \in \text{cov}_{S_{W,X}}(x)$）**：取 $d=1, q_B=1, z_0=\neg z_0(x), W^+=W^-=\vec{1}, X^+=X^-=Y^+=Y^-=\vec{1}, Z=\neg Z(x), p^*=1$（由 $t \ge 1$ 破坏 $w\_uniq$，故 $q_B=1$ 有效），推出 $q_B \notin T, z_0 \notin T, \forall m\ (Z_m \notin T)$ 且 $T$ 在 $W^+/W^-$ 上不含与 $W$ 相悖的轨；
   - **见证 2（$u_X \in \text{cov}_{S_{W,X}}(x)$）**：取 $d=1, q_B=1, W^+=W, W^-=\neg W, X^+=X, X^-=\neg X, Y^+=Y^-=\vec{1}, p^*=1$（由 $r \ge 1$ 破坏 $all\_X$，故 $q_B=1$ 有效），推出 $T$ 在 $A/B$ 上不含与 $X$ 相悖的轨；
   - **若 $d \in T$ 或存在 $j_0$ 使 $Y_{j_0}^+, Y_{j_0}^- \in T$**：因 $p^* \in T$ 排除 $is\_dummy$，故 $\text{cov}_T(x)$ 被迫留在 $d=1$（特别地 $d(v)=1$），此时为避开 $d=1, \neg(w\_ok \land x\_ok)$（$\kappa=0$），$T$ 必包含 $S_{W,X}$ 全部特征，推出 $v \in \text{cov}_{S_{W,X}}(x)$，矛盾；
   - **否则（$d \notin T$ 且 $\forall j, \neg(Y_j^+, Y_j^- \in T)$）**：令 $Y_j := \neg(Y_j^- \in T)$ 并由 $X$ 的性质取 $Z$ 使 $\Phi(W, X, Y, Z)=1$，则下层点
     $$w_\phi = (d=0, q_B=0, z_0=1, W^+=W, W^-=\neg W, X^+=X, X^-=\neg X, Y^+=Y, Y^-=\neg Y, Z=Z, p^*=1)$$
     有效、属于 $\text{cov}_T(x)$ 且 $\kappa_{P4}(w_\phi) = \neg\Phi(W, X, Y, Z) = 0 \neq 1$，矛盾！

#### 方向 2（分类器满足 P4 $\implies \Omega$，`cls_exist_fair_implies_four_qbf`）
任取 $W \in \{0,1\}^t$，考察有效目标实例
$$x_W = (d=1, q_B=0, z_0=1, W^+=W, W^-=\neg W, X^+=X^-=\vec{1}, Y^+=Y^-=\vec{1}, Z=\vec{1}, p^*=1).$$
由 P4 及引理 1.1，存在公平 Weak AXp $S \subseteq \mathcal{N}$（即 $p^* \notin S$）不被任何不公平 Weak AXp 严格包含。
1. **$d \in S$**：将 $x_W$ 的 $(d, p^*)$ 同置为 $(0, 0)$ 所得的 dummy 点 $y_{\text{dummy}, W}$ 有效、$\kappa_{P4}=0 \neq 1$（依赖 $r \ge 1$ 使 $is\_phi=0$），且在 $\mathcal{N}\setminus\{d\}$ 上与 $x_W$ 完全一致，故 $d \in S$；
2. **锁定 $W$ 与 $X$**：同理，将 $x_W$ 中 $W_k$ 对应的 $1$-轨置 $0$（得 $\neg w\_ok$）或将 $(X_i^+, X_i^-)$ 同置 $(0,0)$（得 $\neg x\_ok$）均得有效点且 $\kappa=0$，故 $S$ 必锁定每个 $W_k$ 的 $1$-轨且对每个 $i < r$ 有 $X_i^+ \in S \lor X_i^- \in S$；
3. 令 $X_i := (X_i^+ \in S)$。反设存在 $Y \in \{0,1\}^q$ 使 $\forall Z\ \Phi(W, X, Y, Z) = 0$，构造不公平子集（$p^* \in T$）：
   $$T = \{p^*\} \cup \{W_k^+ \mid W_k=1\} \cup \{W_k^- \mid W_k=0\} \cup \{X_i^+ \mid X_i=1\} \cup \{X_i^- \mid X_i=0\} \cup \{Y_j^+ \mid Y_j^+=1\} \cup \{Y_j^- \mid Y_j=0\}.$$
   - **$T$ 是 Weak AXp**：在 $d=1$ 上 $T$ 保证 $w\_ok \land x\_ok$（$\kappa=1$）；在 $d=0$ 上 $p^*=1$ 排除 $is\_dummy$ 强制 $is\_phi$，进而锁定 $W^+=W, X^+=X, Y^+=Y$，故 $z_0=0$ 时 $\kappa=1$，$z_0=1$ 时 $\kappa = \neg\Phi(W, X, Y, Z) = 1$；
   - **$\text{cov}_S(x_W) \subsetneq \text{cov}_T(x_W)$**：任意 $u \in \text{cov}_S(x_W)$ 因 $d \in S$ 有 $d(u)=1$，由约束强制 $p^*(u)=1, all\_Y(u)=1$，故 $u \in \text{cov}_T(x_W)$；而下层点 $w_\phi(W, X, Y, \vec{1}) \in \text{cov}_T(x_W) \setminus \text{cov}_S(x_W)$（因 $d \in S$）。
   
   矛盾！故 $\forall W \exists X \forall Y \exists Z\ \Phi(W, X, Y, Z) = 1$ 成立。 $\blacksquare$
