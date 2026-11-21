# Complete Mathematical Proofs of Classifier Fairness Under Feature Constraints (P1–P7)

> [!IMPORTANT]
> This document presents the complete mathematical proofs aligned one-to-one with the 5 **Rocq (Coq 9.0)** formalization files (`rocq_proofs/verify_pi2p.v`, `verify_p1.v`, `verify_p2_p3.v`, `verify_p5.v`, `verify_p4.v`; 0 `Admitted`, 0 custom axioms), resolving all **7 open computational complexity lower-bound problems (P1–P7)** posed in Sections 6–7 (**Propositions 27, 28, and 31**) of **Cooper & Bousdira (CP 2026)**, *"Fairness of Classifiers in the Presence of Constraints Between Features"*.

---

## 1. Formal Preliminaries & Core Definitions

### 1.1 Setting and Computational Model

Let $\mathcal{F} = \{1, \dots, n\}$ be the finite set of Boolean features, partitioned into a set of **unprotected features** $\mathcal{N}$ and a set of **protected (sensitive) features** $\mathcal{P}$ ($\mathcal{F} = \mathcal{N} \cup \mathcal{P}$, $\mathcal{N} \cap \mathcal{P} = \emptyset$). The feature space is the finite Boolean hypercube $\mathbb{F} = \{0, 1\}^n$.

- **Feature Constraints and Valid Instance Space**: A polynomial-time decidable Boolean formula/circuit $\mathcal{C} : \mathbb{F} \to \{0, 1\}$ defines the valid instance space $\mathbb{F}[\mathcal{C}] = \{x \in \mathbb{F} \mid \mathcal{C}(x) = 1\}$.
- **Classifier**: A polynomial-time computable Boolean function $\kappa : \mathbb{F} \to \{0, 1\}$ (following Section 7, pp. 12–13 of Cooper & Bousdira, CP 2026).
  - *Representational Strength*: For **P1–P5**, the constructed $(\mathcal{C}, \kappa)$ are polynomial-size Boolean formulas/circuits; for **P6–P7**, $\mathcal{C}_{\text{red}}$ is directly a polynomial-size **pure 5-CNF formula** and $\kappa_d$ is merely a **single-feature projection classifier** (a depth-1 decision tree).
  - *Correspondence with Rocq's Finite-Domain Encoding*: Although instance vectors in the Rocq formalization have type `nat -> bool`, every theorem includes `cnf_bounded` / `dnf_bounded` preconditions and every predicate inspects only finite coordinate prefixes, making the formalization strictly isomorphic to the finite hypercube $\{0,1\}^N$.

### 1.2 Explanations and Fairness Definitions (Aligned with Cooper & Bousdira, CP 2026)

1. **Coverage (Section 2, p. 3)**: For a valid instance $x \in \mathbb{F}[\mathcal{C}]$ and a feature subset $S \subseteq \mathcal{F}$, the coverage of $S$ at $x$ is
   $$\text{cov}_S(x) = \{y \in \mathbb{F}[\mathcal{C}] \mid \forall i \in S,\ y_i = x_i\}.$$
2. **Weak AXp and Abductive Explanation (AXp, Definition 3)**:
   - $S \subseteq \mathcal{F}$ is a **Weak AXp** of $\langle \kappa, x \rangle$ if $\forall y \in \text{cov}_S(x),\ \kappa(y) = \kappa(x)$.
   - $S \subseteq \mathcal{F}$ is an **AXp** if $S$ is a subset-minimal Weak AXp with respect to $\subseteq$.
3. **Strict Subsumption and Prime-Implicant Explanation (PI-explanation, Definition 4)**:
   - $T \subseteq \mathcal{F}$ **strictly subsumes** $S \subseteq \mathcal{F}$ at $x$, denoted $\text{cov}_S(x) \subsetneq \text{cov}_T(x)$, if $\text{cov}_S(x) \subseteq \text{cov}_T(x)$ and there exists $v \in \text{cov}_T(x) \setminus \text{cov}_S(x)$.
   - $S \subseteq \mathcal{F}$ is a **PI-explanation** if $S$ is an AXp and no AXp $T$ strictly subsumes $S$ at $x$.
4. **Decision-Level Fairness (Definition 5)**:
   - A subset $S \subseteq \mathcal{F}$ is **fair** if $S \cap \mathcal{P} = \emptyset$ (i.e., $S \subseteq \mathcal{N}$); otherwise it is **unfair**.
   - **Decision Existential Fairness (P1)**: $\langle \kappa, x \rangle$ has at least one fair PI-explanation.
   - **Existence of an Unfair PI-explanation (P2)**: $\langle \kappa, x \rangle$ has at least one unfair PI-explanation.
   - **Decision Universal Fairness (P3)**: All PI-explanations of $\langle \kappa, x \rangle$ are fair (the exact complement of P2).
5. **Classifier-Level Fairness (Definitions 14 & 15)**:
   - **Constrained FTU (Def. 14)**: $\forall u, v \in \mathbb{F}[\mathcal{C}],\ u|_{\mathcal{N}} = v|_{\mathcal{N}} \implies \kappa(u) = \kappa(v)$.
   - **Classifier Existential Fairness (P4, Def. 15)**: $\forall x \in \mathbb{F}[\mathcal{C}]$, $\langle \kappa, x \rangle$ has a fair PI-explanation.
   - **Classifier Universal Fairness (P5, Def. 15)**: $\forall x \in \mathbb{F}[\mathcal{C}]$, all PI-explanations of $\langle \kappa, x \rangle$ are fair.
6. **Looseness and Disentangledness (Definitions 22 & 25)**:
   - **Looseness (P6, Def. 22)**: $\forall x \in \mathbb{F}[\mathcal{C}],\ \forall p \in \mathcal{P}$, $\{p\}$ does not strictly subsume $\mathcal{N}$ at $x$ (i.e., $\text{cov}_{\mathcal{N}}(x) \not\subsetneq \text{cov}_{\{p\}}(x)$).
   - **Disentangledness (P7, Def. 25)**: $\forall x \in \mathbb{F}[\mathcal{C}]$, $\mathcal{N}$ is a Weak AXp of $\langle \kappa, x \rangle$ that is not strictly subsumed by any unfair Weak AXp $Q$.

### 1.3 Key Bridging Lemma

> **Lemma 1.1 (Coverage-Maximality Characterization of Weak AXps)**  
> *Rocq correspondence: `weak_axp_has_axp`, `weak_fair_to_pi_fair` / `dec_exist_fair_at_to_pi`*
>
> Over a finite feature set $\mathcal{F}$, for every valid instance $x \in \mathbb{F}[\mathcal{C}]$:
> 1. If $S$ is a Weak AXp, then there exists an AXp $S' \subseteq S$ such that $\text{cov}_S(x) \subseteq \text{cov}_{S'}(x)$;
> 2. $\langle \kappa, x \rangle$ has a fair PI-explanation if and only if **there exists a fair Weak AXp $S \subseteq \mathcal{N}$ that is not strictly subsumed by any unfair Weak AXp $T$ ($T \cap \mathcal{P} \neq \emptyset$)**.

**Proof**:
- (1) Since $\mathcal{F}$ is finite, induct on $|S|$: if $S$ is not minimal, replace it with a strict subset Weak AXp and descend; moreover $S' \subseteq S \implies \text{cov}_S(x) \subseteq \text{cov}_{S'}(x)$.
- (2) **($\Rightarrow$)** If $S \subseteq \mathcal{N}$ is a fair PI-explanation, it is a fair Weak AXp. If an unfair Weak AXp $T$ satisfied $\text{cov}_S(x) \subsetneq \text{cov}_T(x)$, by (1) there exists an AXp $T' \subseteq T$ with $\text{cov}_S(x) \subsetneq \text{cov}_T(x) \subseteq \text{cov}_{T'}(x)$, contradicting that $S$ is a PI-explanation.
- (2) **($\Leftarrow$)** Suppose $S \subseteq \mathcal{N}$ is a fair Weak AXp not strictly subsumed by any unfair Weak AXp. In the finite space $\mathbb{F}[\mathcal{C}]$, pick a fair Weak AXp $S^* \subseteq \mathcal{N}$ maximizing $|\text{cov}_{S^*}(x)|$ among all fair Weak AXps satisfying $\text{cov}_S(x) \subseteq \text{cov}_{\hat{S}}(x)$, and by (1) take an AXp $S' \subseteq S^* \subseteq \mathcal{N}$. Since $\text{cov}_{S^*}(x) \subseteq \text{cov}_{S'}(x)$ and $S^*$ is coverage-maximal, $\text{cov}_{S'}(x) = \text{cov}_{S^*}(x) \supseteq \text{cov}_S(x)$. Thus $S'$ cannot be strictly subsumed by any fair AXp (by maximality of $S^*$), nor by any unfair AXp $T$ (otherwise $\text{cov}_S(x) \subseteq \text{cov}_{S'}(x) \subsetneq \text{cov}_T(x)$, contradicting the hypothesis on $S$). Hence $S'$ is a fair PI-explanation. $\blacksquare$

---

## 2. Complexity Overview (P1–P7)

| ID | Problem | Paper Reference | Reduction Source | Exact Complexity | Rocq File & Main Theorem(s) | Axiom Dependencies |
| :---: | :--- | :--- | :--- | :---: | :--- | :--- |
| **P1** | Decision Existential Fairness | Def. 5, Prop. 27 | $\exists X\forall Y\exists Z\ \Phi_{\text{3-CNF}}$ | **$\Sigma_3^P$-complete** | `verify_p1.v`<br>`p1_sigma3p_equiv_literal` | `Classical_Prop.classic` |
| **P2** | Unfair PI-Explanation Existence | Defs. 4–5, Prop. 27 | $\exists X\forall Y\exists Z\ \Phi_{\text{3-CNF}}$ | **$\Sigma_3^P$-complete** | `verify_p2_p3.v`<br>`p2_sigma3p_equiv` | `Classical_Prop.classic` |
| **P3** | Decision Universal Fairness | Def. 5, Prop. 27 | $\forall X\exists Y\forall Z\ \neg\Phi_{\text{3-CNF}}$ | **$\Pi_3^P$-complete** | `verify_p2_p3.v`<br>`p3_pi3p_equiv` | `Classical_Prop.classic` |
| **P4** | Classifier Existential Fairness | Def. 15, Prop. 28 | $\forall W\exists X\forall Y\exists Z\ \Phi_{\text{3-CNF}}$ | **$\Pi_4^P$-complete** | `verify_p4.v`<br>`p4_pi4p_equiv_literal` | `Classical_Prop.classic`<br>(`p4_constrained_ftu`: **0 axioms**) |
| **P5** | Classifier Universal Fairness | Def. 15, Prop. 28 | $\forall X\exists Y\forall Z\ \neg\Phi_{\text{3-CNF}}$ | **$\Pi_3^P$-complete** | `verify_p5.v`<br>`p5_pi3p_equiv` | `Classical_Prop.classic`<br>(`p5_constrained_ftu`: **0 axioms**) |
| **P6** | Looseness of $\mathcal{C}$ on $\mathcal{P}$ | Def. 22, Prop. 31 | $\forall X\exists Z\ \neg\Phi_{\text{3-DNF}}$ | **$\Pi_2^P$-complete** | `verify_pi2p.v`<br>`looseness_pi2p_equiv` | **0 axioms (constructive)** |
| **P7** | Disentangledness of $\kappa$ | Def. 25, Prop. 31 | $\forall X\exists Z\ \neg\Phi_{\text{3-DNF}}$ | **$\Pi_2^P$-complete** | `verify_pi2p.v`<br>`disentangled_pi2p_equiv` | **0 axioms (constructive)** |

---

## 3. $\Pi_2^P$-Completeness of P6 (Looseness) and P7 (Disentangledness)

> **Core Intuition**: In Definition 22 (looseness), blocking $\{p^*\}$ from strictly subsuming $\mathcal{N}$ does not require flipping $p^*$ in isolation; it allows **simultaneously adjusting the remaining protected features $Z \in \mathcal{P}\setminus\{p^*\}$** to preserve constraint satisfaction. Placing the outer 2-QBF variables $X$ in $\mathcal{N}$, the inner variables $Z$ in $\mathcal{P}$, and adding a selector feature $d \in \mathcal{N}$ so that $d=0$ forms an unconstrained region yields a single pure 5-CNF reduction for both P6 and P7.

**Rocq File**: `verify_pi2p.v` (theorems `looseness_pi2p_equiv` and `disentangled_pi2p_equiv`; fully constructive, 0 axioms).

### Theorem 3.1
Deciding looseness (P6) and deciding disentangledness (P7) are both **$\Pi_2^P$-complete** (even when the constraint is restricted to a polynomial-size pure 5-CNF formula and the classifier is a single-feature projection).

### Reduction Construction
We reduce from the dual form of $\Pi_2\text{SAT}$: given a 3-DNF formula $\Phi_{\text{DNF}}(X, Z)$ over variables $X \in \{0,1\}^r, Z \in \{0,1\}^s$ ($r \ge 1$), decide
$$\neg\exists X \in \{0,1\}^r\ \forall Z \in \{0,1\}^s\ \Phi_{\text{DNF}}(X, Z) = 1 \quad \Longleftrightarrow \quad \forall X \in \{0,1\}^r\ \exists Z \in \{0,1\}^s\ \neg\Phi_{\text{DNF}}(X, Z) = 1.$$
Note that $\neg\Phi_{\text{DNF}}(X, Z)$ is a polynomial-size 3-CNF formula.

- **Feature Partition**:
  - Unprotected features $\mathcal{N} = \{d, X_0, \dots, X_{r-1}\}$;
  - Protected features $\mathcal{P} = \{p^*, Z_0, \dots, Z_{s-1}\}$.
- **Constraint and Classifier**:
  $$\mathcal{C}_{\text{red}}(d, X, p^*, Z) \equiv (\neg d) \lor p^* \lor \neg\Phi_{\text{DNF}}(X, Z), \qquad \kappa_d(d, X, p^*, Z) = d.$$
  Writing $\neg\Phi_{\text{DNF}} = \bigwedge_\ell C_\ell$, we have $\mathcal{C}_{\text{red}} \equiv \bigwedge_\ell (\neg d \lor p^* \lor C_\ell)$, a polynomial-size pure 5-CNF.

### Proof

**Upper Bound**: $\text{P6}, \text{P7} \in \Pi_2^P$ is proved in Proposition 31 of Cooper & Bousdira (CP 2026).

#### Part I: Equivalence for P6 (Looseness)
- **($\Rightarrow$) Assume $\forall X \exists Z\ \neg\Phi_{\text{DNF}}(X, Z) = 1$**:
  Let $x \in \mathbb{F}[\mathcal{C}_{\text{red}}]$ and $p \in \mathcal{P}$. It suffices to construct a valid instance $z \in \mathbb{F}[\mathcal{C}_{\text{red}}]$ with $z|_{\mathcal{N}} = x|_{\mathcal{N}}$ and $z_p \neq x_p$ (so $\text{cov}_{\mathcal{N}}(x) \not\subseteq \text{cov}_{\{p\}}(x)$):
  1. If $d(x) = 0$: every $d=0$ instance satisfies $\mathcal{C}_{\text{red}}$, so simply flip $p$;
  2. If $d(x) = 1$ and $p = Z_j$: set $z = (d=1, X(x), p^*=1, Z(x)[Z_j := \neg Z_j(x)])$, which satisfies $\mathcal{C}_{\text{red}}(z)=1$ since $p^*=1$;
  3. If $d(x) = 1$ and $p = p^*$:
     - If $p^*(x) = 0$, set $z = (d=1, X(x), p^*=1, Z(x))$, which gives $\mathcal{C}_{\text{red}}(z) = 1$;
     - If $p^*(x) = 1$, choose $Z$ such that $\neg\Phi_{\text{DNF}}(X(x), Z) = 1$ and set $z = (d=1, X(x), p^*=0, Z)$, which gives $\mathcal{C}_{\text{red}}(z) = 1$.
  
  Hence $\{p\}$ never strictly subsumes $\mathcal{N}$, and $\mathcal{C}_{\text{red}}$ is loose.

- **($\Leftarrow$) Assume there exists $X \in \{0,1\}^r$ such that $\forall Z\ \Phi_{\text{DNF}}(X, Z) = 1$**:
  Consider the valid instance $x = (d=1, X, p^*=1, \vec{0})$ (valid since $p^*=1$).
  - For every $z \in \text{cov}_{\mathcal{N}}(x)$, we have $d(z)=1$ and $X(z)=X$, so $\neg\Phi_{\text{DNF}}(X, Z(z))=0$; hence $\mathcal{C}_{\text{red}}(z)=1$ forces $p^*(z) = 1 = p^*(x)$, giving $\text{cov}_{\mathcal{N}}(x) \subseteq \text{cov}_{\{p^*\}}(x)$;
  - Meanwhile, the valid point $y = (d=0, X, p^*=1, \vec{0})$ lies in $\text{cov}_{\{p^*\}}(x) \setminus \text{cov}_{\mathcal{N}}(x)$ since $d(y)=0 \neq 1$.
  
  Thus $\{p^*\}$ strictly subsumes $\mathcal{N}$ at $x$, and $\mathcal{C}_{\text{red}}$ is not loose.

#### Part II: Equivalence for P7 (Disentangledness, $r \ge 1$)
Since $\kappa_d(w) = d(w)$ and $d \in \mathcal{N}$, $\mathcal{N}$ is automatically a Weak AXp of $\langle \kappa_d, x \rangle$ at every valid $x$.
- **($\Rightarrow$) Assume $\forall X \exists Z\ \neg\Phi_{\text{DNF}}(X, Z) = 1$**:
  If an unfair Weak AXp $Q$ strictly subsumed $\mathcal{N}$ at some $x$, pick $p \in Q \cap \mathcal{P}$; then $\text{cov}_{\mathcal{N}}(x) \subsetneq \text{cov}_Q(x) \subseteq \text{cov}_{\{p\}}(x)$, so $\{p\}$ strictly subsumes $\mathcal{N}$, contradicting P6. Hence $\kappa_d$ is disentangled.
- **($\Leftarrow$) Assume there exists $X$ such that $\forall Z\ \Phi_{\text{DNF}}(X, Z) = 1$**:
  Take $x = (d=1, X, p^*=1, \vec{0}) \in \mathbb{F}[\mathcal{C}_{\text{red}}]$ and the unfair subset $Q = \{d, p^*\}$ ($p^* \in Q \cap \mathcal{P}$).
  - Since $d \in Q$ and $\kappa_d(w) = d(w)$, $Q$ is a Weak AXp of $\langle \kappa_d, x \rangle$;
  - As in the reverse direction of P6, every $z \in \text{cov}_{\mathcal{N}}(x)$ satisfies $d(z)=1$ and $p^*(z)=1$, so $\text{cov}_{\mathcal{N}}(x) \subseteq \text{cov}_Q(x)$;
  - Since $r \ge 1$, the point $y = (d=1, X[X_0 := \neg X_0], p^*=1, \vec{0})$ is valid (as $p^*=1$) and lies in $\text{cov}_Q(x) \setminus \text{cov}_{\mathcal{N}}(x)$.
  
  Therefore the unfair Weak AXp $Q$ strictly subsumes $\mathcal{N}$, and $\kappa_d$ is not disentangled. $\blacksquare$

---

## 4. $\Sigma_3^P$-Completeness of P1 (Decision Existential Fairness)

> **Core Intuition**: To simulate $\exists X \forall Y \exists Z\ \Phi(X, Y, Z) = 1$, a selector feature $d$ partitions the valid space into two layers:
> - **Upper layer ($d=1$)** encodes $\exists X$: the target instance $x^* = \vec{1}$ lies in the upper layer, and any fair Weak AXp $S \subseteq \mathcal{N}$ must include $d=1$ and at least one rail from each dual-rail pair $(X_i^+, X_i^-)$, thereby encoding an assignment $X$. The constraint forces $p=1$ and $Y_j^+ = Y_j^- = 1$ on the upper layer (when $x\_ok = 1$).
> - **Lower layer ($d=0, p=1$)** encodes $\forall Y \exists Z$: the constraint enforces mutually exclusive dual-rail encodings on $(X_i^+, X_i^-)$ and $(Y_j^+, Y_j^-)$, while $\kappa_{P1}$ outputs $\neg\Phi(X^+, Y^+, Z)$. If there exists a "bad $Y^*$" such that $\forall Z\ \Phi(X, Y^*, Z)=0$, an unfair subset $T$ can drop $d=1$ and carry $p=1$ along with the corresponding rails of $Y^*$ to jump into the lower layer while keeping $\kappa_{P1}=1$, strictly subsuming $S$.

**Rocq File**: `verify_p1.v` (theorem `p1_sigma3p_equiv_literal`, bridged to literal Definition 5 via `weak_fair_to_pi_fair` / `pi_fair_to_weak_fair`).

### Theorem 4.1 (Closing Open Question P1 on p. 12 / Proposition 27 of CP 2026)
Deciding whether a decision $\langle \mathcal{C}, \kappa, x^* \rangle$ has a fair PI-explanation (P1) is **$\Sigma_3^P$-complete**.

### Reduction Construction
We reduce from a standard $\Sigma_3\text{SAT}$ instance $\Psi = \exists X \in \{0,1\}^r\ \forall Y \in \{0,1\}^q\ \exists Z \in \{0,1\}^s\ \Phi(X, Y, Z) = 1$, where $\Phi$ is a 3-CNF formula (so $\neg\Phi$ is a polynomial-size 3-DNF).

- **Feature Partition**:
  - Unprotected features $\mathcal{N} = \{d\} \cup \{X_i^+, X_i^-\}_{i<r}$;
  - Protected features $\mathcal{P} = \{p\} \cup \{Y_j^+, Y_j^-\}_{j<q} \cup \{Z_k\}_{k<s}$.
- **Target Instance**: $x^* = \vec{1}$ (all features set to $1$).
- **Auxiliary Predicates**:
  $$x\_ok(w) \equiv \bigwedge_{i<r} (X_i^+ \lor X_i^-), \quad x\_uniq(w) \equiv \bigwedge_{i<r} (X_i^+ \oplus X_i^-),$$
  $$y\_uniq(w) \equiv \bigwedge_{j<q} (Y_j^+ \oplus Y_j^-), \quad all\_Y(w) \equiv \bigwedge_{j<q} (Y_j^+ \land Y_j^-).$$
- **Constraint $\mathcal{C}_{P1}$ and Classifier $\kappa_{P1}$**:
  $$\mathcal{C}_{P1}(w) \equiv \begin{cases}
    p \land all\_Y(w) & \text{if } d = 1 \land x\_ok(w),\\
    1 & \text{if } d = 1 \land \neg x\_ok(w),\\
    x\_uniq(w) \land y\_uniq(w) & \text{if } d = 0 \land p = 1,\\
    1 & \text{if } d = 0 \land p = 0,
  \end{cases}
  \qquad
  \kappa_{P1}(w) \equiv \begin{cases}
    x\_ok(w) & \text{if } d = 1,\\
    \neg\Phi(X^+, Y^+, Z) & \text{if } d = 0 \land p = 1,\\
    0 & \text{if } d = 0 \land p = 0.
  \end{cases}$$

Clearly $\mathcal{C}_{P1}(x^*) = 1$ and $\kappa_{P1}(x^*) = 1$.

### Proof

**Upper Bound**: $\text{P1} \in \Sigma_3^P$ is established in Proposition 27 of Cooper & Bousdira (CP 2026). By Lemma 1.1, it suffices to prove that $\Psi$ holds iff there exists a fair Weak AXp $S \subseteq \mathcal{N}$ not strictly subsumed by any unfair Weak AXp $T$.

#### 1. ($\Rightarrow$) If $\Psi$ holds, then $x^*$ is existentially fair
Pick a witness $X \in \{0,1\}^r$ for $\forall Y \exists Z\ \Phi(X, Y, Z) = 1$, and define the fair subset
$$S_X = \{d\} \cup \{X_i^+ \mid X_i = 1\} \cup \{X_i^- \mid X_i = 0\} \subseteq \mathcal{N}.$$
Clearly $S_X$ is a fair Weak AXp of $x^*$ ($d=1$ and $x\_ok=1 \implies \kappa_{P1}=1$).

For contradiction, suppose an unfair Weak AXp $T$ strictly subsumes $S_X$, i.e., $\text{cov}_{S_X}(x^*) \subsetneq \text{cov}_T(x^*)$, and pick a witness $v \in \text{cov}_T(x^*) \setminus \text{cov}_{S_X}(x^*)$.
1. **Eliminating redundant features via $\text{cov}_{S_X}(x^*) \subseteq \text{cov}_T(x^*)$**:
   - Flipping any $Z_k$ in $x^*$ to $0$ stays in $\text{cov}_{S_X}(x^*)$, so $\forall k < s,\ Z_k \notin T$;
   - For each $i < r$, flipping the unselected rail of $(X_i^+, X_i^-)$ (i.e., $X_i^-$ if $X_i=1$, or $X_i^+$ if $X_i=0$) in $x^*$ to $0$ stays in $\text{cov}_{S_X}(x^*)$, so the unselected rail is not in $T$.
2. **Case analysis on $d \in T$**:
   - **Case A: $d \in T$**. Then every $u \in \text{cov}_T(x^*)$ has $d(u) = 1$. If $T$ omitted the selected rail of some pair $(X_i^+, X_i^-)$ in $S_X$ (so neither $X_i^+$ nor $X_i^-$ is in $T$), setting $(X_i^+, X_i^-) = (0,0)$ in $x^*$ produces a valid $d=1, \neg x\_ok$ instance in $\text{cov}_T(x^*)$ with $\kappa_{P1}=0 \neq 1$, contradicting that $T$ is a Weak AXp. Thus $S_X \subseteq T$, forcing $v \in \text{cov}_{S_X}(x^*)$, a contradiction.
   - **Case B: $d \notin T$**.
     - **First show $p \in T$**: Consider $w^{(0,0)} = (d=0, p=0, X^+=X^-=\vec{1}, Y^+=Y^-=\vec{1}, Z=\vec{1})$. We have $\mathcal{C}_{P1}(w^{(0,0)})=1$ and $\kappa_{P1}(w^{(0,0)})=0 \neq 1$; since all features except $d, p$ equal $1$, $d \notin T$ and $T$ being a Weak AXp force **$p \in T$**.
     - **Next show $\forall j < q,\ \neg(Y_j^+ \in T \land Y_j^- \in T)$**: If $Y_{j_0}^+, Y_{j_0}^- \in T$ for some $j_0 < q$, then $p \in T$ rules out $d=0, p=0$, while $Y_{j_0}^+=Y_{j_0}^-=1$ violates $y\_uniq$ and rules out $d=0, p=1$. Thus $\text{cov}_T(x^*)$ is forced to stay in $d=1$ (in particular $d(v)=1$). Just as in Case A, avoiding $d=1, \neg x\_ok$ ($\kappa=0$) forces $T$ to contain every selected rail of $S_X$, yielding $v \in \text{cov}_{S_X}(x^*)$, a contradiction.
     - **Lower-layer counterexample**: Set $Y^*_j := \neg(Y_j^- \in T)$ (i.e., $Y^*_j=0$ if $Y_j^- \in T$, else $1$). By choice of $X$, there exists $Z^*$ such that $\Phi(X, Y^*, Z^*) = 1$. Consider the $d=0, p=1$ instance
       $$w_{(X, Y^*, Z^*)} = (d=0, p=1, X^+=X, X^-=\neg X, Y^+=Y^*, Y^-=\neg Y^*, Z=Z^*).$$
       We verify $\mathcal{C}_{P1}(w_{(X,Y^*,Z^*)})=1$ and $w_{(X,Y^*,Z^*)} \in \text{cov}_T(x^*)$ (since $Y_j^+, Y_j^-$ are never both in $T$, $Y^*_j$ satisfies all $Y^+/Y^-$ constraints of $T$), yet $\kappa_{P1}(w_{(X,Y^*,Z^*)}) = \neg\Phi(X, Y^*, Z^*) = 0 \neq 1$, contradicting that $T$ is a Weak AXp.

#### 2. ($\Leftarrow$) If $x^*$ is existentially fair, then $\Psi$ holds
Let $S \subseteq \mathcal{N}$ be a fair Weak AXp not strictly subsumed by any unfair Weak AXp.
1. **$d \in S$**: Since $w^{(0,0)} = (d=0, p=0, \vec{1})$ is valid, has $\kappa_{P1}=0 \neq 1$, and equals $1$ on $\mathcal{N}\setminus\{d\}$, we must have $d \in S$.
2. **$\forall i < r,\ X_i^+ \in S \lor X_i^- \in S$**: Otherwise setting $(X_i^+, X_i^-) = (0,0)$ in $x^*$ gives a valid point with $\kappa_{P1}=0 \neq 1$, a contradiction.
3. Define $X_i := (X_i^+ \in S)$ (whenever $X_i=0$, we must have $X_i^- \in S$). We claim that for every $Y \in \{0,1\}^q$ there exists $Z$ such that $\Phi(X, Y, Z) = 1$:
   Otherwise, if $\forall Z,\ \Phi(X, Y, Z) = 0$ for some $Y$, define the unfair subset ($p \in T$):
   $$T = \{p\} \cup \{X_i^+ \mid X_i = 1\} \cup \{X_i^- \mid X_i = 0\} \cup \{Y_j^+ \mid Y_j = 1\} \cup \{Y_j^- \mid Y_j = 0\}.$$
   - **$T$ is a Weak AXp**: On $d=1$, $T$ guarantees $x\_ok=1$ ($\kappa=1$); on $d=0$, $p \in T$ rules out $p=0$, and $x\_uniq \land y\_uniq$ together with $T$ force $X^+=X, Y^+=Y$, giving $\kappa_{P1} = \neg\Phi(X, Y, Z) = 1$.
   - **$\text{cov}_S(x^*) \subsetneq \text{cov}_T(x^*)$**: Any $u \in \text{cov}_S(x^*)$ satisfies $d(u)=1$ and $x\_ok(u)=1$, so $\mathcal{C}_{P1}(u)=1$ forces $p(u)=1$ and $all\_Y(u)=1$, giving $u \in \text{cov}_T(x^*)$; meanwhile $w_{(X, Y, \vec{0})} \in \text{cov}_T(x^*) \setminus \text{cov}_S(x^*)$ since $d \in S$.
   
   This contradicts that $S$ is not strictly subsumed by any unfair Weak AXp. Hence $\Psi$ holds. $\blacksquare$

---

## 5. Completeness of P2 (Unfair PI-Explanation Existence) and P3 (Decision Universal Fairness)

> **Core Intuition**: Reusing the exact constraint and classifier of P1, we simply set the **unique protected feature to be the selector bit $\mathcal{P} = \{d\}$**. Upper-layer explanations containing $d$ immediately become **unfair**, whereas lower-layer explanations dropping $d$ and carrying $p=1$ become **fair**—achieving an exact duality between existential fairness and unfair PI-explanation existence.

**Rocq File**: `verify_p2_p3.v` (theorems `p2_sigma3p_equiv` and `p3_pi3p_equiv`, verified directly against literal Definitions 3–5).

### Theorem 5.1 (Closing Open Questions P2 & P3 on p. 12 / Proposition 27 of CP 2026)
Deciding whether a decision has an unfair PI-explanation (P2) is **$\Sigma_3^P$-complete**; its complement, deciding universal fairness of a decision (P3), is **$\Pi_3^P$-complete**.

### Reduction Construction
Set $\mathcal{C}_{P2} = \mathcal{C}_{P1}$, $\kappa_{P2} = \kappa_{P1}$, and $x^* = \vec{1}$, while partitioning the features as
$$\mathcal{P} = \{d\}, \qquad \mathcal{N} = \{X_i^+, X_i^-\}_{i<r} \cup \{p\} \cup \{Y_j^+, Y_j^-\}_{j<q} \cup \{Z_k\}_{k<s}.$$
Thus a subset $T \subseteq \mathcal{F}$ is unfair if and only if $d \in T$.

### Proof

**Upper Bounds**: $\text{P2} \in \Sigma_3^P$ and $\text{P3} \in \Pi_3^P$ follow from Proposition 27 of Cooper & Bousdira (CP 2026). We prove $\Psi \iff x^*$ has an unfair PI-explanation:

- **($\Rightarrow$) If $\Psi$ holds**: Pick a witness $X \in \{0,1\}^r$ and define
  $$T_X = \{d\} \cup \{X_i^+ \mid X_i = 1\} \cup \{X_i^- \mid X_i = 0\}.$$
  1. **Unfairness**: $d \in T_X \cap \mathcal{P}$.
  2. **Minimality ($T_X$ is an AXp)**: $T_X$ is a Weak AXp. Removing $d$ is refuted by $w^{(0,0)} = (d=0, p=0, \vec{1})$ ($\kappa=0$); removing the selected rail of pair $i$ is refuted by $x^*[X_i^+:=0, X_i^-:=0]$ ($d=1, \neg x\_ok, \kappa=0$). Hence $T_X$ is a minimal AXp.
  3. **Coverage Maximality ($T_X$ is a PI-explanation)**: Suppose any AXp (in fact any Weak AXp) $S \subseteq \mathcal{F}$ strictly subsumes $T_X$. Verbatim as in Theorem 4.1 ($\Rightarrow$)—eliminating $Z_k$ and unselected rails, then branching on $d \in S$ vs. $d \notin S \implies p \in S$—every case yields a contradiction. Hence $T_X$ is an unfair PI-explanation.

- **($\Leftarrow$) If there exists an unfair PI-explanation $T$**:
  Since $T$ is unfair, $d \in T$; since $T$ is a Weak AXp and $d=1, \neg x\_ok$ imposes no extra constraints, every $i < r$ satisfies $X_i^+ \in T \lor X_i^- \in T$ (in fact exactly one holds by minimality of $T$). Set $X_i := (X_i^+ \in T)$.
  If there existed $Y \in \{0,1\}^q$ with $\forall Z\ \Phi(X, Y, Z) = 0$, then as in Theorem 4.1 the subset
  $$S = \{p\} \cup \{X_i^+ \mid X_i = 1\} \cup \{X_i^- \mid X_i = 0\} \cup \{Y_j^+ \mid Y_j = 1\} \cup \{Y_j^- \mid Y_j = 0\}$$
  would be a Weak AXp strictly subsuming $T$ ($\text{cov}_T(x^*) \subsetneq \text{cov}_S(x^*)$). By Lemma 1.1(1), there exists an AXp $S' \subseteq S$ that also strictly subsumes $T$, contradicting that $T$ is a PI-explanation. Thus $\Psi$ holds.

Since P3 is the exact complement of P2 (`p3_pi3p_equiv`), P3 is **$\Pi_3^P$-complete**. $\blacksquare$

---

## 6. $\Pi_3^P$-Completeness of P5 (Classifier Universal Fairness)

> **Core Obstacle & Technique — "$(0,0)$-Absorbing Non-Exclusive Encoding"**:
> Unlike the single-instance problem P3, classifier universal fairness (P5) requires **every valid instance $x \in \mathbb{F}[\mathcal{C}]$** (including points in the lower $d=0$ region!) to have **no unfair PI-explanation**.
>
> If we kept the mutually exclusive encoding $Y_j^+ \oplus Y_j^- = 1$ in the lower layer $d=0, p=1$, then literals $Y_j^+=1$ and $Y_j^-=0$ would have identical coverage in the lower layer, causing unfair AXps containing $d=0$ and fair AXps without $d$ to tie in coverage and preventing strict subsumption.
>
> **Solution**: In the lower layer $d=0, p=1$, replace mutual exclusion with the **no-double-1 constraint** $x\_not11 \land y\_not11$ (allowing three states $(1,0), (0,1), (0,0)$ per pair), and make $(0,0)$ an **absorbing state where $\kappa = 0$**! Then for any $x \in \{d=0, p=1\}$ with $\kappa(x)=0$, dualizing positive literals $Y_j^+=1$ in an unfair AXp to negative literals $Y_j^-=0$ and replacing $d=0$ with $p=1$ produces a fair Weak AXp whose coverage **strictly gains the $(0,0)$ absorbing state**, breaking every lower-layer tie.

**Rocq File**: `verify_p5.v` (theorem `p5_constrained_ftu` with 0 axioms; main theorem `p5_pi3p_equiv`).

### Theorem 6.1 (Closing Open Problem P5 in Section 7 / Proposition 28 of CP 2026)
Deciding whether a classifier satisfies universal fairness (P5) is **$\Pi_3^P$-complete**.

### Reduction Construction
Assume $r \ge 1, q \ge 1$. We reduce from the $\Pi_3\text{SAT}$ instance $\neg\Psi \equiv \forall X \in \{0,1\}^r\ \exists Y \in \{0,1\}^q\ \forall Z \in \{0,1\}^s\ \neg\Phi_{\text{3-CNF}}(X, Y, Z) = 1$.

- **Feature Partition**: Unique protected feature $\mathcal{P} = \{d\}$; unprotected features $\mathcal{N} = \{X_i^+, X_i^-\}_{i<r} \cup \{p\} \cup \{Y_j^+, Y_j^-\}_{j<q} \cup \{Z_k\}_{k<s}$.
- **New Auxiliary Predicates**:
  $$x\_not11(w) \equiv \bigwedge_{i<r} \neg(X_i^+ \land X_i^-), \qquad y\_not11(w) \equiv \bigwedge_{j<q} \neg(Y_j^+ \land Y_j^-),$$
  $$\text{dummy\_body}(w) \equiv \Big(\bigwedge_{i<r}(X_i^+ \land X_i^-)\Big) \land \Big(\bigwedge_{j<q}(\neg Y_j^+ \land \neg Y_j^-)\Big) \land \Big(\bigwedge_{k<s} \neg Z_k\Big).$$
- **Constraint $\mathcal{C}_{P5}$ and Classifier $\kappa_{P5}$**:
  $$\mathcal{C}_{P5}(w) \equiv \begin{cases}
    all\_Y(w) \land p & \text{if } d = 1 \land x\_ok(w),\\
    all\_Y(w) & \text{if } d = 1 \land \neg x\_ok(w),\\
    x\_not11(w) \land y\_not11(w) & \text{if } d = 0 \land p = 1,\\
    \text{dummy\_body}(w) & \text{if } d = 0 \land p = 0 \quad (\text{unique } \texttt{inst\_dummy}),
  \end{cases}$$
  $$\kappa_{P5}(w) \equiv \begin{cases}
    x\_ok(w) & \text{if } d = 1,\\
    0 & \text{if } d = 0 \land p = 1 \land \big(\exists i,\ \neg X_i^+ \land \neg X_i^- \ \lor\ \exists j,\ \neg Y_j^+ \land \neg Y_j^-\big),\\
    \neg\Phi(X^+, Y^+, Z) & \text{if } d = 0 \land p = 1 \land x\_uniq(w) \land y\_uniq(w),\\
    0 & \text{if } d = 0 \land p = 0.
  \end{cases}$$

### Proof

**Upper Bound**: $\text{P5} \in \Pi_3^P$ is proved in Proposition 28 of Cooper & Bousdira (CP 2026).

#### Property 0 (Constrained FTU holds unconditionally, `p5_constrained_ftu`)
Since $q \ge 1$, $d=1$ forces $(Y_0^+, Y_0^-) = (1, 1)$, whereas $d=0$ enforces $\neg(Y_0^+ \land Y_0^-)$ for both $p=1$ ($y\_not11$) and $p=0$ ($\text{dummy\_body}$). Hence the unique protected feature $d$ is uniquely determined by $(Y_0^+, Y_0^-) \subseteq \mathcal{N}$, so Constrained FTU holds unconditionally.

#### Direction 1 ($\neg\Psi \implies$ Classifier satisfies P5)
Assume $\forall X \exists Y^* \forall Z\ \Phi(X, Y^*, Z) = 0$. Let $x \in \mathbb{F}[\mathcal{C}_{P5}]$ be any valid instance and $T$ be any unfair Weak AXp ($d \in T$). We partition into 4 exhaustive cases and show in each case that $T$ is not a PI-explanation (either $T$ is not a minimal AXp, or there exists a Weak AXp $S$ strictly subsuming $T$, which by Lemma 1.1(1) yields an AXp $S' \subseteq S$ strictly subsuming $T$):

- **Case 1: $d(x)=1 \land x\_ok(x)=1$ ($\kappa(x)=1, p(x)=1, all\_Y(x)=1$, `neg_three_qbf_case_d1_true`)**  
  For each $i < r$, $T$ must contain at least one rail $X_i^+$ or $X_i^-$ evaluating to $1$ at $x$ (otherwise setting $(X_i^+, X_i^-)=(0,0)$ yields a valid $d=1, \neg x\_ok$ point with $\kappa=0 \neq 1$). Set $X_i := (X_i^+ \in T \land X_i^+(x)=1)$ (when $X_i=0$, we have $X_i^- \in T \land X_i^-(x)=1$). By $\neg\Psi$, pick $Y^*$ such that $\forall Z\ \Phi(X, Y^*, Z)=0$, and construct the fair subset:
  $$S = \{p\} \cup \{X_i^+ \mid X_i = 1\} \cup \{X_i^- \mid X_i = 0\} \cup \{Y_j^+ \mid Y^*_j = 1\} \cup \{Y_j^- \mid Y^*_j = 0\} \subseteq \mathcal{N}.$$
  - **$S$ is a Weak AXp**: On $d=1$, $S$ ensures $x\_ok=1$ ($\kappa=1$); on $d=0$, $p \in S$ forces $p=1$, and $x\_not11 \land y\_not11$ together with the $1$-literals in $S$ force $x\_uniq \land y\_uniq$ with $X^+=X, Y^+=Y^*$, so $\kappa_{P5} = \neg\Phi(X, Y^*, Z) = 1$.
  - **$\text{cov}_T(x) \subsetneq \text{cov}_S(x)$**: Every $u \in \text{cov}_T(x)$ has $d(u)=1, x\_ok(u)=1$, so the constraint forces $p(u)=1, all\_Y(u)=1$, placing $u \in \text{cov}_S(x)$; meanwhile $w_{(X, Y^*, \vec{0})} \in \text{cov}_S(x) \setminus \text{cov}_T(x)$ since $d \in T$. Thus $T$ is not a PI-explanation.

- **Case 2: $d(x)=1 \land x\_ok(x)=0$ ($\kappa(x)=0$, `neg_three_qbf_case_d1_false`)**  
  We show $T$ is not a minimal AXp:
  - **Subcase 2a ($p \in T \land p(x)=0$)**: The strict subset $S_p = \{p\} \subsetneq T$ (omitting $d$) forces $\kappa_{P5}=0$ globally ($d=1, p=0 \implies \neg x\_ok$; $d=0, p=0 \implies \kappa=0$), contradicting minimality of $T$;
  - **Subcase 2b (otherwise: $p \notin T$ or $p(x)=1$)**: There must exist $i_0 < r$ such that $X_{i_0}^+, X_{i_0}^- \in T$ and $X_{i_0}^+(x) = X_{i_0}^-(x) = 0$ (otherwise, setting every rail not fixed to $0$ by $T$ to $1$ and setting $p=1$ produces a valid $w \in \text{cov}_T(x)$ with $d=1, x\_ok=1, \kappa=1 \neq 0$, a contradiction). Then the strict subset $S_{i_0} = \{X_{i_0}^+, X_{i_0}^-\} \subsetneq T$ forces $\kappa_{P5}=0$ globally (violating $x\_ok$ when $d=1$, entering the $(0,0)$ absorbing state when $d=0, p=1$, and $0$ when $d=0, p=0$), contradicting minimality.

- **Case 3: $d(x)=0 \land p(x)=0$ (the unique `inst_dummy`, $\kappa(x)=0$, `neg_three_qbf_case_d0_p0`)**  
  - **Subcase 3a ($T$ fixes some $Y_{j_0}^+$ or $Y_{j_0}^-$)**: At `inst_dummy` that feature equals $0$, which already excludes $d=1$ (which requires $all\_Y$), so $T \setminus \{d\} \subsetneq T$ remains a Weak AXp, contradicting minimality;
  - **Subcase 3b ($T$ contains no $Y_j^+, Y_j^-$)**: Take the fair subset $S_p = \{p\} \subseteq \mathcal{N}$ (at $x$, $p(x)=0$). As in Case 2a, $S_p$ is a Weak AXp. Claim $\text{cov}_T(x) \subseteq \text{cov}_{S_p}(x)$:
    Suppose for contradiction there exists $u \in \text{cov}_T(x)$ with $p(u)=1$ (so $p \notin T$ and $d(u)=0$). Because $u$ satisfies $x\_not11(u)$ while `inst_dummy` has $X_i^+=X_i^-=1$, $T$ cannot contain both rails of any pair $(X_i^+, X_i^-)$! Setting $X_i := (X_i^+ \in T)$ and picking $Y^*$ via $\neg\Psi$ yields the lower-layer point $w_{(X, Y^*, \vec{0})} \in \text{cov}_T(x)$ (note $Z(\text{dummy})=\vec{0}$) with $\kappa_{P5} = \neg\Phi(X, Y^*, \vec{0}) = 1 \neq 0$, a contradiction.
    Moreover, since $r \ge 1$, the valid point $(d=1, p=0, X^+=X^-=\vec{0}, Y^+=Y^-=\vec{1}, Z=\vec{0})$ lies in $\text{cov}_{S_p}(x) \setminus \text{cov}_T(x)$, so $S_p$ strictly subsumes $T$.

- **Case 4: $d(x)=0 \land p(x)=1$ (`neg_three_qbf_case_d0_p1`)**  
  - **Subcase 4a ($T$ contains some $Y_{j_0}^+$ or $Y_{j_0}^-$ taking value $0$ at $x$)**: This $0$-literal already rules out $d=1$, so $T \setminus \{d\} \subsetneq T$ remains a Weak AXp, contradicting minimality;
  - **Subcase 4b (otherwise, and $\kappa_{P5}(x)=1$)**: Since $\kappa_{P5}(x)=1$, for each $i < r$, $T$ must fix the rail taking value $1$ at $x$ (otherwise flipping it to $0$ enters the $(0,0)$ absorbing state and gives $\kappa=0 \neq 1$). Hence $T \setminus \{d\} \subsetneq T$ automatically guarantees $x\_ok=1$ ($\kappa=1$) on $d=1$, remaining a Weak AXp and contradicting minimality;
  - **Subcase 4c (otherwise, and $\kappa_{P5}(x)=0$)**: Here every $Y^+/Y^-$ feature in $T$ equals $1$ at $x$ (so by $y\_not11(x)$ its dual rail equals $0$ at $x$).
    1. *If $T$ contains some $Y_{j_0}^+$ or $Y_{j_0}^-$*: Construct the dual fair subset
       $$S = (T \setminus (\{d\} \cup \{Y_j^+, Y_j^-\}_{j<q})) \cup \{p\} \cup \{Y_j^- \mid Y_j^+ \in T\} \cup \{Y_j^+ \mid Y_j^- \in T\} \subseteq \mathcal{N}.$$
       - **$\text{cov}_T(x) \subseteq \text{cov}_S(x)$**: For every $u \in \text{cov}_T(x)$, $d(u)=0$ and $Y_{j_0}^+=1$ (or $Y_{j_0}^-=1$) rule out `inst_dummy`, so $p(u)=1$; by $y\_not11(u)$, $Y_j^+(u)=1 \implies Y_j^-(u)=0 = Y_j^-(x)$ (and dually), whence $u \in \text{cov}_S(x)$.
       - **$S$ is a Weak AXp**: Every $w \in \text{cov}_S(x)$ contains at least one $0$-valued $Y^+/Y^-$ rail (ruling out $d=1$) and has $p(w)=1$. Either $w$ agrees with $x$ on all $Y^+/Y^-$ features of $T$, giving $w \in \text{cov}_T(x) \implies \kappa(w)=0$, or some pair takes $(0,0)$ at $w$, entering the absorbing state and giving $\kappa(w)=0$.
       - **Strict subsumption**: Changing $(Y_{j_0}^+, Y_{j_0}^-)$ in $x$ to $(0,0)$ produces a valid point $v \in \text{cov}_S(x) \setminus \text{cov}_T(x)$.
    2. *If $T$ contains no $Y_j^+, Y_j^-$*: If there exists $i_0 < r$ with $X_{i_0}^+, X_{i_0}^- \in T \land X_{i_0}^+(x)=X_{i_0}^-(x)=0$, then $\{X_{i_0}^+, X_{i_0}^-\} \subsetneq T$ forces $\kappa=0$ globally, contradicting minimality; otherwise set $X_i := (X_i^+(x) \text{ if } X_i^+ \in T \text{ else } \neg X_i^-(x))$ and pick $Y^*$ via $\neg\Psi$ to obtain a valid point $w_{(X, Y^*, Z(x))} \in \text{cov}_T(x)$ with $\kappa_{P5} = \neg\Phi(X, Y^*, Z(x)) = 1 \neq 0$, a contradiction.

#### Direction 2 ($\Psi \implies$ Classifier violates P5, `three_qbf_implies_not_cls_univ_fair`)
If $\Psi$ holds, pick a witness $X$, and consider $x^* = \vec{1}$ and the unfair subset $T_X = \{d\} \cup \{X_i^+ \mid X_i=1\} \cup \{X_i^- \mid X_i=0\}$.
- **Minimality**: Dropping $d$ is refuted by the unique `inst_dummy` $= (d=0, p=0, X^+=X^-=\vec{1}, Y^+=Y^-=\vec{0}, Z=\vec{0})$ (since $T_X \setminus \{d\}$ contains only $X^+, X^-$ features and no $p, Y^+, Y^-, Z$, so `inst_dummy` $\in \text{cov}_{T_X \setminus \{d\}}(x^*)$ with $\kappa_{P5}=0 \neq 1$); dropping any $X_i^+/X_i^-$ is refuted by $d=1, X_i^+=X_i^-=0$.
- **Coverage Maximality**: Suppose an AXp $S$ strictly subsumes $T_X$. As in Theorem 4.1, eliminate $Z_k$ and unselected rails; if $d \in S$ or $Y_{j_0}^+, Y_{j_0}^- \in S$ for some $j_0$, then $S$ is trapped in $d=1$ (since $y\_not11$ rules out $d=0, p=1$ and `inst_dummy` has $Y_{j_0}^+=0$, ruling out $d=0, p=0$), yielding $\text{cov}_S(x^*) \subseteq \text{cov}_{T_X}(x^*)$, a contradiction. Otherwise set $Y_j := \neg(Y_j^- \in S)$ and pick $Z$ via $\Psi$ to get $w_{(X, Y, Z)} \in \text{cov}_S(x^*)$ with $\kappa_{P5}=0 \neq 1$, a contradiction.

Hence $T_X$ is an unfair PI-explanation of $x^*$, violating P5. $\blacksquare$

---

## 7. $\Pi_4^P$-Completeness of P4 (Classifier Existential Fairness)

> **Core Obstacle & Technique — "Looseness Shield"**:
> To match the four-quantifier prefix $\forall W \exists X \forall Y \exists Z\ \Phi(W, X, Y, Z) = 1$, the outer $\forall x \in \mathbb{F}[\mathcal{C}]$ ranges over a family of upper-layer target points $\{x_W\}_{W \in \{0,1\}^t}$, checking $\exists X \forall Y \exists Z\ \Phi$ at each $x_W$ via unfair subsets $T$ jumping across layers into the lower $d=0, \Phi$ region.
>
> **Bidirectional-Jump Obstacle**: If an unfair Weak AXp $T$ covers both $x_W$ and some lower-layer $\Phi=0$ point $x_\phi$, then symmetrically $T$ is also an unfair Weak AXp of $x_\phi$, threatening to subsume all fair explanations of $x_\phi$ in the reverse direction!
>
> **Solution (Looseness Shield)**: Use a **single protected feature $\mathcal{P} = \{p^*\}$**, make $\kappa_{P4}$ **completely independent of $p^*$** (so Constrained FTU holds unconditionally), and leave **$p^* \in \{0,1\}$ completely unconstrained on the lower $d=0, is\_phi$ region**! Then for every point $x$ in $is\_phi$, the fair set $S = \mathcal{N}$ covers $\{x, x[\neg p^*]\}$, whereas any unfair set $T$ must contain $p^*$ and thus excludes $x[\neg p^*]$, rendering the lower $\Phi$-region immune to reverse jumps—while $d=1$ still enforces $p^*=1$, allowing unfair $T$ to carry $p^*=1$ into the $p^*=1$ branch of $is\_phi$ to complete the reduction.

**Rocq File**: `verify_p4.v` (theorem `p4_constrained_ftu` with 0 axioms; main theorem `p4_pi4p_equiv_literal` bridged to literal Definitions 3, 4, 15 via finite coverage counting).

### Theorem 7.1 (Closing the Final Open Problem P4 in Section 7 / Proposition 28 of CP 2026)
Deciding whether a classifier satisfies existential fairness (P4) is **$\Pi_4^P$-complete**.

### Reduction Construction
Assume $t \ge 1, r \ge 1$. We reduce from a standard $\Pi_4\text{SAT}$ instance $\Omega = \forall W \in \{0,1\}^t\ \exists X \in \{0,1\}^r\ \forall Y \in \{0,1\}^q\ \exists Z \in \{0,1\}^s\ \Phi_{\text{3-CNF}}(W, X, Y, Z) = 1$.

- **Feature Partition**:
  - Protected features $\mathcal{P} = \{p^*\}$ (a single Boolean feature);
  - Unprotected features $\mathcal{N} = \{d, q_B, z_0\} \cup \{W_k^+, W_k^-\}_{k<t} \cup \{X_i^+, X_i^-\}_{i<r} \cup \{Y_j^+, Y_j^-\}_{j<q} \cup \{Z_m\}_{m<s}$.
- **Auxiliary Predicates**: $w\_ok, w\_uniq, x\_ok, x\_uniq, y\_uniq, all\_Y$ are defined as before, and
  $$all\_X(w) \equiv \bigwedge_{i<r} (X_i^+ \land X_i^-),$$
  $$is\_dummy(w) \equiv (\neg p^*) \land w\_ok(w) \land all\_X(w) \land all\_Y(w),$$
  $$is\_phi(w) \equiv w\_uniq(w) \land x\_uniq(w) \land y\_uniq(w).$$
  *Note that $is\_phi$ does not depend on $p^*$ (the Looseness Shield), and since $r \ge 1$, $is\_dummy$ and $is\_phi$ are mutually exclusive.*
- **Constraint $\mathcal{C}_{P4}$ and Classifier $\kappa_{P4}$**:
  $$\mathcal{C}_{P4}(w) \equiv \begin{cases}
    p^* \land all\_Y(w) \land (\neg q_B) & \text{if } d = 1 \land (w\_ok \land x\_ok) \land (w\_uniq \land all\_X),\\
    p^* \land all\_Y(w) \land q_B & \text{if } d = 1 \land (w\_ok \land x\_ok) \land \neg(w\_uniq \land all\_X),\\
    p^* \land all\_Y(w) \land (\neg q_B) & \text{if } d = 1 \land \neg(w\_ok \land x\_ok),\\
    (\neg q_B) \land \big(is\_dummy(w) \lor is\_phi(w)\big) & \text{if } d = 0,
  \end{cases}$$
  $$\kappa_{P4}(w) \equiv \begin{cases}
    w\_ok(w) \land x\_ok(w) & \text{if } d = 1,\\
    1 & \text{if } d = 0 \land is\_phi(w) \land z_0 = 0,\\
    \neg\Phi(W^+, X^+, Y^+, Z) & \text{if } d = 0 \land is\_phi(w) \land z_0 = 1,\\
    0 & \text{if } d = 0 \land \neg is\_phi(w).
  \end{cases}$$

### Proof

**Upper Bound**: $\text{P4} \in \Pi_4^P$ is proved in Proposition 28 of Cooper & Bousdira (CP 2026). Since $\kappa_{P4}$ is syntactically independent of $p^*$, Constrained FTU holds unconditionally (`p4_constrained_ftu`).

#### Direction 1 ($\Omega \implies$ Classifier satisfies P4)
By Lemma 1.1, we partition $\mathbb{F}[\mathcal{C}_{P4}]$ into 6 exhaustive regions and exhibit in each region a fair Weak AXp $S \subseteq \mathcal{N}$ not strictly subsumed by any unfair Weak AXp $T$ ($p^* \in T$):

1. **Region 1 (Looseness Shield: $d(x)=0, is\_phi(x)=1$, `case_d0_phi`)**  
   Take $S = \mathcal{N}$. By Constrained FTU, $S$ is a fair Weak AXp. Flipping $p^*$ yields a valid instance $u = x[p^* := \neg p^*(x)] \in \text{cov}_{\mathcal{N}}(x)$; any unfair $T$ contains $p^*$, so $u \notin \text{cov}_T(x)$, meaning $\text{cov}_{\mathcal{N}}(x) \not\subseteq \text{cov}_T(x)$.

2. **Region 2 (Dummy region: $d(x)=0, is\_phi(x)=0$, i.e., $is\_dummy(x)=1, p^*(x)=0, \kappa(x)=0$, `case_d0_dummy`)**  
   Since $r \ge 1$, take $S_{\text{dummy}} = \{d, X_0^+, X_0^-\} \subseteq \mathcal{N}$ (values $0, 1, 1$). Since $X_0^+=X_0^-=1$ violates $x\_uniq$, $S_{\text{dummy}}$ is a Weak AXp. If an unfair Weak AXp $T$ ($p^* \in T$) strictly subsumes $S_{\text{dummy}}$:
   - Flipping $z_0(x)$ stays in $\text{cov}_{S_{\text{dummy}}}(x)$, so $z_0 \notin T$;
   - Pick $v \in \text{cov}_T(x) \setminus \text{cov}_{S_{\text{dummy}}}(x)$: $p^*(v)=p^*(x)=0$ rules out $d=1$, so $d(v)=0$; moreover $v \notin \text{cov}_{S_{\text{dummy}}}(x)$ violates $all\_X$, making $is\_dummy(v)=0$, so the constraint forces $is\_phi(v)=1$;
   - Setting $v_0 = v[z_0 := 0]$ gives a valid $v_0 \in \text{cov}_T(x)$ with $\kappa_{P4}(v_0)=1 \neq 0$, a contradiction.

3. **Region 3a (Invalid gate: $d(x)=1, w\_ok(x)=0, \kappa(x)=0$, `case_d1_w_not_ok`)**  
   Pick $k_0 < t$ with $W_{k_0}^+(x)=W_{k_0}^-(x)=0$ and set $S_{w0} = \{W_{k_0}^+, W_{k_0}^-\} \subseteq \mathcal{N}$. Every $w \in \text{cov}_{S_{w0}}(x)$ has $w\_ok(w)=0, is\_phi(w)=0 \implies \kappa(w)=0$. If $T$ strictly subsumes $S_{w0}$, then $T$ omits either $W_{k_0}^+$ or $W_{k_0}^-$ (WLOG $W_{k_0}^+ \notin T$). Take the base point
   $$u_{\text{base}} = (d=1, q_B=0, z_0(x), W_{k_0}^+=0, W_{k\neq k_0}^+=1, W^-=\vec{0}, X^+=X^-=Y^+=Y^-=\vec{1}, Z(x), p^*=1) \in \text{cov}_{S_{w0}}(x) \subseteq \text{cov}_T(x).$$
   Changing $W_{k_0}^+$ to $1$ in $u_{\text{base}}$ yields $w_{\text{hit}}$, which satisfies $w\_uniq \land all\_X$ (so $q_B=0$ is valid), lies in $\text{cov}_T(x)$, and has $\kappa_{P4}(w_{\text{hit}})=1 \neq 0$, a contradiction.

4. **Region 3b (Invalid gate: $d(x)=1, w\_ok(x)=1, x\_ok(x)=0$, whence $q_B(x)=0, p^*(x)=1, \kappa(x)=0$, `case_d1_x_not_ok`)**  
   Pick $i_0 < r$ with $X_{i_0}^+(x)=X_{i_0}^-(x)=0$ and set $S_{x0} = \{d, q_B, X_{i_0}^+\} \subseteq \mathcal{N}$ (values $1, 0, 0$). When $d=1, q_B=0$, $X_{i_0}^+=0$ implies $all\_X=0$, while $w\_ok \land x\_ok \land \neg all\_X$ requires $q_B=1$, so $\text{cov}_{S_{x0}}(x)$ always satisfies $\neg(w\_ok \land x\_ok)$ and $\kappa=0$.
   Suppose an unfair Weak AXp $T$ ($p^* \in T$) strictly subsumes $S_{x0}$, and pick $v \in \text{cov}_T(x) \setminus \text{cov}_{S_{x0}}(x)$:
   - Flipping $z_0(x)$ stays in $\text{cov}_{S_{x0}}(x)$, so $z_0 \notin T$;
   - **Lemma `unfair_weak_axp_kappa0_p1_forces_d1`**: Since $p^*(v)=p^*(x)=1, \kappa(x)=0$, and $z_0 \notin T$, we must have $d(v)=1$ (if $d(v)=0$, $p^*=1$ rules out $is\_dummy$ and forces $is\_phi(v)=1$, so setting $z_0=0$ yields $\kappa=1 \neq 0$, a contradiction);
   - From $d(v)=1$ and $v \notin \text{cov}_{S_{x0}}(x)$, either $q_B \notin T$ or $X_{i_0}^+ \notin T$;
   - **Dual-base splicing construction** (`u_base_A` and `u_base_B` in `verify_p4.v`): Take two valid base points in $\text{cov}_{S_{x0}}(x) \subseteq \text{cov}_T(x)$:
     $$u_{\text{base}, A} = (d=1, q_B=0, z_0(x), W^+=\vec{1}, W^-=\vec{0}, X_{i_0}^+=X_{i_0}^-=0, X_{i\neq i_0}^+=X_{i\neq i_0}^-=1, Y^+=Y^-=\vec{1}, Z(x), p^*=1),$$
     $$u_{\text{base}, B} = (d=1, q_B=0, z_0(x), W^+=\vec{0}, W^-=\vec{0}, X_{i_0}^+=0, X_{i\neq i_0}^+=1, X^-=\vec{1}, Y^+=Y^-=\vec{1}, Z(x), p^*=1)$$
     ($u_{\text{base}, A}$ is valid by $\neg x\_ok$; $u_{\text{base}, B}$ is valid by $\neg w\_ok$ using $t \ge 1$). Thus $T$ agrees with $u_{\text{base}, A}$ on $(d, z_0, W^+, W^-, X^+, Y^+, Y^-, Z, p^*)$ and with $u_{\text{base}, B}$ on $X^-=\vec{1}$. Combining these matching coordinates:
     - If $q_B \notin T$: take $u_{\text{base}, A}$'s remaining coordinates, replace $X^-$ by $\vec{1}$ from $u_{\text{base}, B}$, and set $q_B = 1$. The resulting $w_{\text{hit}}$ satisfies $w\_ok \land x\_ok \land \neg all\_X$ (since $X_{i_0}^+=0$), so $q_B=1$ is valid, $w_{\text{hit}} \in \text{cov}_T(x)$, and $\kappa_{P4}(w_{\text{hit}})=1 \neq 0$, a contradiction;
     - If $X_{i_0}^+ \notin T$: take $u_{\text{base}, A}$'s remaining coordinates, replace $X^-$ by $\vec{1}$ from $u_{\text{base}, B}$, and set $X_{i_0}^+ = 1$ (keeping $q_B=0$). The resulting $w_{\text{hit}}$ satisfies $w\_uniq \land all\_X$, so $q_B=0$ is valid, $w_{\text{hit}} \in \text{cov}_T(x)$, and $\kappa_{P4}(w_{\text{hit}})=1 \neq 0$, a contradiction.

5. **Region 4 (Auxiliary $q_B=1$ region: $d(x)=1, w\_ok \land x\_ok=1, \neg(w\_uniq \land all\_X)$, whence $q_B(x)=1, \kappa(x)=1$, `case_d1_qB1`)**  
   Take the singleton $S_{qB} = \{q_B\} \subseteq \mathcal{N}$. Globally, $q_B=1$ occurs only in this region, so $\kappa=1$ everywhere in $\text{cov}_{S_{qB}}(x)$. If $T$ strictly subsumes $S_{qB}$, then $q_B \notin T$; inside $\text{cov}_{S_{qB}}(x)$, setting $X_0^+=0, X_0^-=1$ (using $r \ge 1$ so $all\_X=0$) allows $W_0^+$ and $W_0^-$ (using $t \ge 1$) to flip freely, so $W_0^+ \notin T \land W_0^- \notin T$. Setting $(q_B, W_0^+, W_0^-) = (0,0,0)$ in $x$ gives a valid $w_{\text{bad}} \in \text{cov}_T(x)$ with $\neg w\_ok \implies \kappa_{P4}=0 \neq 1$, a contradiction.

6. **Region 5 (Target family $x_W$: $d(x)=1, w\_uniq \land all\_X = 1$, whence $q_B(x)=0, p^*(x)=1, all\_Y(x)=1, \kappa(x)=1$, `case_d1_target_W`)**  
   Define $W_k := W_k^+(x)$ (by $w\_uniq$, $W_k^-(x) = \neg W_k$). By $\Omega$, pick $X \in \{0,1\}^r$ such that $\forall Y \exists Z\ \Phi(W, X, Y, Z)=1$, and form the fair Weak AXp:
   $$S_{W, X} = \{d\} \cup \{W_k^+ \mid W_k=1\} \cup \{W_k^- \mid W_k=0\} \cup \{X_i^+ \mid X_i=1\} \cup \{X_i^- \mid X_i=0\} \subseteq \mathcal{N}.$$
   Suppose an unfair Weak AXp $T$ ($p^* \in T$) strictly subsumes $S_{W,X}$, and pick $v \in \text{cov}_T(x) \setminus \text{cov}_{S_{W,X}}(x)$:
   - **Witness 1 ($u_{\text{all1}} \in \text{cov}_{S_{W,X}}(x)$)**: Setting $d=1, q_B=1, z_0=\neg z_0(x), W^+=W^-=\vec{1}, X^+=X^-=Y^+=Y^-=\vec{1}, Z=\neg Z(x), p^*=1$ (violating $w\_uniq$ via $t \ge 1$, so $q_B=1$ is valid) shows $q_B \notin T, z_0 \notin T, \forall m\ (Z_m \notin T)$ and that $T$ contains no rail of $W^+/W^-$ contradicting $W$;
   - **Witness 2 ($u_X \in \text{cov}_{S_{W,X}}(x)$)**: Setting $d=1, q_B=1, W^+=W, W^-=\neg W, X^+=X, X^-=\neg X, Y^+=Y^-=\vec{1}, p^*=1$ (violating $all\_X$ via $r \ge 1$, so $q_B=1$ is valid) shows that $T$ contains no rail of $X^+/X^-$ contradicting $X$;
   - **If $d \in T$ or $\exists j_0,\ Y_{j_0}^+, Y_{j_0}^- \in T$**: Since $p^* \in T$ excludes $is\_dummy$, $\text{cov}_T(x)$ is trapped in $d=1$ (so $d(v)=1$), and avoiding $d=1, \neg(w\_ok \land x\_ok)$ ($\kappa=0$) forces $S_{W,X} \subseteq T$, giving $v \in \text{cov}_{S_{W,X}}(x)$, a contradiction;
   - **Otherwise ($d \notin T$ and $\forall j,\ \neg(Y_j^+, Y_j^- \in T)$)**: Set $Y_j := \neg(Y_j^- \in T)$ and pick $Z$ by choice of $X$ such that $\Phi(W, X, Y, Z)=1$. Then the lower-layer point
     $$w_\phi = (d=0, q_B=0, z_0=1, W^+=W, W^-=\neg W, X^+=X, X^-=\neg X, Y^+=Y, Y^-=\neg Y, Z=Z, p^*=1)$$
     is valid, lies in $\text{cov}_T(x)$, and has $\kappa_{P4}(w_\phi) = \neg\Phi(W, X, Y, Z) = 0 \neq 1$, a contradiction.

#### Direction 2 (Classifier satisfies P4 $\implies \Omega$, `cls_exist_fair_implies_four_qbf`)
Let $W \in \{0,1\}^t$ be arbitrary, and consider the valid target instance
$$x_W = (d=1, q_B=0, z_0=1, W^+=W, W^-=\neg W, X^+=X^-=\vec{1}, Y^+=Y^-=\vec{1}, Z=\vec{1}, p^*=1).$$
By P4 and Lemma 1.1, there exists a fair Weak AXp $S \subseteq \mathcal{N}$ ($p^* \notin S$) not strictly subsumed by any unfair Weak AXp.
1. **$d \in S$**: Setting $(d, p^*) = (0, 0)$ in $x_W$ produces the valid dummy point $y_{\text{dummy}, W}$ with $\kappa_{P4}=0 \neq 1$ (using $r \ge 1$ so $is\_phi=0$), which agrees with $x_W$ on $\mathcal{N}\setminus\{d\}$, forcing $d \in S$;
2. **Locking $W$ and $X$**: Similarly, zeroing the $1$-rail of $W_k$ (giving $\neg w\_ok$) or setting $(X_i^+, X_i^-) = (0,0)$ (giving $\neg x\_ok$) in $x_W$ yields valid points with $\kappa=0$, so $S$ must lock every $1$-rail of $W$ and satisfy $X_i^+ \in S \lor X_i^- \in S$ for all $i < r$;
3. Set $X_i := (X_i^+ \in S)$. Suppose for contradiction there exists $Y \in \{0,1\}^q$ such that $\forall Z\ \Phi(W, X, Y, Z) = 0$, and form the unfair subset ($p^* \in T$):
   $$T = \{p^*\} \cup \{W_k^+ \mid W_k=1\} \cup \{W_k^- \mid W_k=0\} \cup \{X_i^+ \mid X_i=1\} \cup \{X_i^- \mid X_i=0\} \cup \{Y_j^+ \mid Y_j=1\} \cup \{Y_j^- \mid Y_j=0\}.$$
   - **$T$ is a Weak AXp**: On $d=1$, $T$ guarantees $w\_ok \land x\_ok$ ($\kappa=1$); on $d=0$, $p^*=1$ excludes $is\_dummy$ and forces $is\_phi$, locking $W^+=W, X^+=X, Y^+=Y$, so $\kappa=1$ when $z_0=0$ and $\kappa = \neg\Phi(W, X, Y, Z) = 1$ when $z_0=1$;
   - **$\text{cov}_S(x_W) \subsetneq \text{cov}_T(x_W)$**: Every $u \in \text{cov}_S(x_W)$ has $d(u)=1$ (since $d \in S$), so the constraint forces $p^*(u)=1$ and $all\_Y(u)=1$, placing $u \in \text{cov}_T(x_W)$; meanwhile $w_\phi(W, X, Y, \vec{1}) \in \text{cov}_T(x_W) \setminus \text{cov}_S(x_W)$ (since $d \in S$).
   
   Contradiction! Hence $\forall W \exists X \forall Y \exists Z\ \Phi(W, X, Y, Z) = 1$ holds. $\blacksquare$
