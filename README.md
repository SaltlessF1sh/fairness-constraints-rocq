# Exact Complexity of Classifier Fairness Under Feature Constraints (P1–P7) — Rocq 9.0 Formalization

This repository provides **machine-checked Rocq (Coq 9.0) formal proofs** (over 5,300 lines, **0 `Admitted`**, **0 custom axioms**) along with full natural-language mathematical proofs (in English and Chinese) resolving **all 7 open computational complexity lower-bound problems (P1–P7)** posed in Section 7 (**Propositions 27, 28, and 31**) of:

> **Martin C. Cooper and Imane Bousdira (CP 2026)**, *"Fairness of Classifiers in the Presence of Constraints Between Features"*.

Our reductions establish that every polynomial-hierarchy membership upper bound identified in Cooper & Bousdira (CP 2026) is **tight** ($\Pi_2^P$-complete, $\Sigma_3^P$-complete, $\Pi_3^P$-complete, or $\Pi_4^P$-complete), ruling out collapse to lower complexity classes under general Boolean/CNF/DNF constraints and classifiers (and even under pure 5-CNF constraints + single-feature projection for P6 and P7).

> **Authorship & Verification Note**: This project was developed in **human–AI collaboration**. The natural-language mathematical proofs in [`docs/`](docs/) have been checked by a human author, and a preliminary consistency check has been conducted between the Rocq formalizations (`rocq_proofs/`) and the definitions/theorem statements in Cooper & Bousdira (CP 2026) and the natural-language proofs (all 5 `.v` files compile cleanly under Rocq 9.0 with `0 Admitted` and `0` custom axioms). Independent review and feedback are warmly welcome.

---

## Complexity Results & Formalization Summary (P1–P7)

| ID | Problem | Paper Reference | Reduction Source | Exact Complexity | Rocq File | Main Theorem(s) | Axiom Dependencies (`Print Assumptions`) |
| :---: | :--- | :--- | :--- | :---: | :--- | :--- | :--- |
| **P1** | Decision Existential Fairness | Def. 5, Prop. 27 | $\exists X \forall Y \exists Z\ \Phi_{\text{3-CNF}}$ | **$\Sigma_3^P$-complete** | [`rocq_proofs/verify_p1.v`](rocq_proofs/verify_p1.v) | `p1_sigma3p_equiv_literal` | `Classical_Prop.classic` |
| **P2** | Unfair PI-Explanation Existence | Defs. 4–5, Prop. 27 | $\exists X \forall Y \exists Z\ \Phi_{\text{3-CNF}}$ | **$\Sigma_3^P$-complete** | [`rocq_proofs/verify_p2_p3.v`](rocq_proofs/verify_p2_p3.v) | `p2_sigma3p_equiv` | `Classical_Prop.classic` |
| **P3** | Decision Universal Fairness | Def. 5, Prop. 27 | $\forall X \exists Y \forall Z\ \neg\Phi_{\text{3-CNF}}$ | **$\Pi_3^P$-complete** | [`rocq_proofs/verify_p2_p3.v`](rocq_proofs/verify_p2_p3.v) | `p3_pi3p_equiv` | `Classical_Prop.classic` |
| **P4** | Classifier Existential Fairness | Def. 15, Prop. 28 | $\forall W \exists X \forall Y \exists Z\ \Phi_{\text{3-CNF}}$ | **$\Pi_4^P$-complete** | [`rocq_proofs/verify_p4.v`](rocq_proofs/verify_p4.v) | `p4_constrained_ftu`,<br>`p4_pi4p_equiv_literal` | FTU: **Closed (0 axioms)**<br>Equiv: `Classical_Prop.classic` |
| **P5** | Classifier Universal Fairness | Def. 15, Prop. 28 | $\forall X \exists Y \forall Z\ \neg\Phi_{\text{3-CNF}}$ | **$\Pi_3^P$-complete** | [`rocq_proofs/verify_p5.v`](rocq_proofs/verify_p5.v) | `p5_constrained_ftu`,<br>`p5_pi3p_equiv` | FTU: **Closed (0 axioms)**<br>Equiv: `Classical_Prop.classic` |
| **P6** | Looseness of $\mathcal{C}$ on $\mathcal{P}$ | Def. 22, Prop. 31 | $\forall X \exists Z\ \neg\Phi_{\text{3-DNF}}$ | **$\Pi_2^P$-complete** | [`rocq_proofs/verify_pi2p.v`](rocq_proofs/verify_pi2p.v) | `looseness_pi2p_equiv` | **Closed (0 axioms)** |
| **P7** | Disentangledness of $\kappa$ | Def. 25, Prop. 31 | $\forall X \exists Z\ \neg\Phi_{\text{3-DNF}}$ | **$\Pi_2^P$-complete** | [`rocq_proofs/verify_pi2p.v`](rocq_proofs/verify_pi2p.v) | `disentangled_pi2p_equiv` | **Closed (0 axioms)** |

---

## Key Proof Techniques

1. **Dual-Rail Feature Encoding & Gate Selector (`P1–P3`)**: Encodes existential/universal QBF assignments via dual-rail pairs $(X_i^+, X_i^-)$ and $(Y_j^+, Y_j^-)$ gated by a selector feature $d$, distinguishing fair vs. unfair PI-explanations across layers (`P1` vs. `P2/P3`).
2. **$(0,0)$-Absorbing Non-Exclusive Encoding (`P5`)**: Relaxes $d=0, p=1$ mutual exclusion to $\neg(X_i^+ \land X_i^-) \land \neg(Y_j^+ \land Y_j^-)$ with a $\kappa = 0$ absorbing state at $(0,0)$, breaking all lower-layer coverage ties on quantified instances.
3. **Single-Protected "Looseness Shield" (`P4`)**: Uses a single protected feature $\mathcal{P} = \{p^*\}$ to which $\kappa_{P4}$ is invariant (ensuring Constrained FTU constructively) while leaving $p^* \in \{0,1\}$ unconstrained on the lower $\Phi$-evaluation region, blocking reverse cross-layer subsumption attacks.
4. **Pure 5-CNF + Single-Literal Projection (`P6, P7`)**: Encodes $\forall X \exists Z\ \neg\Phi_{\text{3-DNF}}(X,Z)$ via $\mathcal{C}_{\text{red}} \equiv \neg d \lor p^* \lor \neg\Phi_{\text{DNF}}(X,Z)$ and $\kappa_d = d$, proving both looseness and disentangledness $\Pi_2^P$-hard constructively with 0 axioms.

---

## Repository Structure

```text
fairness-constraints-rocq/
├── README.md
├── LICENSE
├── _CoqProject
├── .gitignore
├── run_all_verifications.ps1
├── rocq_proofs/
│   ├── verify_pi2p.v          # P6 & P7 (Pi_2^P-complete, 0 axioms)
│   ├── verify_p1.v            # P1 (Sigma_3^P-complete)
│   ├── verify_p2_p3.v         # P2 (Sigma_3^P-complete) & P3 (Pi_3^P-complete)
│   ├── verify_p5.v            # P5 (Pi_3^P-complete + Constrained FTU)
│   └── verify_p4.v            # P4 (Pi_4^P-complete + Constrained FTU)
└── docs/
    ├── natural_language_proofs_en.md  # Canonical mathematical proof (English)
    ├── natural_language_proofs_en.tex # LaTeX source (English, pdfLaTeX)
    ├── natural_language_proofs_en.pdf # Compiled English proof PDF
    ├── natural_language_proofs.md     # Canonical mathematical proof (Chinese)
    ├── natural_language_proofs.tex    # LaTeX source (Chinese, XeLaTeX)
    └── natural_language_proofs.pdf    # Compiled Chinese proof PDF
```

---

## Quick Verification

### Requirements
- **The Rocq Prover 9.0** (`coqc` / `coq_makefile`, tested with Rocq 9.0.1)

### Build via `coq_makefile` (Linux / macOS / Unix-like Make)

```bash
coq_makefile -f _CoqProject -o Makefile && make
```

### Build via PowerShell (Windows)

```powershell
powershell -ExecutionPolicy Bypass -File .\run_all_verifications.ps1
```

Both workflows compile all 5 `.v` files cleanly with exit code `0`, check for any `Admitted`/`admit`/`Abort`, and execute `Print Assumptions` at the end of each proof file.
