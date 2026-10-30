This project was edited by [Aristotle] (https://aristotle.harmonic.fun).
This project was edited by [Claude] (https://claude.ai)

Every Theorem or Lemma statement proven in the paper has a Lean declaration, typically contained in a single file named after the Lemma/Theorem, which contains the main proof of that Lemma/Theorem. Some theorems (e.g. Theorems 4 and 5) are represented by multiple files. 

Every Hypothesis, Definition, Claim, Lemma, and Theorem statement has been hand-checked by the authors to ensure correctness of the Lean code.

Every declaration in the project has a docstring citing the paper. The main results reference their Theorem, Lemma, Definition, or Claim number. Helper Lemmas and Definitions that had no docstring got a generated one naming the result or section they support (e.g. "Auxiliary result for the proof of Theorem 4 (Section 7.3.4, Small-U case)").

The main theorems (Theorems 4 and 5, Lemma 7.9) use only Lean's standard axioms. Fact 2.2 (`HypergeomChernoff`) and the [ACN05] 3-approximation guarantee for PIVOT (`PivotThreeApprox`) are assumed as hypotheses, not proved, and no Chernoff bounds or other external results are formalized.

**Deviation from the paper.** In the Small-\(U\) case the Lean project measures \(\theta\) with \(T\) itself rather than the window start \(L_i\), and doesn't use the Small-\(U\) condition when bounding \(|U|\). Both changes only simplify the argument; the conclusion is the same. 

**Notes on AI usage.** We initially used Aristotle to build out the Lean code for the entire project. We did this by giving Aristotle our fully written paper and instructing it to formally verify every numbered Lemma and Theorem statement, assuming external results such as the Hypergeometric Chernoff bound and 3-Approximability of Pivot. We then hand-checked all Hypotheses, Definitions, Lemmas, and Theorem statements to ensure correctness of the Lean code. We then used Claude as an additional correctness check to again ensure the paper was encoded correctly. While doing this, we improved two Lemma statements (Lemmas 3.4 and 6.2). We then used Claude to update the Lean encodings of these Lemmas, and once again hand-checked their encodings.