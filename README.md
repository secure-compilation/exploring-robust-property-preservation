# Trace-Relating Compiler Correctness and Secure Compilation #

This repository contains the Coq development of the paper
**Trace-relating compiler correctness and secure sompilation**.

### Entry points ###

The paper includes includes direct pointers to the mechanizations of its main
results. From those theorems, formal definitions can quickly be found. The root
of all such references is the `Diff` folder.

 * Theorem 2.4 (coincidence of TPσ and TPτ):
   File ``NonRobustDef.v``, Corollary `Adj_σTP_iff_τTP`.

 * Theorem 2.6 (adjunction of the induced property mappings):
   File ``Galois.v``, Lemma `induced_adj_law`.

 * Theorem 2.7 (trinitarian equivalence):
   File `NonRobustTraceCriterion.v`, Theorems `rel_TC_τTP` and `rel_TC_σTP`.

 * Theorem 2.13 (preservation of subset-closed hyperproperties):
   File `NonRobustSSCHCriterion.v`, Theorems `rel_TC_sClτSCHP` and `rel_TC_sCl_σRSCHP`.

 * Example 3.1 (trace relation of a compiler with undefined behavior):
   File `UndefBehaviorCompCert.v`.

 * Example 3.3 (trace-relating compiler with resource exhaustion):
   File `ResourceExhaustion.v` and subfolder `ResourceExhaustion/`.

 * Theorem 3.4 (trace-relating compiler correctness with different source and target values):
   File `TypeRelationExampleInput.v`, Theorem `correctness`.

 * Theorem 3.11 (trace-preserving compilation and abstract noninterference):
   File `ANI.v` , Theorem `compiling_ANI`.

 * Theorem 4.3 (trinitarian equivalence for safety properties):
   File `NonRobustSafetyCriterion.v`, Theorems `tilde_SC_σSP` and `tilde_SC_Cl_τTP`.

 * Theorem 4.5 (weak trinitarian equivalence for non-subset closed hyperproperties):
   File `NonRobustHyperCriterion.v `, Theorem `rel_HC_τHP` and Lemma `rel_HC_σHP`.

 * Theorem 5.2 (trinitarian equivalence for robust trace properties):
   File `RobustTraceCriterion.v`, Theorems `rel_RTC_τRTP` and `rel_RTC_σRTP`.

 * Theorem 5.3 (robust trace-relating compiler correctness with extra observations in the target):
   File `MoreTargetEventsExample.v`, Corollary `extra_target_RTCt`.

 * Figure 3 (additional trinitarian equivalences):

    * Robust safety properties:
      File `RobustSafetyCriterion.v`, Theorems `tilde_RSC_σRSP` and `tilde_RSC_Cl_τRTP`.

    * Robust trace properties: Theorem 5.2.

    * Robust subset-closed hyperproperties:
      File `RobustSSCHCriterion.v`, Theorems `rel_RSCHC_sClτRSCHP` and `rel_RTC_σRTP`.

    * Robust hyperproperties:
      File `RobustHyperCriterion.v`, Theorems `rel_RHC_τRHP` and `rel_RHC_σRHP`.

    * Robust hypersafety properties:
      File `RobustHyperSafetyCriterion.v`, Theorems `rel_RHSC_sCl_σRHSP` and `rel_RHSC_hsCl_τRHSP`.

    * Robust 2-relational trace properties:
      File `Robust2relTraceCriterion.v`, Theorems `rel_R2rTC_τR2rTP` and `rel_R2rTC_σR2rTP`.

    * Robust 2-relational subset-closed hyperproperties:
      File `Robust2relSSCHCriterion.v`, Theorems `rel_R2rSCHC_sCl_τR2rSCHP` and `rel_R2rTC_σR2rTP`.

### Prerequisites for the Coq proofs ###

The Coq development is known to work with Coq v8.7.X, v8.8.X, and v8.9.X but it
has very few dependencies, so it will likely work with other versions as well.

### Replaying the Coq proofs ###

    $ make -j4

### License ###

This Coq development is licensed under the Apache License, Version 2.0 (see
`LICENSE`) unless overridden by another license file.
