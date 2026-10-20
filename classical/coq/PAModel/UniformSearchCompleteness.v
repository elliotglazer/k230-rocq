(** Uniform completeness for the exact numerical seeded search.
    Internal proof lengths and command codes range over the given PA model. *)
From PAModel Require Import Model Arithmetic CodeExpressions NumericalProofs
 SearchStep KernelSafety RunSyntax UniformSearch NumericalReachability
 ProgramRealizability NumericalProofInduction RuntimeAxiomLeaves
 NumericalModusPonensCompiler ProgramGeneralization ProgramHaltSuffix.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Theorem numerical_proof_program_realizes M f :
 numerically_provable M f -> program_realizes M f.
Proof.
 apply(numerical_proof_induction M(program_realizes M)
   (program_realizes_definable M)).
 - exact(numerical_axiom_program_realizes M).
 - exact(program_realizes_modus_ponens M).
 - exact(program_realizes_gen M).
Qed.

Theorem uniform_numerical_search_complete M :
 numerically_provable M(code_numeral M 1) ->
 exists b c N,numerical_run M b c N /\ halt_at M b c N.
Proof.
 intro H. exact(program_realizes_one_halts M
   (numerical_proof_program_realizes M(code_numeral M 1)H)).
Qed.

Theorem uniform_numerical_search_iff M :
 numerically_provable M(code_numeral M 1) <->
 exists b c N,numerical_run M b c N /\ halt_at M b c N.
Proof.
 split;[apply uniform_numerical_search_complete|].
 intros[b[c[N[Hrun Hhalt]]]].
 exact(uniform_numerical_search_sound M b c N Hrun Hhalt).
Qed.

Definition numerical_search_completeness_sentence : form :=
 numerically_provable_formula(num 1) →
   ∃∃∃(run_formula $2 $1 $0 ∧ halt_at_formula $2 $1 $0).

Local Opaque holds numerically_provable_formula run_formula halt_at_formula.
Theorem numerical_search_completeness_sentence_valid M rho :
 holds M rho numerical_search_completeness_sentence.
Proof.
 unfold numerical_search_completeness_sentence.
 rewrite holds_imp,numerically_provable_formula_correct. intro H.
 destruct(uniform_numerical_search_complete M H)as[b[c[N[Hrun Hhalt]]]].
 rewrite holds_ex. exists b. rewrite holds_ex. exists c.
 rewrite holds_ex. exists N.
 rewrite holds_and,run_formula_correct,halt_at_formula_correct.
 exact(conj Hrun Hhalt).
Qed.

Print Assumptions numerical_proof_program_realizes.
Print Assumptions uniform_numerical_search_complete.
Print Assumptions uniform_numerical_search_iff.
Print Assumptions numerical_search_completeness_sentence_valid.
