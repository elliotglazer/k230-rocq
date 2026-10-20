(** A fixed two-entry beta certificate swaps source indices0,1. It acts on
    arbitrary internal formulas; its finite-formula calibration is separate. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  NumericalRenamingMaps NumericalRenaming NumericalSubstitution RenamingSubstitution
  SetFormulaCodes SourceBounded SourceRenamingBounds SchemaRenamingDescriptors
  SourceNumeralLift SubstitutionSource SourceSwap.
From FOL.Tennenbaum Require Import Peano.
From Undecidability.FOL Require Import Syntax.Core Syntax.Facts Syntax.BinSig Sets.Signatures.
From FOL Require Import FullSyntax.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Theorem source_fixed_swap_map M :source_swap_map M (code_numeral M 3) (code_numeral M 1).
Proof.
  split.
  - apply (proj2 (renaming_lookup_inside M _ _ _ _ (zeroM M) _ (coding_zero_lt_succ M (code_numeral M 1)))).
    apply (descriptor_beta_certificate M 3 1 0 1 1);reflexivity||lia.
  - apply (proj2 (renaming_lookup_inside M _ _ _ _ (code_numeral M 1) _ (coding_lt_succ M (code_numeral M 1)))).
    apply (descriptor_beta_certificate M 3 1 1 0 1);reflexivity||lia.
Qed.

Definition source_swap_sigma :nat->sf_term :=fun i=>
  match i with 0=>var 1|1=>var 0|S(S k)=>var(S(S k)) end.

Theorem source_fixed_swap_lookup M i :
  renaming_lookup M (code_numeral M 3) (code_numeral M 1) (code_numeral M 2) (zeroM M)
    (code_numeral M i) (code_numeral M (sf_index (source_swap_sigma i))).
Proof.
  destruct i as [|[|i]];[exact (proj1 (source_fixed_swap_map M))|
    exact (proj2 (source_fixed_swap_map M))|apply source_swap_tail].
Qed.

Theorem source_fixed_swap_bounded M f swapped n :
  source_bounded M f (succM M (succM M n)) ->
  numerical_renaming M f (code_numeral M 3) (code_numeral M 1)
    (code_numeral M 2) (zeroM M) swapped ->
  source_bounded M swapped (succM M (succM M n)).
Proof.
  intros HF HR. apply (numerical_renaming_preserves_bound M f _ _ _ _ swapped _ _ HF HR).
  intros i j HI HJ.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i) as [E|[i' E]];subst i.
  - assert (E:j=code_numeral M 1) by (eapply renaming_lookup_functional;[exact HJ|exact (proj1 (source_fixed_swap_map M))]).
    subst j. apply coding_lt_succ_cancel,coding_zero_lt_succ.
  - destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) i') as [E|[i'' E]];subst i'.
    + assert (E:j=zeroM M) by (eapply renaming_lookup_functional;[exact HJ|exact (proj2 (source_fixed_swap_map M))]).
      subst j. apply coding_zero_lt_succ.
    + assert (E:j=succM M(succM M i'')) by (eapply renaming_lookup_functional;[exact HJ|apply source_swap_tail]).
      now subst j.
Qed.

Theorem source_fixed_swap_finite_lift M (phi:sf_form) :
  numerical_renaming M (code_numeral M (sf_encode phi)) (code_numeral M 3)
    (code_numeral M 1) (code_numeral M 2) (zeroM M)
    (code_numeral M (sf_encode phi[source_swap_sigma])).
Proof.
  apply (proj2 (numerical_renaming_substitution M _ _ _ _ _ _)).
  rewrite coding_add_zero_r.
  apply (fixed_source_substitution M (fun _=>zeroM M) phi source_swap_sigma
    (code_numeral M 3) (code_numeral M 1) (code_numeral M 2) (code_numeral M 2) _ _).
  - intro i. pose proof (proj1 (renaming_substitution_lookup M _ _ _ (zeroM M) _ _)
      (source_fixed_swap_lookup M i)) as H. now rewrite coding_add_zero_r in H.
  - exact (source_formula_numeral_graph M phi).
  - exact (source_formula_numeral_graph M phi[source_swap_sigma]).
Qed.

Print Assumptions source_fixed_swap_map.
Print Assumptions source_fixed_swap_bounded.
Print Assumptions source_fixed_swap_finite_lift.
