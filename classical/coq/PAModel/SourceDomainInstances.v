(** Domain predicates at arbitrary internally coded variables.  The domain
    is a source formula whose sole possible free variable is index zero. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  NumericalProofs SetCodeDescent SourceBounded SourceBoundMonotone
  NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation
  NumericalRenaming NumericalContextRenaming SourceQuantifierRules
  SourceSubstitutionIdentity SourceSubstitutionRenaming SourceRelativizationBounds.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Lemma domain_index_below_one M i : coding_lt M i (code_numeral M 1) -> i = zeroM M.
Proof.
  intro HI. destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i) as [E|[i' E]];[exact E|].
  subst i. change (coding_lt M (succM M i') (succM M (zeroM M))) in HI.
  exfalso. exact (coding_not_lt_zero M i' (proj1 (coding_lt_succ_cancel M i' (zeroM M)) HI)).
Qed.

Theorem source_domain_instance_zero M domain :
  source_bounded M domain (code_numeral M 1) ->
  numerical_instantiation M domain (zeroM M) domain.
Proof.
  intro HD. destruct (substitution_singleton_total M (zeroM M)) as [b [c [HH _]]].
  exists b,c. split;[exact HH|].
  apply (numerical_substitution_identity_on_bound M domain b c
    (succM M (zeroM M)) (zeroM M) (code_numeral M 1) HD).
  intros i HI. rewrite (domain_index_below_one M i HI). exact HH.
Qed.

Theorem source_domain_instance_shift M domain i f g :
  source_bounded M domain (code_numeral M 1) ->
  numerical_instantiation M domain i f -> source_formula_shift M f g ->
  numerical_instantiation M domain (succM M i) g.
Proof.
  intros HD [b [c [HH HF]]] HS.
  destruct (substitution_singleton_total M (succM M i)) as [d [e [HH' _]]].
  exists d,e. split;[exact HH'|].
  apply (numerical_substitution_then_renaming M domain (code_numeral M 1)
    b c (succM M (zeroM M)) (zeroM M)
    (zeroM M) (zeroM M) (zeroM M) (succM M (zeroM M))
    d e (succM M (zeroM M)) (zeroM M) f g HD HF HS).
  intros j u v HJ HU HV. rewrite (domain_index_below_one M j HJ) in *.
  assert (EU:u=i) by (eapply substitution_lookup_functional;[exact HU|exact HH]).
  subst u. apply context_shift_lookup in HV. subst v. exact HH'.
Qed.

Theorem source_domain_instance_bound M domain i f k :
  source_bounded M domain (code_numeral M 1) -> coding_lt M i k ->
  numerical_instantiation M domain i f -> source_bounded M f k.
Proof.
  intros HD HI HF. apply (numerical_instantiation_bounded M domain i f k).
  - exact (sr_domain_bound_succ M domain k HD).
  - exact HI.
  - exact HF.
Qed.

Print Assumptions source_domain_instance_zero.
Print Assumptions source_domain_instance_shift.
Print Assumptions source_domain_instance_bound.

