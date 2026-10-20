(** All five inputs to selected-request assembly are proved here. Slots
    0..7 are distinct nonzero role names; slots 8 and 9 are the arbitrary
    predicate before and after the checked witness substitution. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates
  NamedLeibnizSteps NamedBinderFresh TemplateBinderFresh TemplateFormulaFresh
  TemplateNamedSubstitution NumericalSingleton NumericalTaggedComprehension
  TaggedSelectedOutput TaggedSelectedRequest TaggedSubsetFacts TaggedEligibility.
From Stdlib Require Import Lists.List Lia.
Unset Implicit Arguments.

Theorem numerical_tagged_selected_request M rho :
  (forall i j,i<8 -> j<8 -> i<>j -> rho i<>rho j) ->
  (forall i,i<8 -> rho i<>zeroM M) ->
  expression_named_substitution M rho rho (rho 0) (rho 1) (CEvar 8) (CEvar 9) ->
  expression_binder_absent M rho (rho 1) (CEvar 8) ->
  ns_proof M rho
    (E_wim (E_selected_exclusions (CEvar 1) (CEvar 2) (CEvar 4) (CEvar 5) (CEvar 7))
      (E_wim (E_wel (CEvar 3) (CEvar 6))
        (E_wim (E_tagged_local_request (CEvar 0) (CEvar 2) (CEvar 3) (CEvar 4)
          (CEvar 5) (CEvar 6) (CEvar 8) (E_raw_singleton (CEvar 0) (CEvar 2) (CEvar 7)))
          (E_wim (E_wa (E_wel (CEvar 1) (CEvar 3)) (CEvar 9)) (E_wel (CEvar 1) (CEvar 6)))))).
Proof.
  intros HD HN HTheta HB.
  apply (ns_proof_macro M rho
    (selected_request_inputs (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4)
      (CEvar 5) (CEvar 6) (CEvar 8) (CEvar 9) (CEvar 7))).
  - intros e [<-|[<-|[<-|[<-|[<-|[]]]]]].
    + apply (numerical_singleton_profile M rho (CEvar 1) (CEvar 0) (CEvar 2) (CEvar 7)
        (rho 1) (rho 0) (rho 2) (rho 7) eq_refl eq_refl eq_refl eq_refl);
        apply HD;lia.
    + apply (numerical_singleton_subset M rho (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 6) (CEvar 7)
        (rho 1) (rho 2) (rho 3) (rho 6) (rho 7) eq_refl eq_refl eq_refl eq_refl eq_refl).
      * apply HN;lia.
      * apply HD;lia.
      * apply HD;lia.
      * apply HD;lia.
      * apply HD;lia.
      * apply HD;lia.
      * apply HD;lia.
    + apply (numerical_tagged_eligibility M rho (CEvar 2) (CEvar 3) (CEvar 6) (CEvar 0) (CEvar 5)
        (rho 2) (rho 3) (rho 6) (rho 0) eq_refl eq_refl eq_refl eq_refl).
      * apply HN;lia.
      * apply HD;lia.
      * apply HD;lia.
      * apply HD;lia.
      * apply HD;lia.
    + apply (numerical_tagged_selected_output M rho (CEvar 0) (CEvar 1) (CEvar 2)
        (CEvar 3) (CEvar 4) (CEvar 5) (CEvar 8) (CEvar 9) (CEvar 7)
        (rho 0) (rho 1) (rho 7) eq_refl eq_refl eq_refl).
      * apply HN;lia.
      * apply HD;lia.
      * apply HD;lia.
      * apply HD;lia.
      * intros v HV. change (v=rho 2) in HV. subst v. apply HD;lia.
      * intros v HV. change (v=rho 3) in HV. subst v. apply HD;lia.
      * intros v HV. change (v=rho 4) in HV. subst v. apply HD;lia.
      * intros v HV. change (v=rho 5) in HV. subst v. apply HD;lia.
      * exact HTheta.
      * exact HB.
    + apply (numerical_tagged_witness_cleanup_fresh M rho (CEvar 0) (CEvar 1) (CEvar 2)
        (CEvar 3) (CEvar 4) (CEvar 5) (CEvar 6) (CEvar 8)
        (E_raw_singleton (CEvar 0) (CEvar 2) (CEvar 7)) (rho 0) eq_refl).
      * apply HN;lia.
      * intros v HV. change (v=rho 2) in HV. subst v. apply HD;lia.
      * intros v HV. change (v=rho 5) in HV. subst v. apply HD;lia.
      * intros v HV. change (v=rho 4) in HV. subst v. apply HD;lia.
      * intros v HV. change (v=rho 1) in HV. subst v. apply HD;lia.
      * intros v HV. change (v=rho 6) in HV. subst v. apply HD;lia.
  - apply tagged_selected_request_program.
Qed.

Print Assumptions numerical_tagged_selected_request.
