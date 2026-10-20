(** The constructed universal query can be consumed at its root and marker.
    Slot 6 is a formula code; the seven role names skip that slot. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates
  NamedLeibnizSteps FreshNames NamedBinderFresh NumericalSingleton
  NumericalTaggedComprehension NumericalTaggedKernel TaggedRequestSpecialization
  TaggedRootRequest TaggedMarkerRequest TaggedEligibility TaggedSubsetFacts
  NumericalKP0 NumericalKP0Eligibility NumericalKP0Requests TemplatePropositional ProofMacros.
From Stdlib Require Import Lists.List Lia.
Unset Implicit Arguments.

Definition tagged_request_role M (rho:nat->carrier M) idx :=
  match idx with 6=>rho 7|_=>rho idx end.
Definition tagged_request_roles_distinct M rho :=
  forall i j,i<7 -> j<7 -> i<>j -> tagged_request_role M rho i<>tagged_request_role M rho j.
Definition tagged_request_roles_nonzero M rho :=
  forall i,i<7 -> tagged_request_role M rho i<>zeroM M.

Theorem numerical_tagged_universal_root M rho :
  tagged_request_roles_distinct M rho -> tagged_request_roles_nonzero M rho ->
  formula_fresh M (rho 6) (rho 1) -> named_binder_absent M (rho 6) (rho 4) ->
  ns_proof M rho
    (E_wim (E_root_exclusions (CEvar 0) (CEvar 3) (CEvar 4)
      (E_raw_singleton (CEvar 0) (CEvar 4) (CEvar 7)))
      (E_wim (E_tagged_request_clause (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)
        (CEvar 4) (CEvar 5) (CEvar 6) (CEvar 7)) (E_wel (CEvar 2) (CEvar 5)))).
Proof.
  intros HD HN HF HB.
  assert (HS:ns_proof M rho
    (E_wim (E_tagged_request_clause (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)
      (CEvar 4) (CEvar 5) (CEvar 6) (CEvar 7))
      (E_tagged_local_request (CEvar 0) (CEvar 4) (CEvar 2) (CEvar 3)
        (CEvar 4) (CEvar 5) (CEvar 6) (E_raw_singleton (CEvar 0) (CEvar 4) (CEvar 7))))).
  { exact (numerical_tagged_request_specialization M (rho 0) (rho 1) (rho 4)
      (rho 2) (rho 3) (rho 4) (rho 5) (rho 7) (rho 6)
      (HN 1 ltac:(lia)) (HD 1 4 ltac:(lia) ltac:(lia) ltac:(lia))
      (HD 0 1 ltac:(lia) ltac:(lia) ltac:(lia)) (HD 0 4 ltac:(lia) ltac:(lia) ltac:(lia))
      (HD 5 1 ltac:(lia) ltac:(lia) ltac:(lia)) (HD 5 4 ltac:(lia) ltac:(lia) ltac:(lia))
      (HD 6 1 ltac:(lia) ltac:(lia) ltac:(lia)) (HD 6 4 ltac:(lia) ltac:(lia) ltac:(lia))
      (HD 2 1 ltac:(lia) ltac:(lia) ltac:(lia)) (HD 3 1 ltac:(lia) ltac:(lia) ltac:(lia))
      (HD 4 1 ltac:(lia) ltac:(lia) ltac:(lia)) HF HB). }
  assert (HC:ns_proof M rho
    (E_wim (E_root_exclusions (CEvar 0) (CEvar 3) (CEvar 4)
      (E_raw_singleton (CEvar 0) (CEvar 4) (CEvar 7)))
      (E_wim (E_tagged_local_request (CEvar 0) (CEvar 4) (CEvar 2) (CEvar 3)
        (CEvar 4) (CEvar 5) (CEvar 6) (E_raw_singleton (CEvar 0) (CEvar 4) (CEvar 7)))
        (E_wel (CEvar 2) (CEvar 5))))).
  { apply (numerical_tagged_root_request M rho (CEvar 0) (CEvar 2) (CEvar 3)
      (CEvar 4) (CEvar 5) (CEvar 6) (E_raw_singleton (CEvar 0) (CEvar 4) (CEvar 7))
      (rho 0) eq_refl (HN 0 ltac:(lia))).
    - intros v Hv. change (v=rho 4) in Hv. subst v. exact (HD 4 0 ltac:(lia) ltac:(lia) ltac:(lia)).
    - intros v Hv. change (v=rho 3) in Hv. subst v. exact (HD 3 0 ltac:(lia) ltac:(lia) ltac:(lia)).
    - intros v Hv. change (v=rho 2) in Hv. subst v. exact (HD 2 0 ltac:(lia) ltac:(lia) ltac:(lia)).
    - intros v Hv. change (v=rho 5) in Hv. subst v. exact (HD 5 0 ltac:(lia) ltac:(lia) ltac:(lia)). }
  apply (ns_proof_macro M rho
    ((E_wim (E_tagged_request_clause (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)
      (CEvar 4) (CEvar 5) (CEvar 6) (CEvar 7))
      (E_tagged_local_request (CEvar 0) (CEvar 4) (CEvar 2) (CEvar 3)
        (CEvar 4) (CEvar 5) (CEvar 6) (E_raw_singleton (CEvar 0) (CEvar 4) (CEvar 7)))) ::
    (E_wim (E_root_exclusions (CEvar 0) (CEvar 3) (CEvar 4)
      (E_raw_singleton (CEvar 0) (CEvar 4) (CEvar 7)))
      (E_wim (E_tagged_local_request (CEvar 0) (CEvar 4) (CEvar 2) (CEvar 3)
        (CEvar 4) (CEvar 5) (CEvar 6) (E_raw_singleton (CEvar 0) (CEvar 4) (CEvar 7)))
        (E_wel (CEvar 2) (CEvar 5)))) :: nil)).
  - intros e [<-|[<-|[]]];[exact HS|exact HC].
  - apply macro_discharge. do 2 apply macro_deduction.
    eapply md_mp.
    + eapply md_mp;[apply md_hyp;now left|]. apply md_global,PM_input;now left.
    + eapply md_mp;[apply md_hyp;now right;left|]. apply md_global,PM_input;now right;left.
Qed.

Print Assumptions numerical_tagged_universal_root.

Lemma tagged_marker_universal_program Empty Exclusions Member Request Local Eligible Subset Result :
  proof_macro nil
    (E_wim Request Local :: E_wim Exclusions (E_wim Local (E_wim Eligible Result)) ::
     E_wim (E_wa Member Subset) Eligible :: E_wim Empty Subset :: nil)
    (E_wim Empty (E_wim Exclusions (E_wim Member (E_wim Request Result)))).
Proof.
  apply macro_discharge. do 4 apply macro_deduction.
  eapply md_mp with (a:=Eligible).
  - eapply md_mp with (a:=E_wa Member Subset).
    + apply kp0_md_conjunction.
      * apply md_hyp;now right;left.
      * eapply md_mp with (a:=Empty).
        -- apply md_hyp;now right;right;right;left.
        -- apply md_global,PM_input;now right;right;right;left.
    + apply md_global,PM_input;now right;right;left.
  - eapply md_mp with (a:=Local).
    + eapply md_mp with (a:=Request);[apply md_hyp;now left|].
      apply md_global,PM_input;now left.
    + eapply md_mp with (a:=Exclusions);[apply md_hyp;now right;right;left|].
      apply md_global,PM_input;now right;left.
Qed.

Theorem numerical_tagged_universal_marker M rho :
  tagged_request_roles_distinct M rho -> tagged_request_roles_nonzero M rho ->
  formula_fresh M (rho 6) (rho 1) -> named_binder_absent M (rho 6) (rho 3) ->
  ns_proof M rho
    (E_wim (E_wal (CEvar 7) (E_wn (E_wel (CEvar 7) (CEvar 3))))
      (E_wim (E_marker_exclusions (CEvar 0) (CEvar 3) (CEvar 4)
        (E_raw_singleton (CEvar 0) (CEvar 3) (CEvar 7)))
        (E_wim (E_wel (CEvar 2) (CEvar 5))
          (E_wim (E_tagged_request_clause (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)
            (CEvar 4) (CEvar 5) (CEvar 6) (CEvar 7)) (E_wel (CEvar 3) (CEvar 5)))))).
Proof.
  intros HD HN HF HB.
  set (Req:=E_tagged_request_clause (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)
    (CEvar 4) (CEvar 5) (CEvar 6) (CEvar 7)).
  set (Loc:=E_tagged_local_request (CEvar 0) (CEvar 3) (CEvar 2) (CEvar 3)
    (CEvar 4) (CEvar 5) (CEvar 6) (E_raw_singleton (CEvar 0) (CEvar 3) (CEvar 7))).
  set (Excl:=E_marker_exclusions (CEvar 0) (CEvar 3) (CEvar 4)
    (E_raw_singleton (CEvar 0) (CEvar 3) (CEvar 7))).
  set (Elig:=E_kp_eligible (CEvar 4) (CEvar 0) (CEvar 5) (CEvar 3)).
  set (Sub:=E_ksubset (CEvar 3) (CEvar 2) (CEvar 5)).
  set (Emp:=E_wal (CEvar 7) (E_wn (E_wel (CEvar 7) (CEvar 3)))).
  apply (ns_proof_macro M rho
    (E_wim Req Loc :: E_wim Excl (E_wim Loc (E_wim Elig (E_wel (CEvar 3) (CEvar 5)))) ::
     E_wim (E_wa (E_wel (CEvar 2) (CEvar 5)) Sub) Elig :: E_wim Emp Sub :: nil)).
  - intros e [<-|[<-|[<-|[<-|[]]]]].
    + exact (numerical_tagged_request_specialization M (rho 0) (rho 1) (rho 3)
        (rho 2) (rho 3) (rho 4) (rho 5) (rho 7) (rho 6)
        (HN 1 ltac:(lia)) (HD 1 3 ltac:(lia) ltac:(lia) ltac:(lia))
        (HD 0 1 ltac:(lia) ltac:(lia) ltac:(lia)) (HD 0 3 ltac:(lia) ltac:(lia) ltac:(lia))
        (HD 5 1 ltac:(lia) ltac:(lia) ltac:(lia)) (HD 5 3 ltac:(lia) ltac:(lia) ltac:(lia))
        (HD 6 1 ltac:(lia) ltac:(lia) ltac:(lia)) (HD 6 3 ltac:(lia) ltac:(lia) ltac:(lia))
        (HD 2 1 ltac:(lia) ltac:(lia) ltac:(lia)) (HD 3 1 ltac:(lia) ltac:(lia) ltac:(lia))
        (HD 4 1 ltac:(lia) ltac:(lia) ltac:(lia)) HF HB).
    + apply (numerical_tagged_marker_request M rho (CEvar 0) (CEvar 2) (CEvar 3)
        (CEvar 4) (CEvar 5) (CEvar 6) (E_raw_singleton (CEvar 0) (CEvar 3) (CEvar 7))
        (rho 0) eq_refl (HN 0 ltac:(lia))).
      * intros v Hv. change (v=rho 4) in Hv. subst v. exact (HD 4 0 ltac:(lia) ltac:(lia) ltac:(lia)).
      * intros v Hv. change (v=rho 3) in Hv. subst v. exact (HD 3 0 ltac:(lia) ltac:(lia) ltac:(lia)).
      * intros v Hv. change (v=rho 5) in Hv. subst v. exact (HD 5 0 ltac:(lia) ltac:(lia) ltac:(lia)).
    + exact (numerical_tagged_eligibility M rho (CEvar 3) (CEvar 2) (CEvar 5) (CEvar 0) (CEvar 4)
        (rho 3) (rho 2) (rho 5) (rho 0) eq_refl eq_refl eq_refl eq_refl
        (HN 0 ltac:(lia)) (HD 0 2 ltac:(lia) ltac:(lia) ltac:(lia))
        (HD 5 0 ltac:(lia) ltac:(lia) ltac:(lia)) (HD 5 2 ltac:(lia) ltac:(lia) ltac:(lia))
        (HD 3 0 ltac:(lia) ltac:(lia) ltac:(lia))).
    + exact (numerical_empty_subset M rho (CEvar 3) (CEvar 2) (CEvar 5) (CEvar 7)
        (rho 3) (rho 5) (rho 7) eq_refl eq_refl eq_refl
        (HN 6 ltac:(lia)) (HN 5 ltac:(lia)) (HD 6 5 ltac:(lia) ltac:(lia) ltac:(lia))
        (HD 3 6 ltac:(lia) ltac:(lia) ltac:(lia)) (HD 3 5 ltac:(lia) ltac:(lia) ltac:(lia))).
  - apply tagged_marker_universal_program.
Qed.

Print Assumptions numerical_tagged_universal_marker.
