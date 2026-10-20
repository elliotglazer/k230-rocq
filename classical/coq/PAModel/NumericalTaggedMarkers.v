(** The actual pair and empty-marker facts discharge both exceptional
    query branches. The same constructed K contains B and T. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates
  NamedLeibnizSteps FreshNames NamedBinderFresh NumericalSingleton NumericalRawPair
  NumericalTaggedComprehension NumericalTaggedKernel TaggedRootRequest TaggedMarkerRequest
  TaggedUniversalRequests RawMarkerExclusions RawMarkerQuantifiers
  NumericalKP0 TemplatePropositional ProofMacros.
From Stdlib Require Import Lists.List Lia.
Unset Implicit Arguments.

Theorem numerical_tagged_markers M rho :
  tagged_request_roles_distinct M rho -> tagged_request_roles_nonzero M rho ->
  formula_fresh M (rho 6) (rho 1) ->
  named_binder_absent M (rho 6) (rho 4) -> named_binder_absent M (rho 6) (rho 3) ->
  ns_proof M rho
    (E_wim (E_marker_empty (CEvar 3) (CEvar 7))
      (E_wim (E_wn (E_weq (CEvar 2) (CEvar 3)))
        (E_wim (E_raw_pair (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 7))
          (E_wim (E_tagged_request_clause (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)
            (CEvar 4) (CEvar 5) (CEvar 6) (CEvar 7))
            (E_wa (E_wel (CEvar 2) (CEvar 5)) (E_wel (CEvar 3) (CEvar 5))))))).
Proof.
  intros HD HN HF HR HT.
  set (Emp:=E_marker_empty (CEvar 3) (CEvar 7)).
  set (Neq:=E_wn (E_weq (CEvar 2) (CEvar 3))).
  set (Pair:=E_raw_pair (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 7)).
  set (Req:=E_tagged_request_clause (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)
    (CEvar 4) (CEvar 5) (CEvar 6) (CEvar 7)).
  set (Sroot:=E_wal (CEvar 0) (E_wn (E_raw_singleton (CEvar 0) (CEvar 4) (CEvar 7)))).
  set (Smarker:=E_wal (CEvar 0) (E_wn (E_raw_singleton (CEvar 0) (CEvar 3) (CEvar 7)))).
  set (RnotT:=E_wn (E_weq (CEvar 4) (CEvar 3))).
  set (TnotR:=E_wn (E_weq (CEvar 3) (CEvar 4))).
  set (RootExcl:=E_wa RnotT Sroot).
  set (MarkerExcl:=E_wa TnotR Smarker).
  set (Bmem:=E_wel (CEvar 2) (CEvar 5)).
  set (Tmem:=E_wel (CEvar 3) (CEvar 5)).
  set (inputs:=
    E_wim Emp (E_wim Pair RnotT) ::
    E_wim Neq (E_wim Pair Sroot) ::
    E_wim Emp Smarker ::
    E_wim Emp (E_wim Pair TnotR) ::
    E_wim RootExcl (E_wim Req Bmem) ::
    E_wim Emp (E_wim MarkerExcl (E_wim Bmem (E_wim Req Tmem))) :: nil).
  apply (ns_proof_macro M rho inputs).
  - intros e [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
    + exact (numerical_pair_not_empty M rho (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 7)
        (rho 2) (rho 3) (rho 7) eq_refl eq_refl eq_refl
        (HN 6 ltac:(lia)) (HD 6 2 ltac:(lia) ltac:(lia) ltac:(lia))
        (HD 3 6 ltac:(lia) ltac:(lia) ltac:(lia))).
    + exact (numerical_pair_no_singletons M rho (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 0) (CEvar 7)
        (rho 2) (rho 3) (rho 4) (rho 0) (rho 7) eq_refl eq_refl eq_refl eq_refl eq_refl
        (HN 0 ltac:(lia)) (HD 6 2 ltac:(lia) ltac:(lia) ltac:(lia))
        (HD 6 3 ltac:(lia) ltac:(lia) ltac:(lia)) (HD 4 6 ltac:(lia) ltac:(lia) ltac:(lia))
        (HD 0 6 ltac:(lia) ltac:(lia) ltac:(lia)) (HD 2 0 ltac:(lia) ltac:(lia) ltac:(lia))
        (HD 3 0 ltac:(lia) ltac:(lia) ltac:(lia)) (HD 4 0 ltac:(lia) ltac:(lia) ltac:(lia))).
    + exact (numerical_empty_no_singletons M rho (CEvar 3) (CEvar 0) (CEvar 7)
        (rho 3) (rho 0) (rho 7) eq_refl eq_refl eq_refl
        (HN 6 ltac:(lia)) (HN 0 ltac:(lia)) (HD 6 0 ltac:(lia) ltac:(lia) ltac:(lia))
        (HD 3 6 ltac:(lia) ltac:(lia) ltac:(lia)) (HD 3 0 ltac:(lia) ltac:(lia) ltac:(lia))).
    + exact (numerical_pair_not_empty_reverse M rho (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 7)
        (rho 2) (rho 3) (rho 7) eq_refl eq_refl eq_refl
        (HN 6 ltac:(lia)) (HD 6 2 ltac:(lia) ltac:(lia) ltac:(lia))
        (HD 3 6 ltac:(lia) ltac:(lia) ltac:(lia))).
    + exact (numerical_tagged_universal_root M rho HD HN HF HR).
    + exact (numerical_tagged_universal_marker M rho HD HN HF HT).
  - apply macro_discharge. do 4 apply macro_deduction.
    set (delta:=Req :: Pair :: Neq :: Emp :: nil).
    assert (HRex:macro_derivation nil inputs delta RootExcl).
    { apply kp0_md_conjunction.
      - eapply md_mp with (a:=Pair);[apply md_hyp;now right;left|].
        eapply md_mp with (a:=Emp);[apply md_hyp;now right;right;right;left|].
        apply md_global,PM_input;now left.
      - eapply md_mp with (a:=Pair);[apply md_hyp;now right;left|].
        eapply md_mp with (a:=Neq);[apply md_hyp;now right;right;left|].
        apply md_global,PM_input;now right;left. }
    assert (HTex:macro_derivation nil inputs delta MarkerExcl).
    { apply kp0_md_conjunction.
      - eapply md_mp with (a:=Pair);[apply md_hyp;now right;left|].
        eapply md_mp with (a:=Emp);[apply md_hyp;now right;right;right;left|].
        apply md_global,PM_input;now right;right;right;left.
      - eapply md_mp with (a:=Emp);[apply md_hyp;now right;right;right;left|].
        apply md_global,PM_input;now right;right;left. }
    assert (HBmem:macro_derivation nil inputs delta Bmem).
    { eapply md_mp with (a:=Req);[apply md_hyp;now left|].
      eapply md_mp with (a:=RootExcl);[exact HRex|].
      apply md_global,PM_input;now right;right;right;right;left. }
    apply kp0_md_conjunction;[exact HBmem|].
    eapply md_mp with (a:=Req);[apply md_hyp;now left|].
    eapply md_mp with (a:=Bmem);[exact HBmem|].
    eapply md_mp with (a:=MarkerExcl);[exact HTex|].
    eapply md_mp with (a:=Emp);[apply md_hyp;now right;right;right;left|].
    apply md_global,PM_input;now right;right;right;right;right;left.
Qed.

Print Assumptions numerical_tagged_markers.
