(** The universal query can be applied to any fresh singleton query P.
    All exclusions are consequences of the actual empty marker and pair. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates
  NamedLeibnizSteps FreshNames NamedBinderFresh TemplateBinderFresh TemplateNamedSubstitution
  NumericalSingleton NumericalRawPair NumericalTaggedComprehension NumericalTaggedKernel
  TaggedRequestSpecialization TaggedSelectedRequest NumericalSelectedRequest
  RawMarkerExclusions RawMarkerTransport NumericalKP0 TemplatePropositional ProofMacros.
From Stdlib Require Import Lists.List Lia.
Unset Implicit Arguments.

Definition selected_query_role M (rho:nat->carrier M) idx :=
  match idx with 8=>rho 10|_=>rho idx end.
Definition selected_query_roles_distinct M rho :=
  forall i j,i<9 -> j<9 -> i<>j -> selected_query_role M rho i<>selected_query_role M rho j.
Definition selected_query_roles_nonzero M rho :=
  forall i,i<9 -> selected_query_role M rho i<>zeroM M.

Lemma universal_selected_program Emp Neq Pair Bmem Req Loc Sing NRoot NMarker Condition Result :
  proof_macro nil
    (E_wim Req Loc :: E_wim Emp (E_wim Sing NMarker) ::
     E_wim Neq (E_wim Pair (E_wim Sing NRoot)) ::
     E_wim (E_wa NRoot (E_wa NMarker Sing))
       (E_wim Bmem (E_wim Loc (E_wim Condition Result))) :: nil)
    (E_wim Emp (E_wim Neq (E_wim Pair (E_wim Bmem
      (E_wim Req (E_wim Sing (E_wim Condition Result))))))).
Proof.
  apply macro_discharge. do 7 apply macro_deduction.
  eapply md_mp with (a:=Condition);[apply md_hyp;now left|].
  eapply md_mp with (a:=Loc).
  - eapply md_mp with (a:=Req);[apply md_hyp;now right;right;left|].
    apply md_global,PM_input;now left.
  - eapply md_mp with (a:=Bmem);[apply md_hyp;now right;right;right;left|].
    eapply md_mp with (a:=E_wa NRoot (E_wa NMarker Sing)).
    + apply kp0_md_conjunction.
      * eapply md_mp with (a:=Sing);[apply md_hyp;now right;left|].
        eapply md_mp with (a:=Pair);[apply md_hyp;now right;right;right;right;left|].
        eapply md_mp with (a:=Neq);[apply md_hyp;now right;right;right;right;right;left|].
        apply md_global,PM_input;now right;right;left.
      * apply kp0_md_conjunction.
        -- eapply md_mp with (a:=Sing);[apply md_hyp;now right;left|].
           eapply md_mp with (a:=Emp);[apply md_hyp;now right;right;right;right;right;right;left|].
           apply md_global,PM_input;now right;left.
        -- apply md_hyp;now right;left.
    + apply md_global,PM_input;now right;right;right;left.
Qed.

Theorem numerical_tagged_universal_selected M rho :
  selected_query_roles_distinct M rho -> selected_query_roles_nonzero M rho ->
  formula_fresh M (rho 8) (rho 10) -> named_binder_absent M (rho 8) (rho 2) ->
  expression_named_substitution M rho rho (rho 0) (rho 1) (CEvar 8) (CEvar 9) ->
  expression_binder_absent M rho (rho 1) (CEvar 8) ->
  ns_proof M rho
    (E_wim (E_marker_empty (CEvar 4) (CEvar 7))
      (E_wim (E_wn (E_weq (CEvar 3) (CEvar 4)))
        (E_wim (E_raw_pair (CEvar 3) (CEvar 4) (CEvar 5) (CEvar 7))
          (E_wim (E_wel (CEvar 3) (CEvar 6))
            (E_wim (E_tagged_request_clause (CEvar 0) (CEvar 10) (CEvar 3) (CEvar 4)
              (CEvar 5) (CEvar 6) (CEvar 8) (CEvar 7))
              (E_wim (E_raw_singleton (CEvar 1) (CEvar 2) (CEvar 7))
                (E_wim (E_wa (E_wel (CEvar 1) (CEvar 3)) (CEvar 9))
                  (E_wel (CEvar 1) (CEvar 6))))))))).
Proof.
  intros HD HN HF HP HSub HAbs.
  assert (D:forall i j,i<8 -> j<8 -> i<>j -> rho i<>rho j).
  { intros i j Hi Hj Hij.
    assert (RI:selected_query_role M rho i=rho i).
    { do 8 (destruct i as [|i];[reflexivity|]);lia. }
    assert (RJ:selected_query_role M rho j=rho j).
    { do 8 (destruct j as [|j];[reflexivity|]);lia. }
    rewrite <-RI,<-RJ. apply HD;lia. }
  assert (N:forall i,i<8 -> rho i<>zeroM M).
  { intros i Hi.
    assert (RI:selected_query_role M rho i=rho i).
    { do 8 (destruct i as [|i];[reflexivity|]);lia. }
    rewrite <-RI. apply HN;lia. }
  set (Req:=E_tagged_request_clause (CEvar 0) (CEvar 10) (CEvar 3) (CEvar 4)
    (CEvar 5) (CEvar 6) (CEvar 8) (CEvar 7)).
  set (Loc:=E_tagged_local_request (CEvar 0) (CEvar 2) (CEvar 3) (CEvar 4)
    (CEvar 5) (CEvar 6) (CEvar 8) (E_raw_singleton (CEvar 0) (CEvar 2) (CEvar 7))).
  set (Sing:=E_raw_singleton (CEvar 1) (CEvar 2) (CEvar 7)).
  set (Emp:=E_marker_empty (CEvar 4) (CEvar 7)).
  set (Neq:=E_wn (E_weq (CEvar 3) (CEvar 4))).
  set (Pair:=E_raw_pair (CEvar 3) (CEvar 4) (CEvar 5) (CEvar 7)).
  set (Bmem:=E_wel (CEvar 3) (CEvar 6)).
  set (NRoot:=E_wn (E_weq (CEvar 2) (CEvar 5))).
  set (NMarker:=E_wn (E_weq (CEvar 2) (CEvar 4))).
  set (Condition:=E_wa (E_wel (CEvar 1) (CEvar 3)) (CEvar 9)).
  set (Result:=E_wel (CEvar 1) (CEvar 6)).
  apply (ns_proof_macro M rho
    (E_wim Req Loc :: E_wim Emp (E_wim Sing NMarker) ::
     E_wim Neq (E_wim Pair (E_wim Sing NRoot)) ::
     E_wim (E_wa NRoot (E_wa NMarker Sing))
       (E_wim Bmem (E_wim Loc (E_wim Condition Result))) :: nil)).
  - intros e [<-|[<-|[<-|[<-|[]]]]].
    + exact (numerical_tagged_request_specialization M (rho 0) (rho 10) (rho 2)
        (rho 3) (rho 4) (rho 5) (rho 6) (rho 7) (rho 8)
        (HN 8 ltac:(lia)) (HD 8 2 ltac:(lia) ltac:(lia) ltac:(lia))
        (HD 0 8 ltac:(lia) ltac:(lia) ltac:(lia)) (D 0 2 ltac:(lia) ltac:(lia) ltac:(lia))
        (HD 6 8 ltac:(lia) ltac:(lia) ltac:(lia)) (D 6 2 ltac:(lia) ltac:(lia) ltac:(lia))
        (HD 7 8 ltac:(lia) ltac:(lia) ltac:(lia)) (D 7 2 ltac:(lia) ltac:(lia) ltac:(lia))
        (HD 3 8 ltac:(lia) ltac:(lia) ltac:(lia)) (HD 4 8 ltac:(lia) ltac:(lia) ltac:(lia))
        (HD 5 8 ltac:(lia) ltac:(lia) ltac:(lia)) HF HP).
    + exact (numerical_singleton_not_marker M rho (CEvar 4) (CEvar 1) (CEvar 2) (CEvar 7)
        (rho 4) (rho 1) (rho 2) (rho 7) eq_refl eq_refl eq_refl eq_refl
        (N 7 ltac:(lia)) (D 7 1 ltac:(lia) ltac:(lia) ltac:(lia))
        (D 4 7 ltac:(lia) ltac:(lia) ltac:(lia)) (D 2 7 ltac:(lia) ltac:(lia) ltac:(lia))).
    + exact (numerical_singleton_not_pair M rho (CEvar 3) (CEvar 4) (CEvar 5)
        (CEvar 1) (CEvar 2) (CEvar 7) (rho 3) (rho 4) (rho 5) (rho 1) (rho 2) (rho 7)
        eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
        (D 7 3 ltac:(lia) ltac:(lia) ltac:(lia)) (D 7 4 ltac:(lia) ltac:(lia) ltac:(lia))
        (D 5 7 ltac:(lia) ltac:(lia) ltac:(lia)) (D 1 7 ltac:(lia) ltac:(lia) ltac:(lia))
        (D 2 7 ltac:(lia) ltac:(lia) ltac:(lia))).
    + exact (numerical_tagged_selected_request M rho D N HSub HAbs).
  - apply universal_selected_program.
Qed.

Print Assumptions numerical_tagged_universal_selected.
