(** Every alternative of the tagged profile gives membership in the same
    container. The selected alternative allocates and discharges its singleton. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates
  NamedLeibnizSteps FreshNames NamedBinderFresh TemplateBinderFresh TemplateNamedSubstitution
  NumericalSingleton NumericalRawPair NumericalTaggedComprehension NumericalTaggedKernel
  TaggedUniversalRequests NumericalTaggedMarkers TaggedUniversalSelected
  TaggedSelectedDischarge TaggedSelectedAllocation RawMarkerExclusions
  NumericalKP0 QuotientAtomTemplates TemplatePropositional ProofMacros.
From Stdlib Require Import Lists.List Lia.
Unset Implicit Arguments.

Definition markers_environment M (rho:nat->carrier M) idx :=
  match idx with 0=>rho 0|1=>rho 10|2=>rho 3|3=>rho 4|4=>rho 5|5=>rho 6|6=>rho 8|_=>rho 7 end.
Definition markers_role_index idx :=
  match idx with 0=>0|1=>8|2=>3|3=>4|4=>5|5=>6|_=>7 end.
Lemma markers_roles_from_fixed M rho :
  selected_fixed_roles_distinct M rho -> selected_fixed_roles_nonzero M rho ->
  tagged_request_roles_distinct M (markers_environment M rho) /\
  tagged_request_roles_nonzero M (markers_environment M rho).
Proof.
  intros HD HN.
  assert (E:forall i,i<7 -> tagged_request_role M (markers_environment M rho) i =
    selected_query_role M rho (markers_role_index i)).
  { intros i Hi. do 7 (destruct i as [|i];[reflexivity|]);lia. }
  assert (B:forall i,i<7 -> markers_role_index i<9 /\ markers_role_index i<>2).
  { intros i Hi. do 7 (destruct i as [|i];[cbn;lia|]);lia. }
  assert (I:forall i j,i<7 -> j<7 -> markers_role_index i=markers_role_index j -> i=j).
  { intros i j Hi Hj. destruct i as [|[|[|[|[|[|[|i]]]]]]];
      destruct j as [|[|[|[|[|[|[|j]]]]]]];cbn in *;lia. }
  split.
  - intros i j Hi Hj Hne. rewrite (E i Hi),(E j Hj).
    apply HD;try apply B;try assumption;try (pose proof (B i Hi);lia);try (pose proof (B j Hj);lia).
    intro He. apply Hne. exact (I i j Hi Hj He).
  - intros i Hi. rewrite (E i Hi). apply HN;pose proof (B i Hi);lia.
Qed.

Definition E_lower_point :=
  E_wim (E_marker_empty (CEvar 4) (CEvar 7))
    (E_wim (E_wn (E_weq (CEvar 3) (CEvar 4)))
      (E_wim (E_raw_pair (CEvar 3) (CEvar 4) (CEvar 5) (CEvar 7))
        (E_wim (E_tagged_request_clause (CEvar 0) (CEvar 10) (CEvar 3) (CEvar 4)
          (CEvar 5) (CEvar 6) (CEvar 8) (CEvar 7))
          (E_wim (E_tagged_profile (CEvar 1) (CEvar 3) (CEvar 4) (CEvar 9))
            (E_wel (CEvar 1) (CEvar 6)))))).

Theorem numerical_tagged_lower_point M rho :
  selected_fixed_roles_distinct M rho -> selected_fixed_roles_nonzero M rho ->
  formula_fresh M (rho 8) (rho 10) ->
  named_binder_absent M (rho 8) (rho 5) -> named_binder_absent M (rho 8) (rho 4) ->
  expression_named_substitution M rho rho (rho 0) (rho 1) (CEvar 8) (CEvar 9) ->
  expression_binder_absent M rho (rho 1) (CEvar 8) ->
  ns_proof M rho E_lower_point.
Proof.
  intros HD HN HF HR HT HSub HAbs.
  destruct (markers_roles_from_fixed M rho HD HN) as [DM NM].
  pose proof (numerical_tagged_markers M (markers_environment M rho) DM NM HF HR HT) as HM.
  set (Emp:=E_marker_empty (CEvar 4) (CEvar 7)).
  set (Neq:=E_wn (E_weq (CEvar 3) (CEvar 4))).
  set (Pair:=E_raw_pair (CEvar 3) (CEvar 4) (CEvar 5) (CEvar 7)).
  set (Req:=E_tagged_request_clause (CEvar 0) (CEvar 10) (CEvar 3) (CEvar 4)
    (CEvar 5) (CEvar 6) (CEvar 8) (CEvar 7)).
  set (BM:=E_wel (CEvar 3) (CEvar 6)). set (TM:=E_wel (CEvar 4) (CEvar 6)).
  set (XM:=E_wel (CEvar 1) (CEvar 6)).
  set (Cond:=E_wa (E_wel (CEvar 1) (CEvar 3)) (CEvar 9)).
  change (ns_proof M rho (E_wim Emp (E_wim Neq (E_wim Pair (E_wim Req (E_wa BM TM)))))) in HM.
  pose proof (numerical_tagged_selected_allocated M rho HD HN HF HSub HAbs) as HS.
  change (ns_proof M rho (E_wim Emp (E_wim Neq (E_wim Pair (E_wim BM (E_wim Req (E_wim Cond XM))))))) in HS.
  set (inputs:=(E_wim Emp (E_wim Neq (E_wim Pair (E_wim Req (E_wa BM TM)))) ::
     E_wim Emp (E_wim Neq (E_wim Pair (E_wim BM (E_wim Req (E_wim Cond XM))))) ::
     E_wim (E_weq (CEvar 3) (CEvar 1)) (E_wim BM XM) ::
     E_wim (E_weq (CEvar 4) (CEvar 1)) (E_wim TM XM) ::
     E_wim (E_weq (CEvar 1) (CEvar 3)) (E_weq (CEvar 3) (CEvar 1)) ::
     E_wim (E_weq (CEvar 1) (CEvar 4)) (E_weq (CEvar 4) (CEvar 1)) :: nil)).
  apply (ns_proof_macro M rho inputs).
  - intros e [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
    + exact HM.
    + exact HS.
    + apply numerical_tagged_membership_transport.
    + apply numerical_tagged_membership_transport.
    + apply ns_proof_symmetry.
    + apply ns_proof_symmetry.
  - unfold E_lower_point. change (proof_macro nil inputs
      (E_wim Emp (E_wim Neq (E_wim Pair (E_wim Req
        (E_wim (E_tagged_profile (CEvar 1) (CEvar 3) (CEvar 4) (CEvar 9)) XM)))))).
    apply macro_discharge. do 5 apply macro_deduction.
    set (delta:=Req::Pair::Neq::Emp::nil).
    assert (HMT:macro_derivation nil inputs delta (E_wa BM TM)).
    { eapply md_mp with (a:=Req);[apply md_hyp;now left|].
      eapply md_mp with (a:=Pair);[apply md_hyp;now right;left|].
      eapply md_mp with (a:=Neq);[apply md_hyp;now right;right;left|].
      eapply md_mp with (a:=Emp);[apply md_hyp;now right;right;right;left|].
      apply md_global,PM_input;now left. }
    apply (tagged_md_cases _ _ _ (E_weq (CEvar 1) (CEvar 3))
      (E_or (E_weq (CEvar 1) (CEvar 4)) Cond) XM).
    + apply md_hyp;now left.
    + apply macro_deduction.
      eapply md_mp with (a:=BM).
      * apply tagged_md_left with (b:=TM). eapply macro_weaken;[exact HMT|intros e He;cbn in *;tauto].
      * eapply md_mp with (a:=E_weq (CEvar 3) (CEvar 1)).
        -- eapply md_mp with (a:=E_weq (CEvar 1) (CEvar 3));[apply md_hyp;now left|].
           apply md_global,PM_input;now right;right;right;right;left.
        -- apply md_global,PM_input;now right;right;left.
    + apply macro_deduction. apply (tagged_md_cases _ _ _ (E_weq (CEvar 1) (CEvar 4)) Cond XM).
      * apply md_hyp;now left.
      * apply macro_deduction.
        eapply md_mp with (a:=TM).
        -- apply tagged_md_right with (a:=BM). eapply macro_weaken;[exact HMT|intros e He;cbn in *;tauto].
        -- eapply md_mp with (a:=E_weq (CEvar 4) (CEvar 1)).
           ++ eapply md_mp with (a:=E_weq (CEvar 1) (CEvar 4));[apply md_hyp;now left|].
              apply md_global,PM_input;now right;right;right;right;right;left.
           ++ apply md_global,PM_input;now right;right;right;left.
      * apply macro_deduction.
        eapply md_mp with (a:=Cond);[apply md_hyp;now left|].
        eapply md_mp with (a:=Req);[apply md_hyp;cbn;tauto|].
        eapply md_mp with (a:=BM);[apply tagged_md_left with (b:=TM);eapply macro_weaken;[exact HMT|intros e He;cbn in *;tauto]|].
        eapply md_mp with (a:=Pair);[apply md_hyp;cbn;tauto|].
        eapply md_mp with (a:=Neq);[apply md_hyp;cbn;tauto|].
        eapply md_mp with (a:=Emp);[apply md_hyp;cbn;tauto|].
        apply md_global,PM_input;now right;left.
Qed.

Print Assumptions numerical_tagged_lower_point.
