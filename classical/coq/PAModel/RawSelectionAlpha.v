(** Normalize the existential container name in raw Separation. The
    arbitrary predicate is kept fixed by proved source-fresh substitution. *)
From PAModel Require Import Model CodeExpressions CodeDescent NumericalProofs
  ProofTemplates NamedLeibnizSteps NamedSubstitution NamedBinderFresh NamedExistential
  FreshNames TemplateFormulaFresh TemplateBinderFresh TemplateNamedSubstitution FreshSubstitutionIdentity
  TemplateExistsAlpha QuotientSeparationWitness LiteralMemberSeparationPoint
  QuotedSameContainer SelectionFreshness RawMarkerQuantifiers.
Unset Implicit Arguments.

Lemma raw_selection_binder_absent M rho T A K W Theta w name :
  code_relation M rho W w -> w<>name -> expression_binder_absent M rho name Theta ->
  expression_binder_absent M rho name (E_raw_selection_container T A K W Theta).
Proof.
  intros HW HN HT. unfold E_raw_selection_container.
  apply expression_binder_absent_conjunction.
  - apply expression_binder_absent_atom;now left.
  - unfold E_raw_member_selection. apply expression_binder_absent_universal.
    + exact (marker_name_avoids M rho W w name HW HN).
    + unfold E_selection_raw,E_selection_iff.
      repeat first [apply expression_binder_absent_conjunction|apply expression_binder_absent_implication].
      all:try (apply expression_binder_absent_atom;now left).
      all:try apply expression_binder_absent_one.
      all:exact HT.
Qed.

Theorem numerical_raw_selection_exists_alpha M rho T A K C W Theta tv av kv cv wv :
  code_relation M rho T tv -> code_relation M rho A av ->
  code_relation M rho K kv -> code_relation M rho C cv -> code_relation M rho W wv ->
  kv<>zeroM M -> cv<>zeroM M -> kv<>cv ->
  tv<>kv -> av<>kv -> wv<>kv -> tv<>cv -> av<>cv -> wv<>cv ->
  expression_fresh M rho kv Theta -> expression_fresh M rho cv Theta ->
  ns_proof M rho
    (E_wim (E_wex K (E_raw_selection_container T A K W Theta))
      (E_wex C (E_raw_selection_container T A C W Theta))).
Proof.
  intros HT HA HK HC HW HK0 HC0 HKC HTK HAK HWK HTC HAC HWC HFk HFc.
  set (F:=E_raw_selection_container T A K W Theta).
  set (G:=E_raw_selection_container T A C W Theta).
  assert (RT:expression_named_replace M rho rho kv cv T T).
  { intros x y HX HY. rewrite (code_relation_functional M T rho x tv HX HT),
      (code_relation_functional M T rho y tv HY HT). now right. }
  assert (RA:expression_named_replace M rho rho kv cv A A).
  { intros x y HX HY. rewrite (code_relation_functional M A rho x av HX HA),
      (code_relation_functional M A rho y av HY HA). now right. }
  assert (RW:expression_named_replace M rho rho kv cv W W).
  { intros x y HX HY. rewrite (code_relation_functional M W rho x wv HX HW),
      (code_relation_functional M W rho y wv HY HW). now right. }
  assert (RK:expression_named_replace M rho rho kv cv K C).
  { intros x y HX HY. rewrite (code_relation_functional M K rho x kv HX HK),
      (code_relation_functional M C rho y cv HY HC). now left. }
  assert (RTheta:expression_named_substitution M rho rho kv cv Theta Theta).
  { intros f g Hf Hg. assert (g=f) by (eapply code_relation_functional;eassumption). subst g.
    apply named_substitution_source_fresh;[exact (HFk f Hf)|].
    apply named_formula_fresh_binder_absent,HFc,Hf. }
  assert (RFG:expression_named_substitution M rho rho kv cv F G).
  { unfold F,G,E_raw_selection_container. apply expression_ns_conjunction;[exact HK0| |].
    - apply (expression_ns_atom M rho rho kv cv false);assumption.
    - unfold E_raw_member_selection.
      apply (expression_ns_universal M rho rho kv cv W W _ _ wv HW HW HWK HWC).
      unfold E_selection_raw,E_selection_iff.
      repeat first [apply expression_ns_conjunction;[exact HK0| |]|apply expression_ns_implication].
      all:try (apply (expression_ns_atom M rho rho kv cv false);assumption).
      all:exact RTheta. }
  assert (HFabs:expression_binder_absent M rho kv F).
  { apply (raw_selection_binder_absent M rho T A K W Theta wv kv HW HWK).
    intros f Hf. apply named_formula_fresh_binder_absent,HFk,Hf. }
  assert (HFfresh:expression_fresh M rho cv F).
  { apply (raw_member_selection_body_fresh M rho cv T A K W Theta HC0).
    - exact (marker_name_avoids M rho T tv cv HT HTC).
    - exact (marker_name_avoids M rho A av cv HA HAC).
    - exact (marker_name_avoids M rho K kv cv HK HKC).
    - exact (marker_name_avoids M rho W wv cv HW HWC).
    - exact HFc. }
  intros result HResult.
  destruct (code_relation_total M F rho) as [f Hf].
  destruct (code_relation_total M G rho) as [g Hg].
  destruct (code_relation_total M (E_wex K F) rho) as [exf HExF].
  destruct (code_relation_total M (E_wex C G) rho) as [exg HExG].
  destruct (code_relation_total M (E_wim (E_wex C G) (E_wex K F)) rho) as [back HBack].
  exact (proj1 (numerical_named_exists_alpha M f kv cv g exf exg result back
    HK0 HC0 HKC (HFabs f Hf) (HFfresh f Hf) (RFG f g Hf Hg)
    (proj1 (named_exists_expression M rho K F kv f exf HK Hf) HExF)
    (proj1 (named_exists_expression M rho C G cv g exg HC Hg) HExG)
    (expression_implication_graph M rho (E_wex K F) (E_wex C G) exf exg result HExF HExG HResult)
    (expression_implication_graph M rho (E_wex C G) (E_wex K F) exg exf back HExG HExF HBack))).
Qed.

Print Assumptions raw_selection_binder_absent.
Print Assumptions numerical_raw_selection_exists_alpha.
