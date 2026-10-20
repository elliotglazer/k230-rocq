(** Change only the result-container binder of raw Collection. All matrix
    and input/output roles are kept fixed, using actual named substitution. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates
  NamedLeibnizSteps NamedBinderFresh NamedExistential FreshNames
  TemplateBinderFresh TemplateFormulaFresh TemplateNamedSubstitution
  FreshSubstitutionIdentity TemplateExistsAlpha RawMarkerQuantifiers RawCollectionProfile.
Unset Implicit Arguments.

Lemma raw_collection_profile_binder_absent M rho T A K U V Theta u v name :
  code_relation M rho U u -> code_relation M rho V v -> u<>name -> v<>name ->
  expression_binder_absent M rho name Theta ->
  expression_binder_absent M rho name (E_raw_collection_profile T A K U V Theta).
Proof.
  intros HU HV HUN HVN HTheta.
  unfold E_raw_collection_profile,E_raw_collection_coverage,E_raw_collection_support.
  repeat first
    [ apply expression_binder_absent_conjunction
    | apply expression_binder_absent_universal;[first [exact (marker_name_avoids M rho U u name HU HUN)|exact (marker_name_avoids M rho V v name HV HVN)]|]
    | apply expression_binder_absent_existential;[first [exact (marker_name_avoids M rho U u name HU HUN)|exact (marker_name_avoids M rho V v name HV HVN)]|]
    | apply expression_binder_absent_implication
    | solve [apply expression_binder_absent_atom;now left]
    | solve [exact HTheta] ].
Qed.

Lemma raw_collection_profile_fresh M rho T A K U V Theta t a k u v name :
  code_relation M rho T t -> code_relation M rho A a -> code_relation M rho K k ->
  code_relation M rho U u -> code_relation M rho V v ->
  name<>zeroM M -> t<>name -> a<>name -> k<>name -> u<>name -> v<>name ->
  expression_fresh M rho name Theta ->
  expression_fresh M rho name (E_raw_collection_profile T A K U V Theta).
Proof.
  intros HT HA HK HU HV H0 HTN HAN HKN HUN HVN HTheta.
  assert (NT:expression_name_avoids M rho name T) by exact (marker_name_avoids M rho T t name HT HTN).
  assert (NA:expression_name_avoids M rho name A) by exact (marker_name_avoids M rho A a name HA HAN).
  assert (NK:expression_name_avoids M rho name K) by exact (marker_name_avoids M rho K k name HK HKN).
  assert (NU:expression_name_avoids M rho name U) by exact (marker_name_avoids M rho U u name HU HUN).
  assert (NV:expression_name_avoids M rho name V) by exact (marker_name_avoids M rho V v name HV HVN).
  unfold E_raw_collection_profile,E_raw_collection_coverage,E_raw_collection_support.
  repeat first
    [ apply expression_fresh_conjunction;[exact H0| |]
    | apply expression_fresh_universal;[assumption|]
    | apply expression_fresh_existential;[exact H0|assumption|]
    | apply expression_fresh_implication
    | solve [apply expression_fresh_atom;[now left|assumption|assumption]]
    | solve [exact HTheta] ].
Qed.

Lemma raw_collection_profile_container_substitution M rho T A K C U V Theta t a k c u v :
  code_relation M rho T t -> code_relation M rho A a ->
  code_relation M rho K k -> code_relation M rho C c ->
  code_relation M rho U u -> code_relation M rho V v ->
  k<>zeroM M -> t<>k -> a<>k -> u<>k -> v<>k -> u<>c -> v<>c ->
  expression_fresh M rho k Theta -> expression_binder_absent M rho c Theta ->
  expression_named_substitution M rho rho k c
    (E_raw_collection_profile T A K U V Theta) (E_raw_collection_profile T A C U V Theta).
Proof.
  intros HT HA HK HC HU HV H0 HTK HAK HUK HVK HUC HVC HF HB.
  assert (RT:expression_named_replace M rho rho k c T T).
  { intros x y HX HY. rewrite (code_relation_functional M T rho x t HX HT),
      (code_relation_functional M T rho y t HY HT). now right. }
  assert (RA:expression_named_replace M rho rho k c A A).
  { intros x y HX HY. rewrite (code_relation_functional M A rho x a HX HA),
      (code_relation_functional M A rho y a HY HA). now right. }
  assert (RU:expression_named_replace M rho rho k c U U).
  { intros x y HX HY. rewrite (code_relation_functional M U rho x u HX HU),
      (code_relation_functional M U rho y u HY HU). now right. }
  assert (RV:expression_named_replace M rho rho k c V V).
  { intros x y HX HY. rewrite (code_relation_functional M V rho x v HX HV),
      (code_relation_functional M V rho y v HY HV). now right. }
  assert (RK:expression_named_replace M rho rho k c K C).
  { intros x y HX HY. rewrite (code_relation_functional M K rho x k HX HK),
      (code_relation_functional M C rho y c HY HC). now left. }
  assert (RTheta:expression_named_substitution M rho rho k c Theta Theta).
  { intros f g Hf Hg. assert (g=f) by (eapply code_relation_functional;eassumption). subst g.
    exact (named_substitution_source_fresh M f k c (HF f Hf) (HB f Hf)). }
  unfold E_raw_collection_profile,E_raw_collection_coverage,E_raw_collection_support.
  repeat first
    [ apply expression_ns_conjunction;[exact H0| |]
    | eapply (expression_ns_universal M rho rho k c U U _ _ u HU HU HUK HUC)
    | eapply (expression_ns_universal M rho rho k c V V _ _ v HV HV HVK HVC)
    | eapply (expression_ns_existential M rho rho k c U U _ _ u H0 HU HU HUK HUC)
    | eapply (expression_ns_existential M rho rho k c V V _ _ v H0 HV HV HVK HVC)
    | apply expression_ns_implication
    | solve [apply (expression_ns_atom M rho rho k c false);assumption]
    | solve [exact RTheta] ].
Qed.

Theorem numerical_raw_collection_exists_alpha M rho T A K C U V Theta t a k c u v :
  code_relation M rho T t -> code_relation M rho A a ->
  code_relation M rho K k -> code_relation M rho C c ->
  code_relation M rho U u -> code_relation M rho V v ->
  k<>zeroM M -> c<>zeroM M -> k<>c ->
  t<>k -> a<>k -> u<>k -> v<>k -> t<>c -> a<>c -> u<>c -> v<>c ->
  expression_fresh M rho k Theta -> expression_fresh M rho c Theta ->
  ns_proof M rho
    (E_wim (E_wex K (E_raw_collection_profile T A K U V Theta))
      (E_wex C (E_raw_collection_profile T A C U V Theta))).
Proof.
  intros HT HA HK HC HU HV H0 HC0 HKC HTK HAK HUK HVK HTC HAC HUC HVC HFK HFC.
  set (F:=E_raw_collection_profile T A K U V Theta).
  set (G:=E_raw_collection_profile T A C U V Theta).
  assert (HBK:expression_binder_absent M rho k Theta).
  { intros f Hf. apply named_formula_fresh_binder_absent,HFK,Hf. }
  assert (HBC:expression_binder_absent M rho c Theta).
  { intros f Hf. apply named_formula_fresh_binder_absent,HFC,Hf. }
  intros result HResult.
  destruct (code_relation_total M F rho) as [f Hf].
  destruct (code_relation_total M G rho) as [g Hg].
  destruct (code_relation_total M (E_wex K F) rho) as [ef HEF].
  destruct (code_relation_total M (E_wex C G) rho) as [eg HEG].
  destruct (code_relation_total M (E_wim (E_wex C G) (E_wex K F)) rho) as [back HBack].
  exact (proj1 (numerical_named_exists_alpha M f k c g ef eg result back H0 HC0 HKC
    (raw_collection_profile_binder_absent M rho T A K U V Theta u v k HU HV HUK HVK HBK f Hf)
    (raw_collection_profile_fresh M rho T A K U V Theta t a k u v c HT HA HK HU HV HC0 HTC HAC HKC HUC HVC HFC f Hf)
    (raw_collection_profile_container_substitution M rho T A K C U V Theta t a k c u v
      HT HA HK HC HU HV H0 HTK HAK HUK HVK HUC HVC HFK HBC f g Hf Hg)
    (proj1 (named_exists_expression M rho K F k f ef HK Hf) HEF)
    (proj1 (named_exists_expression M rho C G c g eg HC Hg) HEG)
    (expression_implication_graph M rho (E_wex K F) (E_wex C G) ef eg result HEF HEG HResult)
    (expression_implication_graph M rho (E_wex C G) (E_wex K F) eg ef back HEG HEF HBack))).
Qed.

Print Assumptions raw_collection_profile_binder_absent.
Print Assumptions raw_collection_profile_fresh.
Print Assumptions raw_collection_profile_container_substitution.
Print Assumptions numerical_raw_collection_exists_alpha.
