(** Normalize the Collection result binder even when the generated name
    already is the requested name. *)
From PAModel Require Import Model Arithmetic CodeExpressions ProofTemplates
  NumericalProofs NamedLeibnizSteps TemplatePropositional TemplateFormulaFresh
  RawCollectionProfile RawCollectionContainerAlpha.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Theorem numerical_raw_collection_exists_normalize M rho T A K C U V Theta t a k c u v :
  code_relation M rho T t -> code_relation M rho A a ->
  code_relation M rho K k -> code_relation M rho C c ->
  code_relation M rho U u -> code_relation M rho V v ->
  k<>zeroM M -> c<>zeroM M ->
  t<>k -> a<>k -> u<>k -> v<>k -> t<>c -> a<>c -> u<>c -> v<>c ->
  expression_fresh M rho k Theta -> expression_fresh M rho c Theta ->
  ns_proof M rho
    (E_wim (E_wex K (E_raw_collection_profile T A K U V Theta))
      (E_wex C (E_raw_collection_profile T A C U V Theta))).
Proof.
  intros HT HA HK HC HU HV HK0 HC0 HTK HAK HUK HVK HTC HAC HUC HVC HFk HFc.
  destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
    (fun ax H r=>axioms M ax r H) k c) as [E|HNe].
  - subst c. destruct (code_relation_total M Theta rho) as [theta HTheta].
    set (body:=fun Binder=>E_wex Binder
      (E_raw_collection_profile (CEvar 2) (CEvar 3) Binder (CEvar 4) (CEvar 5) (CEvar 6))).
    set (e:=E_wim (body (CEvar 0)) (body (CEvar 1))).
    set (s1:=fun idx : nat => match idx with
      0=>K|1=>C|2=>T|3=>A|4=>U|5=>V|6=>Theta|_=>CEconst 0 end).
    set (s2:=fun idx : nat => match idx with
      0=>K|1=>K|2=>T|3=>A|4=>U|5=>V|6=>Theta|_=>CEconst 0 end).
    set (values:=fun idx : nat => match idx with
      0=>k|1=>k|2=>t|3=>a|4=>u|5=>v|6=>theta|_=>zeroM M end).
    assert (HS1:forall idx,code_relation M rho (s1 idx) (values idx)).
    { intros [|[|[|[|[|[|[|i]]]]]]];assumption||reflexivity. }
    assert (HS2:forall idx,code_relation M rho (s2 idx) (values idx)).
    { intros [|[|[|[|[|[|[|i]]]]]]];assumption||reflexivity. }
    intros result HResult.
    change (code_relation M rho (code_subst s1 e) result) in HResult.
    apply (proj1 (code_subst_graph M rho s1 values HS1 e result)) in HResult.
    apply (proj2 (code_subst_graph M rho s2 values HS2 e result)) in HResult.
    change (code_relation M rho
      (E_wim (E_wex K (E_raw_collection_profile T A K U V Theta))
        (E_wex K (E_raw_collection_profile T A K U V Theta))) result) in HResult.
    exact (ns_proof_template M rho _ (template_I nil _) result HResult).
  - exact (numerical_raw_collection_exists_alpha M rho T A K C U V Theta t a k c u v
      HT HA HK HC HU HV HK0 HC0 HNe HTK HAK HUK HVK HTC HAC HUC HVC HFk HFc).
Qed.

Print Assumptions numerical_raw_collection_exists_normalize.
