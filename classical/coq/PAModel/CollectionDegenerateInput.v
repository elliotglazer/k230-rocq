(** The raw Collection interface allows the input name to coincide with
    the empty marker. That branch follows from empty-marker specialization. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates
  NamedLeibnizSteps TemplatePropositional ProofMacros RawMarkerExclusions
  NumericalFreshPair RawCollectionProfile.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Theorem numerical_empty_self_elimination M rho T Z G t z :
  code_relation M rho T t -> code_relation M rho Z z ->
  z<>zeroM M -> z<>t -> t<>z ->
  ns_proof M rho (E_wim (E_marker_empty T Z) (E_wim (E_wel T T) G)).
Proof.
  intros HT HZ H0 HZT HTZ.
  apply (ns_proof_macro M rho
    (E_wim (E_marker_empty T Z) (E_wn (E_wel T T)) :: nil)).
  - intros e [<-|[]].
    exact (marker_empty_specialization M rho T Z T t z t HT HZ HT H0 HZT HTZ).
  - apply macro_discharge. do 2 apply macro_deduction.
    eapply md_mp with (a:=CEconst 1).
    + eapply md_mp with (a:=E_wel T T).
      * apply md_hyp;now left.
      * eapply md_mp with (a:=E_marker_empty T Z).
        -- apply md_hyp;now right;left.
        -- apply md_global,PM_input;now left.
    + apply md_global,PM_template,template_F.
Qed.

Theorem numerical_empty_same_code_elimination M rho T A Z G t z :
  code_relation M rho T t -> code_relation M rho A t -> code_relation M rho Z z ->
  z<>zeroM M -> z<>t -> t<>z ->
  ns_proof M rho (E_wim (E_marker_empty T Z) (E_wim (E_wel T A) G)).
Proof.
  intros HT HA HZ H0 HZT HTZ.
  destruct (code_relation_total M G rho) as [g HG].
  set (e:=E_wim (E_marker_empty (CEvar 0) (CEvar 2))
    (E_wim (E_wel (CEvar 0) (CEvar 1)) (CEvar 3))).
  set (s1:=fun i : nat=>match i with 0=>T|1=>T|2=>Z|3=>G|_=>CEconst 0 end).
  set (s2:=fun i : nat=>match i with 0=>T|1=>A|2=>Z|3=>G|_=>CEconst 0 end).
  set (values:=fun i : nat=>match i with 0=>t|1=>t|2=>z|3=>g|_=>zeroM M end).
  change (ns_proof M rho (code_subst s2 e)).
  apply (pair_ns_proof_reinstance M rho e s1 s2 values).
  - intros [|[|[|[|i]]]];assumption||reflexivity.
  - intros [|[|[|[|i]]]];assumption||reflexivity.
  - exact (numerical_empty_self_elimination M rho T Z G t z HT HZ H0 HZT HTZ).
Qed.

Theorem numerical_raw_collection_degenerate_input M rho T A C U V Theta Z t z :
  code_relation M rho T t -> code_relation M rho A t -> code_relation M rho Z z ->
  z<>zeroM M -> z<>t -> t<>z ->
  ns_proof M rho (E_wim (E_marker_empty T Z)
    (E_raw_collection_statement T A C U V Theta)).
Proof.
  intros HT HA HZ H0 HZT HTZ.
  exact (numerical_empty_same_code_elimination M rho T A Z
    (E_wex C (E_raw_collection_profile T A C U V Theta)) t z HT HA HZ H0 HZT HTZ).
Qed.

Print Assumptions numerical_empty_self_elimination.
Print Assumptions numerical_empty_same_code_elimination.
Print Assumptions numerical_raw_collection_degenerate_input.
