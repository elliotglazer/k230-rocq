(** Actual envelope existence at a chosen fresh container name and a
    pre-existing profile binder, used by the raw domain constructions. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions NumericalProofs
  ProofTemplates NamedLeibnizSteps TemplateFormulaFresh TemplateBinderFresh
  NumericalVacuitySteps NumericalKP0Eligibility NumericalRawEnvelope
  EnvelopeSpecializations RawMarkerExclusions RawMarkerQuantifiers
  NumericalFreshPair NumericalFreshSingleton NumericalKP0 ProofMacros QuantifierMacros.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Lemma envelope_point_fresh M rho T A B U tv av bv uv name :
  code_relation M rho T tv -> code_relation M rho A av ->
  code_relation M rho B bv -> code_relation M rho U uv ->
  name<>zeroM M -> tv<>name -> av<>name -> bv<>name -> uv<>name ->
  expression_fresh M rho name (E_envelope_point T A B U).
Proof.
  intros HT HA HB HU H0 HTN HAN HBN HUN.
  unfold E_envelope_point,E_envelope_case.
  repeat first [apply expression_fresh_conjunction;[exact H0| |]
    |apply expression_fresh_disjunction;[exact H0| |]
    |apply expression_fresh_implication].
  all:apply expression_fresh_atom;try (now left);try (now right);
    first [exact (marker_name_avoids M rho T tv name HT HTN)
          |exact (marker_name_avoids M rho A av name HA HAN)
          |exact (marker_name_avoids M rho B bv name HB HBN)
          |exact (marker_name_avoids M rho U uv name HU HUN)].
Qed.

Theorem numerical_envelope_rebind M rho T A B U W tv av bv uv wv :
  code_relation M rho T tv -> code_relation M rho A av -> code_relation M rho B bv ->
  code_relation M rho U uv -> code_relation M rho W wv ->
  uv<>zeroM M -> wv<>zeroM M -> uv<>wv ->
  tv<>uv -> av<>uv -> bv<>uv -> tv<>wv -> av<>wv -> bv<>wv ->
  ns_proof M rho (E_wim (E_raw_envelope T A B U) (E_raw_envelope T A B W)).
Proof.
  intros HT HA HB HU HW HU0 HW0 HUW HTU HAU HBU HTW HAW HBW.
  apply marker_generalize_one.
  - apply (kp0_expression_fresh_vacuity M rho W (E_raw_envelope T A B U) wv HW).
    apply expression_fresh_universal.
    + exact (marker_name_avoids M rho U uv wv HU HUW).
    + exact (envelope_point_fresh M rho T A B U tv av bv uv wv HT HA HB HU HW0 HTW HAW HBW HUW).
  - exact (numerical_envelope_specialize M rho T A B U W tv av bv uv wv
      HT HA HB HU HW HU0 HUW HTU HAU HBU).
Qed.

Theorem numerical_envelope_exists_rebind M rho T A B U W tv av bv uv wv :
  code_relation M rho T tv -> code_relation M rho A av -> code_relation M rho B bv ->
  code_relation M rho U uv -> code_relation M rho W wv ->
  uv<>zeroM M -> wv<>zeroM M -> uv<>wv ->
  tv<>uv -> av<>uv -> bv<>uv -> tv<>wv -> av<>wv -> bv<>wv ->
  ns_proof M rho
    (E_wim (E_wex B (E_raw_envelope T A B U)) (E_wex B (E_raw_envelope T A B W))).
Proof.
  intros HT HA HB HU HW HU0 HW0 HUW HTU HAU HBU HTW HAW HBW.
  apply (ns_proof_macro M rho (E_wim (E_raw_envelope T A B U) (E_raw_envelope T A B W)::nil)).
  - intros e [<-|[]]. exact (numerical_envelope_rebind M rho T A B U W tv av bv uv wv
      HT HA HB HU HW HU0 HW0 HUW HTU HAU HBU HTW HAW HBW).
  - apply macro_exists_monotone,PM_input;now left.
Qed.

Theorem numerical_fresh_envelope M rho T A B W Fresh tv av bv wv base :
  code_relation M rho T tv -> code_relation M rho A av -> code_relation M rho B bv ->
  code_relation M rho W wv -> code_relation M rho Fresh base ->
  tv<>wv -> av<>wv -> wv<>zeroM M -> bv=succM M (succM M base) ->
  coding_lt M (zeroM M) base -> coding_lt M tv base ->
  coding_lt M av base -> coding_lt M wv base ->
  ns_proof M rho (E_wex B (E_raw_envelope T A B W)).
Proof.
  intros HT HA HB HW HF HTW HAW HW0 EB H0 HTB HAB HWB.
  set (P:=CEadd (CEadd Fresh (CEconst 1)) (CEconst 1)).
  set (U:=CEadd P (CEconst 1)).
  assert (HP:code_relation M rho P bv).
  { rewrite EB. apply template_fresh_increment_graph,template_fresh_increment_graph,HF. }
  assert (HU:code_relation M rho U (succM M bv)).
  { apply template_fresh_increment_graph,HP. }
  assert (Hbase:coding_lt M base bv).
  { rewrite EB. eapply coding_lt_trans;apply coding_lt_succ. }
  assert (HTP:coding_lt M tv bv) by exact (coding_lt_trans M tv base bv HTB Hbase).
  assert (HAP:coding_lt M av bv) by exact (coding_lt_trans M av base bv HAB Hbase).
  assert (HWP:coding_lt M wv bv) by exact (coding_lt_trans M wv base bv HWB Hbase).
  assert (HS:ns_proof M rho (E_wex P (E_raw_envelope T A P W))).
  { eapply ns_proof_mp.
    - exact (numerical_raw_envelope_named M rho T A Fresh tv av base HT HA HF H0 HTB HAB).
    - apply (numerical_envelope_exists_rebind M rho T A P U W tv av bv (succM M bv) wv HT HA HP HU HW).
      + apply not_eq_sym,fresh_singleton_lt_neq,coding_zero_lt_succ.
      + exact HW0.
      + apply not_eq_sym,fresh_singleton_lt_neq. eapply coding_lt_trans;[exact HWP|apply coding_lt_succ].
      + apply fresh_singleton_lt_neq. eapply coding_lt_trans;[exact HTP|apply coding_lt_succ].
      + apply fresh_singleton_lt_neq. eapply coding_lt_trans;[exact HAP|apply coding_lt_succ].
      + apply fresh_singleton_lt_neq,coding_lt_succ.
      + exact HTW.
      + exact HAW.
      + apply not_eq_sym,fresh_singleton_lt_neq,HWP. }
  set (body:=E_wex (CEvar 0) (E_raw_envelope (CEvar 1) (CEvar 2) (CEvar 0) (CEvar 3))).
  set (s1:=fun i=>match i with 0=>P|1=>T|2=>A|3=>W|_=>CEconst 0 end).
  set (s2:=fun i=>match i with 0=>B|1=>T|2=>A|3=>W|_=>CEconst 0 end).
  set (values:=fun i=>match i with 0=>bv|1=>tv|2=>av|3=>wv|_=>zeroM M end).
  change (ns_proof M rho (code_subst s2 body)).
  apply (pair_ns_proof_reinstance M rho body s1 s2 values).
  - intros [|[|[|[|i]]]];assumption||reflexivity.
  - intros [|[|[|[|i]]]];assumption||reflexivity.
  - exact HS.
Qed.

Print Assumptions numerical_envelope_rebind.
Print Assumptions numerical_fresh_envelope.
