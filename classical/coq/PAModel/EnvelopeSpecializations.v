(** Exact specializations of the numerical raw-envelope profile. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates
  NamedLeibnizSteps NumericalRawEnvelope TemplateNamedSubstitution TemplateBinderFresh
  StoppingInstantiation StoppingSpecialization QuotientAtomTemplates.
Unset Implicit Arguments.

Definition E_envelope_case T A Y := E_or (E_weq Y A) (E_wa (E_wel Y A) (E_wel T Y)).
Definition E_envelope_point T A B Y :=
  E_wa (E_wim (E_wel Y B) (E_envelope_case T A Y))
       (E_wim (E_envelope_case T A Y) (E_wel Y B)).

Lemma envelope_profile_exact T A B X :
  E_raw_envelope T A B X = E_wal X (E_envelope_point T A B X).
Proof. reflexivity. Qed.

Lemma envelope_point_substitution M rho T A B X Y tv av bv xv yv :
  code_relation M rho T tv -> code_relation M rho A av -> code_relation M rho B bv ->
  code_relation M rho X xv -> code_relation M rho Y yv ->
  xv<>zeroM M -> tv<>xv -> av<>xv -> bv<>xv ->
  expression_named_substitution M rho rho xv yv
    (E_envelope_point T A B X) (E_envelope_point T A B Y).
Proof.
  intros HT HA HB HX HY H0 HTX HAX HBX.
  assert (RX:expression_named_replace M rho rho xv yv X Y).
  { intros u v HU HV. rewrite (code_relation_functional M X rho u xv HU HX),
      (code_relation_functional M Y rho v yv HV HY). now left. }
  assert (RT:expression_named_replace M rho rho xv yv T T).
  { intros u v HU HV. rewrite (code_relation_functional M T rho u tv HU HT),
      (code_relation_functional M T rho v tv HV HT). now right. }
  assert (RA:expression_named_replace M rho rho xv yv A A).
  { intros u v HU HV. rewrite (code_relation_functional M A rho u av HU HA),
      (code_relation_functional M A rho v av HV HA). now right. }
  assert (RB:expression_named_replace M rho rho xv yv B B).
  { intros u v HU HV. rewrite (code_relation_functional M B rho u bv HU HB),
      (code_relation_functional M B rho v bv HV HB). now right. }
  unfold E_envelope_point,E_envelope_case.
  repeat first [apply expression_ns_conjunction;[exact H0| |]
    |apply expression_ns_disjunction;[exact H0| |]
    |apply expression_ns_implication].
  all:first [apply (expression_ns_atom M rho rho xv yv false)
            |apply (expression_ns_atom M rho rho xv yv true)];assumption.
Qed.

Lemma envelope_point_binder_absent M rho T A B Y name :
  expression_binder_absent M rho name (E_envelope_point T A B Y).
Proof.
  unfold E_envelope_point,E_envelope_case.
  repeat first [apply expression_binder_absent_conjunction
    |apply expression_binder_absent_disjunction|apply expression_binder_absent_implication].
  all:apply expression_binder_absent_atom;auto.
Qed.

Theorem numerical_envelope_specialize M rho T A B X Y tv av bv xv yv :
  code_relation M rho T tv -> code_relation M rho A av -> code_relation M rho B bv ->
  code_relation M rho X xv -> code_relation M rho Y yv ->
  xv<>zeroM M -> xv<>yv -> tv<>xv -> av<>xv -> bv<>xv ->
  ns_proof M rho (E_wim (E_raw_envelope T A B X) (E_envelope_point T A B Y)).
Proof.
  intros HT HA HB HX HY H0 HXY HTX HAX HBX.
  destruct (code_relation_total M (E_envelope_point T A B X) rho) as [f HF].
  destruct (code_relation_total M (E_envelope_point T A B Y) rho) as [g HG].
  exact (proj1 (ns_stopping_instantiation M rho X Y (E_envelope_point T A B X)
    (E_envelope_point T A B Y) xv yv f g HX HY HF HG HXY
    (envelope_point_binder_absent M rho T A B X yv f HF)
    (envelope_point_substitution M rho T A B X Y tv av bv xv yv HT HA HB HX HY H0 HTX HAX HBX f g HF HG))).
Qed.

Theorem numerical_envelope_self M rho T A B X :
  ns_proof M rho (E_wim (E_raw_envelope T A B X) (E_envelope_point T A B X)).
Proof. apply ns_stopping_self_specialization. Qed.

Theorem numerical_domain_profile_specialize M rho T B X Y tv bv xv yv :
  code_relation M rho T tv -> code_relation M rho B bv ->
  code_relation M rho X xv -> code_relation M rho Y yv ->
  xv<>yv -> tv<>xv -> bv<>xv ->
  ns_proof M rho (E_wim (E_wal X (E_wim (E_wel X B) (E_wel T X)))
    (E_wim (E_wel Y B) (E_wel T Y))).
Proof.
  intros HT HB HX HY HXY HTX HBX.
  assert (RX:expression_named_replace M rho rho xv yv X Y).
  { intros u v HU HV. rewrite (code_relation_functional M X rho u xv HU HX),
      (code_relation_functional M Y rho v yv HV HY). now left. }
  assert (RT:expression_named_replace M rho rho xv yv T T).
  { intros u v HU HV. rewrite (code_relation_functional M T rho u tv HU HT),
      (code_relation_functional M T rho v tv HV HT). now right. }
  assert (RB:expression_named_replace M rho rho xv yv B B).
  { intros u v HU HV. rewrite (code_relation_functional M B rho u bv HU HB),
      (code_relation_functional M B rho v bv HV HB). now right. }
  destruct (code_relation_total M (E_wim (E_wel X B) (E_wel T X)) rho) as [f HF].
  destruct (code_relation_total M (E_wim (E_wel Y B) (E_wel T Y)) rho) as [g HG].
  assert (HS:expression_named_substitution M rho rho xv yv
    (E_wim (E_wel X B) (E_wel T X)) (E_wim (E_wel Y B) (E_wel T Y))).
  { apply expression_ns_implication;apply (expression_ns_atom M rho rho xv yv false);assumption. }
  assert (HAbs:expression_binder_absent M rho yv (E_wim (E_wel X B) (E_wel T X))).
  { apply expression_binder_absent_implication;apply expression_binder_absent_atom;now left. }
  exact (proj1 (ns_stopping_instantiation M rho X Y _ _ xv yv f g HX HY HF HG HXY
    (HAbs f HF) (HS f g HF HG))).
Qed.

Print Assumptions numerical_envelope_specialize.
Print Assumptions numerical_domain_profile_specialize.
