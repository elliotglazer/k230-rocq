(** Normalize the actual separation output while retaining a fixed
    envelope assumption. No existence or separation premise is assumed. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates
  NamedLeibnizSteps NamedBinderFresh NamedAlpha FreshNames TemplateFormulaFresh
  RawSeparationFromEnvelope RawSelectionAlphaTotal QuotedSameContainer
  RawMarkerExclusions NumericalRawEnvelope NumericalKP0 ProofMacros.
From Stdlib Require Import Lists.List Arith.PeanoNat.
Unset Implicit Arguments.

Definition normalized_separation_environment M w a b t z theta c idx : carrier M :=
  if Nat.eq_dec idx 7 then c else envelope_separation_environment M w a b t z theta (zeroM M) idx.
Definition E_normalized_envelope_result :=
  E_wex (CEvar 7) (E_raw_selection_container (CEvar 3) (CEvar 1) (CEvar 7) (CEvar 0) (CEvar 6)).

Theorem numerical_raw_separation_normalized_envelope M w a b t z theta c :
  (forall i j,i<5 -> j<5 -> i<>j ->
    envelope_separation_environment M w a b t z theta z i <>
    envelope_separation_environment M w a b t z theta z j) ->
  (forall i,i<4 -> envelope_separation_environment M w a b t z theta z i<>zeroM M) ->
  z<>zeroM M -> named_binder_absent M theta t ->
  c<>zeroM M -> t<>c -> a<>c -> w<>c -> formula_fresh M theta c ->
  ns_proof M (normalized_separation_environment M w a b t z theta c)
    (E_wim E_envelope_separation_parameter E_normalized_envelope_result).
Proof.
  intros D N NZ HT NC TC AC WC FC.
  destruct (numerical_raw_separation_from_envelope M w a b t z theta D N NZ HT)
    as (k & f & NK & KW & KA & KB & KT & KZ & FK & HF & PF).
  set (rho:=fun i=>if Nat.eq_dec i 7 then c else envelope_separation_environment M w a b t z theta k i).
  assert (P:ns_proof M rho (E_wim E_envelope_separation_parameter (E_wex (CEvar 4) E_envelope_separation_body))).
  { intros g Hg. change (code_relation M (envelope_separation_environment M w a b t z theta k)
      (E_wim E_envelope_separation_parameter (E_wex (CEvar 4) E_envelope_separation_body)) g) in Hg.
    assert (g=f) by (eapply code_relation_functional;eassumption). now subst g. }
  assert (HA:ns_proof M rho
    (E_wim (E_wex (CEvar 4) E_envelope_separation_body) E_normalized_envelope_result)).
  { apply (numerical_raw_selection_exists_normalize M rho
      (CEvar 3) (CEvar 1) (CEvar 4) (CEvar 7) (CEvar 0) (CEvar 6)
      t a k c w eq_refl eq_refl eq_refl eq_refl eq_refl NK NC
      (not_eq_sym KT) (not_eq_sym KA) (not_eq_sym KW) TC AC WC).
    - intros g Hg. change (g=theta) in Hg. now subst g.
    - intros g Hg. change (g=theta) in Hg. now subst g. }
  pose proof (ns_proof_syl M rho E_envelope_separation_parameter
    (E_wex (CEvar 4) E_envelope_separation_body) E_normalized_envelope_result P HA) as Q.
  change (ns_proof M (normalized_separation_environment M w a b t z theta c)
    (E_wim E_envelope_separation_parameter E_normalized_envelope_result)) in Q. exact Q.
Qed.

Print Assumptions numerical_raw_separation_normalized_envelope.
