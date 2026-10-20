(** The raw supported-Collection premise used by the quotient proof.
    All memberships here are literal raw memberships, not quotient dmem.
    Coverage only requests witnesses when the raw input has an output. *)
From PAModel Require Import Model CodeExpressions CodeDescent NumericalProofs NumericalEquivalence ProofTemplates
  TemplatePropositional ContextualProofs ContextualPropositional ContextualWitnessRules
  NamedExistential NamedBinderFresh FreshNames.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Definition E_raw_collection_coverage T A C U V theta :=
  E_wim (E_wa (E_wel T U) (E_wel U A))
    (E_wim (E_wex V (E_wa (E_wel T V) theta))
      (E_wex V (E_wa (E_wel T V) (E_wa (E_wel V C) theta)))).
Definition E_raw_collection_support T A C U V theta :=
  E_wim (E_wa (E_wel T V) (E_wel V C))
    (E_wex U (E_wa (E_wa (E_wel T U) (E_wel U A)) theta)).
Definition E_raw_collection_profile T A C U V theta :=
  E_wa (E_wel T C)
    (E_wa (E_wal U (E_raw_collection_coverage T A C U V theta))
      (E_wal V (E_raw_collection_support T A C U V theta))).
Definition E_raw_collection_statement T A C U V theta :=
  E_wim (E_wel T A) (E_wex C (E_raw_collection_profile T A C U V theta)).

(** This premise may apply to arbitrary raw predicates with the displayed
    hygiene conditions. Quotient transport will instantiate it only with
    actual source quotations and use their separately proved invariance. *)
Definition raw_collection_template_certificates M t marker :=
  forall a c u v theta,
    c<>zeroM M -> u<>zeroM M -> v<>zeroM M ->
    t<>c -> t<>u -> t<>v -> a<>c -> a<>u -> a<>v -> c<>u -> c<>v -> u<>v ->
    formula_fresh M theta c -> named_binder_absent M theta u -> named_binder_absent M theta v ->
    forall result, code_relation M (t .: a .: c .: u .: v .: theta .: fun _=>zeroM M)
      (E_raw_collection_statement (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)) result ->
      numerical_implies M marker result.

Theorem contextual_raw_collection_coverage M b c n rho T A C U V theta profile allcoverage :
  code_relation M rho (E_raw_collection_profile T A C U V theta) profile ->
  code_relation M rho (E_wal U (E_raw_collection_coverage T A C U V theta)) allcoverage ->
  contextually_provable M b c n profile -> contextually_provable M b c n allcoverage.
Proof.
  intros HP HC PP.
  apply (contextual_propositional_sound M b c n rho
    (cons (E_raw_collection_profile T A C U V theta) nil)
    (E_wal U (E_raw_collection_coverage T A C U V theta))).
  - exact (contextual_inputs_one M b c n rho _ _ HP PP).
  - apply template_der_andl with (b:=E_wal V (E_raw_collection_support T A C U V theta)).
    apply template_der_andr with (a:=E_wel T C).
    apply dhyp;cbn;auto.
  - exact HC.
Qed.

Theorem contextual_raw_collection_support M b c n rho T A C U V theta profile allsupport :
  code_relation M rho (E_raw_collection_profile T A C U V theta) profile ->
  code_relation M rho (E_wal V (E_raw_collection_support T A C U V theta)) allsupport ->
  contextually_provable M b c n profile -> contextually_provable M b c n allsupport.
Proof.
  intros HP HC PP.
  apply (contextual_propositional_sound M b c n rho
    (cons (E_raw_collection_profile T A C U V theta) nil)
    (E_wal V (E_raw_collection_support T A C U V theta))).
  - exact (contextual_inputs_one M b c n rho _ _ HP PP).
  - apply template_der_andr with (a:=E_wal U (E_raw_collection_coverage T A C U V theta)).
    apply template_der_andr with (a:=E_wel T C).
    apply dhyp;cbn;auto.
  - exact HC.
Qed.

Print Assumptions contextual_raw_collection_coverage.
Print Assumptions contextual_raw_collection_support.
