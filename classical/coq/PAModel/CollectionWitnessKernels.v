(** The two finite witness steps in Collection -> quotient Replacement.
    Every conclusion below is an internally coded derivation. The inputs
    are pointwise atom/transport laws, not a quotient image assumption. *)
From PAModel Require Import Model CodeExpressions ProofTemplates TemplatePropositional
  NumericalProofs NumericalEnvironments NumericalContexts ContextualProofs
  ContextualPropositional StableContextSupport NamedExistential ContextualWitnessRules.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List.
Import Stdlib.Lists.List.ListNotations.
Unset Implicit Arguments.

Definition support_input D R P := E_wa (E_wa D R) P.
Definition support_output D Q P' := E_wa D (E_wa Q P').
Definition support_hypotheses D R Q P P' E :=
  cons (support_input D R P) (cons E (cons (E_wim D (E_wim R Q))
    (cons (E_wim E (E_wim P P')) nil))).

Lemma collection_support_program D R Q P P' E : template_derivation nil
  (support_hypotheses D R Q P P' E)
  (support_output D Q P').
Proof.
  assert (HD : template_derivation nil
      (support_hypotheses D R Q P P' E) D).
  { apply template_der_andl with (b:=R),template_der_andl with (b:=P).
    apply dhyp;cbn;auto. }
  assert (HR : template_derivation nil
      (support_hypotheses D R Q P P' E) R).
  { apply template_der_andr with (a:=D),template_der_andl with (b:=P).
    apply dhyp;cbn;auto. }
  assert (HP : template_derivation nil
      (support_hypotheses D R Q P P' E) P).
  { apply template_der_andr with (a:=E_wa D R). apply dhyp;cbn;auto. }
  apply template_der_andi;[exact HD|]. apply template_der_andi.
  - eapply dmp;[|exact HR]. eapply dmp;[|exact HD]. apply dhyp;cbn;auto.
  - eapply dmp;[|exact HP]. eapply dmp;apply dhyp;cbn;auto.
Qed.

Theorem numerical_collection_support_witness M cb cc cn rho x source target exsource extarget
    eq intro transport db dc dn :
  code_relation M rho (support_input (CEvar 0) (CEvar 1) (CEvar 3)) source ->
  code_relation M rho (support_output (CEvar 0) (CEvar 2) (CEvar 4)) target ->
  code_relation M rho (CEvar 5) eq ->
  code_relation M rho (E_wim (CEvar 0) (E_wim (CEvar 1) (CEvar 2))) intro ->
  code_relation M rho (E_wim (CEvar 5) (E_wim (CEvar 3) (CEvar 4))) transport ->
  stable_context_support M cb cc cn eq -> stable_context_support M cb cc cn intro ->
  stable_context_support M cb cc cn transport -> context_fresh M cb cc cn x ->
  named_exists_graph M x source exsource -> named_exists_graph M x target extarget ->
  environment_cons M cb cc cn source db dc dn ->
  contextually_provable M cb cc cn exsource -> contextually_provable M cb cc cn extarget.
Proof.
  intros GS GT GE GI GP PE PI PP HF HS HT HC PEx.
  apply (contextual_witness_map M cb cc cn x source target exsource extarget db dc dn HF HS HT HC PEx).
  assert (HIncl : context_included M cb cc cn db dc dn).
  { intros f Hf. apply (proj2 (context_member_cons M cb cc cn source db dc dn f HC));now right. }
  assert (PSource : contextually_provable M db dc dn source).
  { apply contextual_hyp. apply (proj2 (context_member_cons M cb cc cn source db dc dn source HC));now left. }
  apply (contextual_propositional_sound M db dc dn rho
    (support_hypotheses (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5))
    (support_output (CEvar 0) (CEvar 2) (CEvar 4))).
  - intros e [<-|[<-|[<-|[<-|[]]]]] f HG.
    + assert (f=source) by exact (code_relation_functional M _ rho f source HG GS);now subst f.
    + assert (f=eq) by exact (code_relation_functional M _ rho f eq HG GE);subst f;exact (PE db dc dn HIncl).
    + assert (f=intro) by exact (code_relation_functional M _ rho f intro HG GI);subst f;exact (PI db dc dn HIncl).
    + assert (f=transport) by exact (code_relation_functional M _ rho f transport HG GP);subst f;exact (PP db dc dn HIncl).
  - apply collection_support_program.
  - exact GT.
Qed.

Definition coverage_input D R P := E_wa D (E_wa R P).
Definition coverage_output D R E := E_wa (E_wa D R) E.
Definition coverage_hypotheses D R P Y E :=
  cons (coverage_input D R P) (cons Y (cons (E_wim Y (E_wim P E)) nil)).

Lemma collection_coverage_program D R P Y E : template_derivation nil
  (coverage_hypotheses D R P Y E) (coverage_output D R E).
Proof.
  assert (HD : template_derivation nil (coverage_hypotheses D R P Y E) D).
  { apply template_der_andl with (b:=E_wa R P);apply dhyp;cbn;auto. }
  assert (HR : template_derivation nil (coverage_hypotheses D R P Y E) R).
  { apply template_der_andl with (b:=P),template_der_andr with (a:=D);apply dhyp;cbn;auto. }
  assert (HP : template_derivation nil (coverage_hypotheses D R P Y E) P).
  { apply template_der_andr with (a:=R),template_der_andr with (a:=D);apply dhyp;cbn;auto. }
  apply template_der_andi.
  - apply template_der_andi;assumption.
  - eapply dmp;[|exact HP]. eapply dmp;apply dhyp;cbn;auto.
Qed.

Theorem numerical_collection_coverage_witness M cb cc cn rho z source target exsource extarget
    candidate uniqueness db dc dn :
  code_relation M rho (coverage_input (CEvar 0) (CEvar 1) (CEvar 2)) source ->
  code_relation M rho (coverage_output (CEvar 0) (CEvar 1) (CEvar 4)) target ->
  code_relation M rho (CEvar 3) candidate ->
  code_relation M rho (E_wim (CEvar 3) (E_wim (CEvar 2) (CEvar 4))) uniqueness ->
  stable_context_support M cb cc cn candidate -> stable_context_support M cb cc cn uniqueness ->
  context_fresh M cb cc cn z -> named_exists_graph M z source exsource ->
  named_exists_graph M z target extarget -> environment_cons M cb cc cn source db dc dn ->
  contextually_provable M cb cc cn exsource -> contextually_provable M cb cc cn extarget.
Proof.
  intros GS GT GC GU PC PU HF HS HT HC PEx.
  apply (contextual_witness_map M cb cc cn z source target exsource extarget db dc dn HF HS HT HC PEx).
  assert (HIncl : context_included M cb cc cn db dc dn).
  { intros f Hf. apply (proj2 (context_member_cons M cb cc cn source db dc dn f HC));now right. }
  assert (PSource : contextually_provable M db dc dn source).
  { apply contextual_hyp. apply (proj2 (context_member_cons M cb cc cn source db dc dn source HC));now left. }
  apply (contextual_propositional_sound M db dc dn rho
    (coverage_hypotheses (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4))
    (coverage_output (CEvar 0) (CEvar 1) (CEvar 4))).
  - intros e [<-|[<-|[<-|[]]]] f HG.
    + assert (f=source) by exact (code_relation_functional M _ rho f source HG GS);now subst f.
    + assert (f=candidate) by exact (code_relation_functional M _ rho f candidate HG GC);subst f;exact (PC db dc dn HIncl).
    + assert (f=uniqueness) by exact (code_relation_functional M _ rho f uniqueness HG GU);subst f;exact (PU db dc dn HIncl).
  - apply collection_coverage_program.
  - exact GT.
Qed.

Print Assumptions numerical_collection_support_witness.
Print Assumptions numerical_collection_coverage_witness.
