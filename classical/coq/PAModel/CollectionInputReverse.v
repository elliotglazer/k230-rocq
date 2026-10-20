(** Reverse transport uses the original substitution graph; it does not
    assume that a second substitution reverses capture-rejecting syntax. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates
  ProofMacros TemplatePropositional QuantifierMacros NamedLeibnizSteps
  NamedBinderFresh TemplateBinderFresh TemplateNamedSubstitution StoppingLeibniz
  NumericalSingleton NumericalTaggedComprehension NumericalKP0 CollectionInputCongruence.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Theorem numerical_raw_matrix_transport_reverse M rho X U ThetaX ThetaU xv uv :
  code_relation M rho X xv -> code_relation M rho U uv ->
  expression_binder_absent M rho uv ThetaX ->
  expression_named_substitution M rho rho xv uv ThetaX ThetaU ->
  ns_proof M rho (E_wim (E_weq X U) (E_wim ThetaU ThetaX)).
Proof.
  intros HX HU HA HS.
  destruct (code_relation_total M ThetaX rho) as [f HF].
  destruct (code_relation_total M ThetaU rho) as [g HG].
  destruct (code_relation_total M (E_weq X U) rho) as [h HH].
  apply (proj2 (ns_under_expression M rho (E_weq X U) ThetaU ThetaX h g f HH HG HF)).
  exact (proj2 (stopping_leibniz_internal M f xv uv h g
    (expression_tagged_graph M rho 3 X U xv uv h HX HU HH)
    (HA f HF) (HS f g HF HG))).
Qed.

Theorem numerical_singleton_input_congruence_reverse M rho X U P Z ThetaX ThetaU xv uv pv zv :
  code_relation M rho X xv -> code_relation M rho U uv ->
  code_relation M rho P pv -> code_relation M rho Z zv ->
  zv<>uv -> pv<>zv -> xv<>zv ->
  expression_binder_absent M rho uv ThetaX ->
  expression_named_substitution M rho rho xv uv ThetaX ThetaU ->
  ns_proof M rho
    (E_wim (E_raw_singleton X P Z)
      (E_wim (E_raw_singleton U P Z) (E_wim ThetaU ThetaX))).
Proof.
  intros HX HU HP HZ HZU HPZ HXZ HA HS.
  apply (ns_proof_macro M rho
    (E_wim (E_wel U P) (E_wim (E_raw_singleton X P Z) (E_weq X U)) ::
     E_wim (E_weq X U) (E_wim ThetaU ThetaX) :: nil)).
  - intros e [<-|[<-|[]]].
    + exact (numerical_singleton_uniqueness M rho U X P Z uv xv pv zv
        HU HX HP HZ HZU HPZ HXZ).
    + exact (numerical_raw_matrix_transport_reverse M rho X U ThetaX ThetaU xv uv HX HU HA HS).
  - apply macro_discharge. do 3 apply macro_deduction.
    eapply md_mp with (a:=ThetaU);[apply md_hyp;now left|].
    eapply md_mp with (a:=E_weq X U).
    + eapply md_mp with (a:=E_raw_singleton X P Z);[apply md_hyp;now right;right;left|].
      eapply md_mp with (a:=E_wel U P).
      * apply tagged_md_left with (b:=E_wal Z (E_wim (E_wel Z P) (E_weq Z U))).
        apply md_hyp;now right;left.
      * apply md_global,PM_input;now left.
    + apply md_global,PM_input;now right;left.
Qed.

Print Assumptions numerical_raw_matrix_transport_reverse.
Print Assumptions numerical_singleton_input_congruence_reverse.
