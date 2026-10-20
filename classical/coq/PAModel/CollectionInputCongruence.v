(** A singleton input tag identifies the raw input used by the binary
    Collection matrix. Leibniz transport uses the actual named substitution. *)
From PAModel Require Import Model CodeExpressions CodeDescent NumericalProofs
  ProofTemplates ProofMacros TemplatePropositional QuantifierMacros
  NamedLeibnizSteps NamedBinderFresh TemplateBinderFresh TemplateNamedSubstitution
  StoppingLeibniz NumericalSingleton NumericalTaggedComprehension NumericalKP0.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Theorem numerical_raw_matrix_transport M rho U X Theta ThetaX uv xv :
  code_relation M rho U uv -> code_relation M rho X xv ->
  expression_binder_absent M rho xv Theta ->
  expression_named_substitution M rho rho uv xv Theta ThetaX ->
  ns_proof M rho (E_wim (E_weq U X) (E_wim Theta ThetaX)).
Proof.
  intros HU HX HA HS.
  destruct (code_relation_total M Theta rho) as [f HF].
  destruct (code_relation_total M ThetaX rho) as [g HG].
  destruct (code_relation_total M (E_weq U X) rho) as [h HH].
  apply (proj2 (ns_under_expression M rho (E_weq U X) Theta ThetaX h f g HH HF HG)).
  exact (proj1 (stopping_leibniz_internal M f uv xv h g
    (expression_tagged_graph M rho 3 U X uv xv h HU HX HH)
    (HA f HF) (HS f g HF HG))).
Qed.

Theorem numerical_singleton_input_congruence M rho X U P Z Theta ThetaX xv uv pv zv :
  code_relation M rho X xv -> code_relation M rho U uv ->
  code_relation M rho P pv -> code_relation M rho Z zv ->
  zv<>xv -> pv<>zv -> uv<>zv ->
  expression_binder_absent M rho xv Theta ->
  expression_named_substitution M rho rho uv xv Theta ThetaX ->
  ns_proof M rho
    (E_wim (E_raw_singleton X P Z)
      (E_wim (E_raw_singleton U P Z) (E_wim Theta ThetaX))).
Proof.
  intros HX HU HP HZ HZX HPZ HUZ HA HS.
  apply (ns_proof_macro M rho
    (E_wim (E_wel X P) (E_wim (E_raw_singleton U P Z) (E_weq U X)) ::
     E_wim (E_weq U X) (E_wim Theta ThetaX) :: nil)).
  - intros e [<-|[<-|[]]].
    + exact (numerical_singleton_uniqueness M rho X U P Z xv uv pv zv
        HX HU HP HZ HZX HPZ HUZ).
    + exact (numerical_raw_matrix_transport M rho U X Theta ThetaX uv xv HU HX HA HS).
  - apply macro_discharge. do 3 apply macro_deduction.
    eapply md_mp with (a:=Theta);[apply md_hyp;now left|].
    eapply md_mp with (a:=E_weq U X).
    + eapply md_mp with (a:=E_raw_singleton U P Z);[apply md_hyp;now right;left|].
      eapply md_mp with (a:=E_wel X P).
      * apply tagged_md_left with (b:=E_wal Z (E_wim (E_wel Z P) (E_weq Z X))).
        apply md_hyp;now right;right;left.
      * apply md_global,PM_input;now left.
    + apply md_global,PM_input;now right;left.
Qed.

Print Assumptions numerical_raw_matrix_transport.
Print Assumptions numerical_singleton_input_congruence.
