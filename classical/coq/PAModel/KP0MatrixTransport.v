(** Preserve the same KP0 container and query names while removing a
    provably redundant matrix conjunct. No new witness is chosen here. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates
  ProofMacros QuantifierMacros TemplatePropositional NamedLeibnizSteps
  NumericalKP0 NumericalKP0Requests NumericalKP0Eligibility KP0SeedSpecialization
  NumericalTaggedComprehension NumericalBootstrap.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Lemma request_matrix_transport G inputs B K F H :
  proof_macro G inputs (E_wim F H) -> proof_macro G inputs (E_wim H F) ->
  proof_macro G inputs (E_wim (E_kp_request B K F) (E_kp_request B K H)).
Proof.
  intros PF PH.
  assert (EX:proof_macro G inputs (E_wim (E_wex B H) (E_wex B F))).
  { apply macro_exists_monotone,PH. }
  assert (CAP:proof_macro G inputs
    (E_wim (E_wex B (E_wa (E_wel B K) F)) (E_wex B (E_wa (E_wel B K) H)))).
  { apply macro_exists_monotone,macro_discharge,macro_deduction,kp0_md_conjunction.
    - apply tagged_md_left with (b:=F),md_hyp;now left.
    - eapply md_mp with (a:=F).
      + apply tagged_md_right with (a:=E_wel B K),md_hyp;now left.
      + apply md_global,PF. }
  unfold E_kp_request. apply macro_discharge. do 2 apply macro_deduction.
  eapply md_mp with (a:=E_wex B (E_wa (E_wel B K) F));[|apply md_global,CAP].
  eapply md_mp with (a:=E_wex B F).
  - eapply md_mp with (a:=E_wex B H);[apply md_hyp;now left|apply md_global,EX].
  - apply md_hyp;now right;left.
Qed.

Theorem numerical_kp0_matrix_transport M rho Seed A B K P F H Fp Hp :
  ns_proof M rho (E_wim F H) ->
  ns_proof M rho (E_wim Fp Hp) -> ns_proof M rho (E_wim Hp Fp) ->
  ns_proof M rho
    (E_wim (E_kp_with_seed Seed A B K P F Fp)
      (E_kp_with_seed Seed A B K P H Hp)).
Proof.
  intros FH FpHp HpFp.
  set (inputs:=E_wim F H :: E_wim Fp Hp :: E_wim Hp Fp :: nil).
  apply (ns_proof_macro M rho inputs).
  - intros e [<-|[<-|[<-|[]]]];assumption.
  - unfold E_kp_with_seed. apply macro_exists_monotone,macro_discharge,macro_deduction.
    apply kp0_md_conjunction.
    + eapply md_mp with (a:=E_wal P (E_wim (E_kp_eligible Seed B K P) (E_kp_request B K Fp))).
      * apply tagged_md_left with (b:=E_kp_support_body A B K F),md_hyp;now left.
      * apply md_global,macro_all_monotone,kp0_implication_map,request_matrix_transport;
          apply PM_input;unfold inputs;cbn;tauto.
    + eapply md_mp with (a:=E_kp_support_body A B K F).
      * apply tagged_md_right with
          (a:=E_wal P (E_wim (E_kp_eligible Seed B K P) (E_kp_request B K Fp))),md_hyp;now left.
      * apply md_global. unfold E_kp_support_body.
        apply macro_all_monotone,kp0_implication_map,macro_exists_monotone,PM_input.
        unfold inputs;now left.
Qed.

Lemma equality_padding_intro M rho X F :
  ns_proof M rho (E_wim F (E_wa (E_weq X X) F)).
Proof.
  apply (ns_proof_macro M rho (E_weq X X :: nil)).
  - intros e [<-|[]]. apply ns_proof_reflexivity.
  - apply macro_discharge,macro_deduction,kp0_md_conjunction.
    + apply md_global,PM_input;now left.
    + apply md_hyp;now left.
Qed.

Theorem numerical_kp0_remove_equality_padding M rho Seed A B K P X F Fp :
  ns_proof M rho
    (E_wim (E_kp_with_seed Seed A B K P (E_wa (E_weq X X) F) (E_wa (E_weq X X) Fp))
      (E_kp_with_seed Seed A B K P F Fp)).
Proof.
  apply numerical_kp0_matrix_transport.
  - apply ns_proof_template,bootstrap_projection_right.
  - apply ns_proof_template,bootstrap_projection_right.
  - apply equality_padding_intro.
Qed.

Print Assumptions request_matrix_transport.
Print Assumptions numerical_kp0_matrix_transport.
Print Assumptions numerical_kp0_remove_equality_padding.
