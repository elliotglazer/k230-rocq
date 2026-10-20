(** The machine's propositional row has an actual source derivation for
    all internal formula parameters, including every raw-zero collision. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates
  NumericalContexts NumericalSourceFull RawSourceImage RawFinitePropositional.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Lemma raw_implication_total M a b : exists h,implication_graph M a b h.
Proof. apply (code_relation_total M (E_wim (CEvar 0) (CEvar 1)) (arguments2 a b (zeroM M))). Qed.

Theorem raw_row8_certificate M a b c u cu h ac bc rhs f :
  implication_graph M c u cu -> implication_graph M cu a h ->
  implication_graph M a c ac -> implication_graph M b c bc ->
  implication_graph M ac bc rhs -> implication_graph M h rhs f ->
  raw_prop_certificate M [] f.
Proof.
  intros GCU GH GAC GBC GR GF.
  destruct (raw_implication_total M cu c) as [cc GCC].
  destruct (raw_implication_total M cc c) as [pc GPC].
  apply (rpc_intro M [] h rhs f GF).
  apply (rpc_intro M [h] ac bc rhs GR).
  apply (rpc_intro M [ac;h] b c bc GBC).
  apply (rpc_elim M [b;ac;h] cc c pc GPC).
  - exact (rpc_peirce M [b;ac;h] c u cu cc pc GCU GCC GPC).
  - apply (rpc_intro M [b;ac;h] cu c cc GCC).
    apply (rpc_elim M [cu;b;ac;h] a c ac GAC).
    + apply rpc_hyp. cbn. auto.
    + apply (rpc_elim M [cu;b;ac;h] cu a h GH);apply rpc_hyp;cbn;auto.
Qed.

Theorem raw_row8_source M env f sf :
  code_relation M env code_row8 f -> raw_source_image M f sf ->
  source_full_prv M (zeroM M) (zeroM M) (zeroM M) sf.
Proof.
  intros HF HS. unfold code_row8,E_rho8 in HF.
  set (A:=CEvar 0). set (B:=CEvar 1). set (C:=CEvar 2). set (U:=CEvar 3).
  destruct (code_relation_total M (E_wim C U) env) as [cu GCU].
  destruct (code_relation_total M (E_wim (E_wim C U) A) env) as [h GH].
  destruct (code_relation_total M (E_wim A C) env) as [ac GAC].
  destruct (code_relation_total M (E_wim B C) env) as [bc GBC].
  destruct (code_relation_total M (E_wim (E_wim A C) (E_wim B C)) env) as [rhs GR].
  apply (raw_prop_certificate_empty_source M f sf);[|exact HS].
  apply (raw_row8_certificate M (env 0) (env 1) (env 2) (env 3) cu h ac bc rhs f).
  - exact (expression_implication_graph M env C U _ _ cu eq_refl eq_refl GCU).
  - exact (expression_implication_graph M env (E_wim C U) A cu _ h GCU eq_refl GH).
  - exact (expression_implication_graph M env A C _ _ ac eq_refl eq_refl GAC).
  - exact (expression_implication_graph M env B C _ _ bc eq_refl eq_refl GBC).
  - exact (expression_implication_graph M env (E_wim A C) (E_wim B C) ac bc rhs GAC GBC GR).
  - exact (expression_implication_graph M env (E_wim (E_wim C U) A)
      (E_wim (E_wim A C) (E_wim B C)) h rhs f GH GR HF).
Qed.

Print Assumptions raw_row8_certificate.
Print Assumptions raw_row8_source.
