(** Equality proof programs for the retained K230 numerical calculus.
    Only the guarded reflexivity construction uses the K bundle. All local
    deductions below are propositional; no generalization is applied to a
    temporary hypothesis. The proof plan follows L1_LMeta.v but constructs
    the numerical proof macros directly. *)
From PAModel Require Import CodeExpressions ProofTemplates TemplateCD
  TemplatePropositional ProofMacros QuantifierMacros.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Section Equality.
Variable G : list (code_expr * code_expr).
Variable Inputs : list code_expr.

Lemma template_eq_vacuity x z : In (z,x) G ->
  template_proof G (E_wim (E_weq x x) (E_wal z (E_weq x x))).
Proof.
  intro H. apply template_discharge.
  eapply template_der_andl. apply dthm. exact (template_B6a G x x z H H).
Qed.

Lemma macro_eq_refl x z : In (z,x) G -> proof_macro G Inputs (E_weq x x).
Proof.
  intro Hguard.
  assert (H3 : proof_macro G Inputs (E_wim (E_weq z x) (E_weq x x))).
  { exact (PM_mp _ _ (PM_template _ (TP_row LR7 x x z (CEconst 0)))
      (PM_template _ (tcd_28 G (E_weq z x) (E_weq x x)))). }
  assert (H5 : proof_macro G Inputs (E_wim (E_weq x x) (E_wal z (E_weq x x)))).
  { apply PM_template. exact (template_eq_vacuity x z Hguard). }
  pose proof (macro_exists_monotone G Inputs z _ _
    (macro_syl G Inputs _ _ _ H3 H5)) as H7.
  exact (PM_mp _ _
    (PM_mp _ _ (PM_template _ (TP_row LR1 z x (CEconst 0) (CEconst 0))) H7)
    (PM_template _ (template_r6 z (E_weq x x)))).
Qed.

Lemma macro_eq_sym x y : proof_macro G Inputs (E_weq x x) ->
  proof_macro G Inputs (E_wim (E_weq x y) (E_weq y x)).
Proof.
  intro Hr. apply (macro_discharge G Inputs). apply (macro_deduction G Inputs).
  eapply (md_mp G Inputs _ (E_weq x x)).
  - apply md_global. exact Hr.
  - eapply (md_mp G Inputs _ (E_weq x y)).
    + apply md_hyp. now left.
    + apply md_global, PM_template. exact (TP_row LR7 y x x (CEconst 0)).
Qed.

Lemma macro_eq_trans x y z : proof_macro G Inputs (E_weq x x) ->
  proof_macro G Inputs (E_wim (E_weq x y) (E_wim (E_weq y z) (E_weq x z))).
Proof.
  intro Hr. pose proof (macro_eq_sym x y Hr) as Hsym.
  apply (macro_discharge G Inputs). do 2 apply (macro_deduction G Inputs).
  eapply (md_mp G Inputs _ (E_weq y z)).
  - apply md_hyp. now left.
  - eapply (md_mp G Inputs _ (E_weq y x)).
    + eapply (md_mp G Inputs _ (E_weq x y)).
      * apply md_hyp. right; now left.
      * apply md_global. exact Hsym.
    + apply md_global, PM_template. exact (TP_row LR7 x z y (CEconst 0)).
Qed.

Lemma macro_eq_transport u u' v v' : proof_macro G Inputs (E_weq u' u') ->
  proof_macro G Inputs
    (E_wim (E_weq u u') (E_wim (E_weq v v') (E_wim (E_weq u v) (E_weq u' v')))).
Proof.
  intro Hr. pose proof (macro_eq_sym u' v Hr) as Hsym.
  apply (macro_discharge G Inputs). do 3 apply (macro_deduction G Inputs).
  assert (Huv : macro_derivation G Inputs [E_weq u v; E_weq v v'; E_weq u u'] (E_weq u' v)).
  { eapply (md_mp G Inputs _ (E_weq u v)).
    - apply md_hyp. now left.
    - eapply (md_mp G Inputs _ (E_weq u u')).
      + apply md_hyp. right; right; now left.
      + apply md_global, PM_template. exact (TP_row LR7 u' v u (CEconst 0)). }
  assert (Hvu : macro_derivation G Inputs [E_weq u v; E_weq v v'; E_weq u u'] (E_weq v u')).
  { exact (md_mp G Inputs _ _ _ Huv (md_global G Inputs _ _ Hsym)). }
  eapply (md_mp G Inputs _ (E_weq v v')).
  - apply md_hyp. right; now left.
  - eapply (md_mp G Inputs _ (E_weq v u')).
    + exact Hvu.
    + apply md_global, PM_template. exact (TP_row LR7 u' v' v (CEconst 0)).
Qed.

Lemma macro_member_transport u u' v v' : proof_macro G Inputs
  (E_wim (E_weq u u') (E_wim (E_weq v v') (E_wim (E_wel u v) (E_wel u' v')))).
Proof.
  apply (macro_discharge G Inputs). do 3 apply (macro_deduction G Inputs).
  eapply (md_mp G Inputs _ (E_wel u' v)).
  - eapply (md_mp G Inputs _ (E_wel u v)).
    + apply md_hyp. now left.
    + eapply (md_mp G Inputs _ (E_weq u u')).
      * apply md_hyp. right; right; now left.
      * apply md_global, PM_template. exact (TP_row LR5 u' v u (CEconst 0)).
  - eapply (md_mp G Inputs _ (E_weq v v')).
    + apply md_hyp. right; now left.
    + apply md_global, PM_template. exact (TP_row LR3 v v' u' (CEconst 0)).
Qed.
End Equality.

Print Assumptions macro_eq_refl.
Print Assumptions macro_eq_sym.
Print Assumptions macro_eq_trans.
Print Assumptions macro_eq_transport.
Print Assumptions macro_member_transport.
