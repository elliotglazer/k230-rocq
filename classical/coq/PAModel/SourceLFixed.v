(** The exact pinned constructible-set class and its fixed nonemptiness
    proof, transferred to the current minimal source syntax and every PA
    model. This does not supply the uniform L schema interpretations. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  OldNamedSyntaxBridge OldFullNDSourceBridge SourceBounded SourceNumeralLift
  SourceFiniteContexts NumericalContexts NumericalSourceFull.
From OldZFC Require Z_L.
From OldZF Require Std_iface.
From OldRegCon Require MinZF.
From OldUndecidability.FOL.Sets Require minZF.
From Undecidability.FOL Require Import Syntax.Bounded Syntax.Core Syntax.BinSig Sets.Signatures Deduction.FullND.
From FOL Require Import FullSyntax.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Definition source_L_domain : sf_form := isolated_formula OldZFC.Z_L.Lform.
Definition old_L_background : list (isolated_old_form OC.falsity_on) :=
  OldRegCon.MinZF.ax_reg' :: OldUndecidability.FOL.Sets.minZF.ax_om' ::
    OldZF.Std_iface.ZF0base ++ OldZFC.Z_L.Ax_L.
Definition source_L_background : list sf_form := List.map isolated_formula old_L_background.
Definition source_L_domain_code M := code_numeral M (sf_encode source_L_domain).
Definition source_L_nonempty_formula : sf_form := quant Ex source_L_domain.
Definition source_L_nonempty_code M := code_numeral M (sf_encode source_L_nonempty_formula).

Lemma source_L_domain_bounded : Undecidability.FOL.Syntax.Bounded.bounded 1 source_L_domain.
Proof. exact (@isolated_bounded OC.falsity_on 1 OldZFC.Z_L.Lform OldZFC.Z_L.bounded_Lform). Qed.

Lemma source_L_nonempty_finite :
  @Undecidability.FOL.Deduction.FullND.prv
    Undecidability.FOL.Syntax.BinSig.sig_empty
    Undecidability.FOL.Sets.Signatures.ZFSignature.ZF_pred_sig
    Undecidability.FOL.Syntax.Core.falsity_on Undecidability.FOL.Syntax.Core.class
    source_L_background source_L_nonempty_formula.
Proof.
  apply (@isolated_fullnd_to_current OC.falsity_on OC.class old_L_background
    (@OC.quant OldUndecidability.FOL.Syntax.BinSig.sig_empty
      OldUndecidability.FOL.Sets.Signatures.ZFSignature.ZF_pred_sig
      OC.FullSyntax.full_operators OC.falsity_on OC.FullSyntax.Ex OldZFC.Z_L.Lform)).
  apply OldZFC.Z_L.L_ex_g.
  - intros a HA. unfold old_L_background. right;right. apply in_app_iff. now left.
  - unfold old_L_background. now left.
  - unfold old_L_background. right;now left.
  - intros a HA. unfold old_L_background. right;right. apply in_app_iff. now right.
Qed.

Theorem numerical_L_domain_bounded M :
  source_bounded M (source_L_domain_code M) (code_numeral M 1).
Proof.
  exact (proj2 (source_formula_numeral_bounded M source_L_domain 1) source_L_domain_bounded).
Qed.

Theorem numerical_L_nonempty_from_background M b c n :
  source_model_context_represents M b c n source_L_background ->
  source_full_prv M b c n (source_L_nonempty_code M).
Proof.
  exact (@source_full_forward_model Undecidability.FOL.Syntax.Core.falsity_on
    Undecidability.FOL.Syntax.Core.class M source_L_background
    source_L_nonempty_formula source_L_nonempty_finite b c n).
Qed.

Theorem numerical_L_nonempty_context M :
  exists b c n,source_model_context_represents M b c n source_L_background /\
    source_full_prv M b c n (source_L_nonempty_code M).
Proof.
  destruct (source_model_context_total M source_L_background) as [b [c [n HC]]].
  exists b,c,n. split;[exact HC|exact (numerical_L_nonempty_from_background M b c n HC)].
Qed.

Print Assumptions source_L_domain_bounded.
Print Assumptions source_L_nonempty_finite.
Print Assumptions numerical_L_domain_bounded.
Print Assumptions numerical_L_nonempty_from_background.
Print Assumptions numerical_L_nonempty_context.
