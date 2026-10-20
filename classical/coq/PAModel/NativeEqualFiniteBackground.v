(** Empty and Hosting are consequences of only three fixed ZFC axioms.
    This finite proof can be relativized using the already checked fixed
    L images. No varying-matrix reflection theorem is needed here. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceNumeralLift
  ZFCFiniteAxiomTemplates SourceFiniteContexts NumericalContexts NumericalSourceFull
  FiniteSourceNoSelf NativeEqualBackgroundCalibration NativeKUniformClosedImplication.
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts Syntax.Facts.
From Stdlib Require Import Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition native_equal_fixed_background :list sf_form :=[ax_eset';ax_pair';ax_refl'].

Theorem native_equal_hosting_finite G :In ax_pair' G ->In ax_refl' G ->G ⊢C source_equal_hosting.
Proof.
  intros HPair HRefl. unfold source_equal_hosting,source_equal_host_body.
  ns_all x.
  ns_assert HP ax_pair'. { apply Ctx;exact HPair. }
  ns_inst HP x. ns_inst HP x. ns_exists_elim HP s HS.
  apply(ExI s). ns_simp.
  ns_inst HS x. apply(IE(CE2 HS)). apply DI1. apply finite_set_refl;exact HRefl.
Qed.

Theorem native_equal_background_finite :native_equal_fixed_background ⊢C
  source_equal_empty ∧ source_equal_hosting.
Proof.
  apply CI.
  - change(native_equal_fixed_background ⊢C ax_eset'). apply Ctx. now left.
  - apply native_equal_hosting_finite;unfold native_equal_fixed_background;cbn;tauto.
Qed.

Theorem numerical_native_equal_background M b c n background :
  source_model_context_represents M b c n native_equal_fixed_background ->
  native_equal_background M background ->source_full_prv M b c n background.
Proof.
  intros HC HB.
  rewrite(sf_relation_functional M SFAnd (code_numeral M(sf_encode source_equal_empty))
    (code_numeral M(sf_encode source_equal_hosting))
    background (code_numeral M(sf_encode(source_equal_empty ∧source_equal_hosting))) HB
    (sf_make_numeral M SFAnd (sf_encode source_equal_empty)(sf_encode source_equal_hosting))).
  exact(source_full_forward_model M native_equal_fixed_background _ native_equal_background_finite b c n HC).
Qed.

Print Assumptions native_equal_background_finite.
Print Assumptions numerical_native_equal_background.
