(** Literal axiom correspondence for the pinned minimal ZFc/ZFR library.
    Only finite external library contexts are lifted by this module. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  OldNamedSyntaxBridge OldFullNDSourceBridge OldWFCoreCorrespondence
  FiniteSourceAxiomLift NumericalCoreAxioms ZFCFiniteAxiomTemplates ZFCFiniteSourceCodes
  SourceNumeralLift.
From OldZF Require Std_iface.
From OldZFC Require Z_rel Z_prim.
From OldRegCon Require MinZF.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Theorem old_std_core_axiom_forward phi :
  OldZF.Std_iface.ZFc phi -> standard_zfc_core_source_axiom (isolated_formula phi).
Proof.
  intro H. apply old_wf_minimal_core_exact.
  destruct H as [H|E].
  - destruct H as [a HA|body n HC|body n HC].
    + left. unfold OldZF.Std_iface.ZF0base in HA.
      cbn [OldUndecidability.FOL.Sets.minZF.minZFeq'
        OldUndecidability.FOL.Sets.minZF.minZF' List.In] in HA |- *. tauto.
    + right;left. exists n,body. split;[reflexivity|].
      exact (OldZFC.Z_rel.fb_bounded _ 0 HC).
    + right;right. exists n,body. split;[reflexivity|].
      exact (OldZFC.Z_rel.fb_bounded _ 0 HC).
  - subst phi. left.
    cbn [OldUndecidability.FOL.Sets.minZF.minZFeq'
      OldUndecidability.FOL.Sets.minZF.minZF' List.In]. tauto.
Qed.

Theorem old_std_core_axiom_lift M phi :
  OldZF.Std_iface.ZFc phi ->
  numerical_zfc_core_source_axiom M (code_numeral M (sf_encode (isolated_formula phi))).
Proof. intro H. apply finite_core_axiom_lift,old_std_core_axiom_forward,H. Qed.

Lemma old_fixed_foundation_exact :
  isolated_formula OldRegCon.MinZF.ax_reg'=source_foundation.
Proof. reflexivity. Qed.

Theorem old_zfr_axiom_lift M phi :
  OldZFC.Z_prim.ZFR phi ->
  numerical_zfc_core_source_axiom M (code_numeral M (sf_encode (isolated_formula phi))) \/
  zfc_source_graph M ZFCFoundation (code_numeral M (sf_encode (isolated_formula phi))).
Proof.
  intros [HC|E].
  - left. exact (old_std_core_axiom_lift M phi HC).
  - right. subst phi. rewrite old_fixed_foundation_exact.
    exact (source_formula_numeral_graph M source_foundation).
Qed.

Print Assumptions old_std_core_axiom_forward.
Print Assumptions old_std_core_axiom_lift.
Print Assumptions old_fixed_foundation_exact.
Print Assumptions old_zfr_axiom_lift.
