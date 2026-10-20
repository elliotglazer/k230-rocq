(** Actual core-provability of WF closure and every fixed core axiom image
    inside any PA model, using only fixed external derivations. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  NumericalContexts NumericalSourceFull SourceFiniteContexts SourceNumeralLift
  NumericalCoreAxioms CoreConsistencyReduction FiniteSourceAxiomLift
  OldNamedSyntaxBridge OldFullNDSourceBridge SourceWFFormula NumericalWFFoundation
  SourceRelativization SourceRelativizationFunctionality SourceRelativizationCalibration
  ZFCFiniteAxiomTemplates ZFCFiniteSourceCodes
  WFClosureFiniteBridge OldWFCoreCorrespondence WFAllFixedFiniteBridge.
From Undecidability.FOL Require Import Syntax.Core Sets.minZF Deduction.FullND.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Theorem finite_current_core_proof_lift M (A:list sf_form) (phi:sf_form) :
  (forall a,In a A -> standard_zfc_core_source_axiom a) ->
  @Undecidability.FOL.Deduction.FullND.prv
    Undecidability.FOL.Syntax.BinSig.sig_empty
    Undecidability.FOL.Sets.Signatures.ZFSignature.ZF_pred_sig
    Undecidability.FOL.Syntax.Core.falsity_on Undecidability.FOL.Syntax.Core.class A phi ->
  source_core_provable M (code_numeral M (sf_encode phi)).
Proof.
  intros HA HP. destruct (source_model_context_total M A) as [b [c [n HC]]].
  exists b,c,n. split.
  - intros f HF. apply (proj1 (source_model_context_member_iff M b c n A f HC)) in HF.
    destruct HF as [a [HIn ->]]. apply finite_core_axiom_lift,HA,HIn.
  - exact (@source_full_forward_model Undecidability.FOL.Syntax.Core.falsity_on
      Undecidability.FOL.Syntax.Core.class M A phi HP b c n HC).
Qed.

Theorem numerical_wf_closure_core M : source_core_provable M (source_wf_closure_code M).
Proof.
  destruct source_wf_closure_finite as [A [HA HP]].
  apply (finite_current_core_proof_lift M (List.map isolated_formula A) source_wf_closure).
  - intros a HF. apply List.in_map_iff in HF. destruct HF as [olda [<- HF]].
    apply old_wf_minimal_core_exact,HA,HF.
  - exact HP.
Qed.

Theorem numerical_wf_all_fixed_core M tag f rf :
  In tag zfc_core_fixed_tags -> zfc_source_graph M tag f ->
  source_relativization M (source_wf_domain_code M) f rf -> source_core_provable M rf.
Proof.
  intros HT HF HR.
  pose proof (zfc_source_graph_functional M tag f
    (code_numeral M (sf_encode (zfc_fixed_source tag))) HF
    (source_formula_numeral_graph M (zfc_fixed_source tag))) as EF. subst f.
  pose proof (source_relativization_finite_lift M wf_domain (zfc_fixed_source tag)) as HR0.
  pose proof (source_relativization_functional M (code_numeral M (sf_encode (zfc_fixed_source tag)))
    (source_wf_domain_code M) rf
    (code_numeral M (sf_encode (sf_relativize wf_domain (zfc_fixed_source tag)))) HR HR0) as ER.
  subst rf.
  assert (HIn:In (zfc_fixed_source tag) Undecidability.FOL.Sets.minZF.minZFeq').
  { apply standard_zfc_core_fixed_iff. exists tag. split;[exact HT|reflexivity]. }
  destruct (source_wf_all_fixed_finite (zfc_fixed_source tag) HIn) as [A [HA HP]].
  exact (finite_current_core_proof_lift M A _ HA HP).
Qed.

Theorem numerical_wf_foundation_core M f rf :
  zfc_source_graph M ZFCFoundation f ->
  source_relativization M (source_wf_domain_code M) f rf -> source_core_provable M rf.
Proof.
  intros HF HR. exists (zeroM M),(zeroM M),(zeroM M). split.
  - intros a HA. exfalso. exact (context_empty M (zeroM M) (zeroM M) a HA).
  - apply (numerical_wf_foundation_image M (zeroM M) (zeroM M) (zeroM M) f rf).
    + intros a HA. exfalso. exact (context_empty M (zeroM M) (zeroM M) a HA).
    + exact HF.
    + exact HR.
Qed.

Print Assumptions finite_current_core_proof_lift.
Print Assumptions numerical_wf_closure_core.
Print Assumptions numerical_wf_all_fixed_core.
Print Assumptions numerical_wf_foundation_core.
