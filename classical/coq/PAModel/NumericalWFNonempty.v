(** Actual numerical WF nonemptiness from the finite source core background.
    The target context may be an arbitrary internal closed context. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalContexts
  NumericalSourceFull SourceNumeralLift SourceBounded SetFormulaCodes
  NumericalCoreAxioms CoreConsistencyReduction SourceHypothesisTransport
  ZFCFiniteAxiomTemplates ZFCFiniteSourceCodes
  SourceWFFormula SourceWFEmptyWitness NumericalWFFoundation.
From Undecidability.FOL.Sets Require Import minZF.
From FOL Require Import FullSyntax.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Lemma source_formula_ex_numeral M (phi:sf_form) :
  sf_relation M SFEx (code_numeral M (sf_encode phi)) (zeroM M)
    (code_numeral M (sf_encode (∃ phi))).
Proof. exact (sf_make_numeral M SFEx (sf_encode phi) 0). Qed.

Definition source_wf_nonempty_code M := code_numeral M (sf_encode (∃ wf_domain)).

Theorem numerical_wf_nonempty_model_context M b c n :
  source_model_context_represents M b c n minZFeq' ->
  source_full_prv M b c n (source_wf_nonempty_code M).
Proof.
  exact (source_full_forward_model M minZFeq' (∃ wf_domain) wf_domain_nonempty_prv b c n).
Qed.

Theorem numerical_wf_fixed_context_is_core M b c n :
  source_model_context_represents M b c n minZFeq' -> source_core_context M b c n.
Proof.
  intros HC f HF.
  apply (proj1 (source_model_context_member_iff M b c n minZFeq' f HC)) in HF.
  destruct HF as [phi [HIn ->]].
  destruct (proj2 (standard_zfc_core_fixed_iff phi) HIn) as [tag [HT E]]. subst phi.
  left. exists tag. split;[exact HT|]. exact (source_formula_numeral_graph M (zfc_fixed_source tag)).
Qed.

Theorem numerical_wf_nonempty_core_background M :
  exists b c n,source_core_context M b c n /\
    context_bounded M b c n (zeroM M) /\
    sf_relation M SFEx (source_wf_domain_code M) (zeroM M) (source_wf_nonempty_code M) /\
    source_full_prv M b c n (source_wf_nonempty_code M).
Proof.
  destruct (source_model_context_total M minZFeq') as [b [c [n HC]]].
  pose proof (numerical_wf_fixed_context_is_core M b c n HC) as HCore.
  exists b,c,n. split;[exact HCore|]. split.
  - intros f HF. exact (numerical_zfc_core_source_axiom_closed M f (HCore f HF)).
  - split.
    + exact (source_formula_ex_numeral M wf_domain).
    + exact (numerical_wf_nonempty_model_context M b c n HC).
Qed.

Theorem numerical_wf_nonempty_from_fixed_proofs M gb gc gn :
  context_bounded M gb gc gn (zeroM M) ->
  (forall tag,In tag zfc_core_fixed_tags ->
    source_full_prv M gb gc gn (code_numeral M (sf_encode (zfc_fixed_source tag)))) ->
  source_full_prv M gb gc gn (source_wf_nonempty_code M).
Proof.
  intros HClosed HFixed.
  destruct (source_model_context_total M minZFeq') as [b [c [n HC]]].
  apply (source_full_prv_replace_hypotheses M gb gc gn (ex_intro _ (zeroM M) HClosed)
    n b c (source_wf_nonempty_code M) (numerical_wf_nonempty_model_context M b c n HC)).
  intros f HF.
  apply (proj1 (source_model_context_member_iff M b c n minZFeq' f HC)) in HF.
  destruct HF as [phi [HIn ->]].
  destruct (proj2 (standard_zfc_core_fixed_iff phi) HIn) as [tag [HT E]].
  subst phi. exact (HFixed tag HT).
Qed.

Print Assumptions numerical_wf_nonempty_model_context.
Print Assumptions numerical_wf_nonempty_core_background.
Print Assumptions numerical_wf_nonempty_from_fixed_proofs.
