(** The fixed extensionality quotation admits the original descending-even
    binder plan and the current sequential plan, in every PA model. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  QuotientAtomTemplates QuotationQTrans FixedAxiomCertificates ZFCFiniteAxiomTemplates
  FiniteNamedPolicies FinitePolicyBounded FiniteTemplateRebase SetCodeDescent
  TargetNumeralLift NumericalEquivalence.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From Stdlib Require Import Lia.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition raw_extensionality := source_qtrans $0 ax_ext'.
Definition old_extensionality_expression :=
  named_policy_formula true (named_bottom_expression (CEconst 0))
    depth_binder_policy (fun i => CEconst (2 * i + 1)) (CEconst 0)
    raw_extensionality.

Lemma raw_extensionality_bounded : bounded 1 raw_extensionality.
Proof. apply set_formula_boundb_sound. vm_compute. reflexivity. Qed.

Lemma raw_extensionality_template_exact :
  template_set_formula (fun _ => CEconst 1) (CEconst 4) raw_extensionality =
  finite_source_quotation_expression ax_ext'.
Proof. unfold raw_extensionality. rewrite template_qtrans_exact. reflexivity. Qed.

Theorem extensionality_old_code_normalization M old q :
  code_relation M (fun _=>zeroM M) old_extensionality_expression old ->
  code_relation M (fun _=>zeroM M) (finite_source_quotation_expression ax_ext') q ->
  numerical_equivalent M old q.
Proof.
  intros HO HQ.
  apply (finite_bounded_depth_to_sequential_codes M raw_extensionality 1
    (fun _=>zeroM M) (fun _=>zeroM M) true
    (fun i=>CEconst (2*i+1)) (fun _=>CEconst 1)
    (CEconst 0) (CEconst 4) (CEconst 0)
    (fun i=>code_numeral M (2*i+1)) (fun _=>code_numeral M 1)
    (code_numeral M 4) old q).
  - exact raw_extensionality_bounded.
  - intros i Hi. assert (i=0) by lia. now subst i.
  - intro i. reflexivity.
  - intro i. reflexivity.
  - intros i m Hm. apply target_numerals_distinct. lia.
  - reflexivity.
  - apply template_hygienic_below.
    + exact (sf_numeral_lt M 0 4 ltac:(lia)).
    + intro i. exact (sf_numeral_lt M 1 4 ltac:(lia)).
  - exact HO.
  - rewrite raw_extensionality_template_exact. exact HQ.
Qed.

Print Assumptions raw_extensionality_bounded.
Print Assumptions raw_extensionality_template_exact.
Print Assumptions extensionality_old_code_normalization.
