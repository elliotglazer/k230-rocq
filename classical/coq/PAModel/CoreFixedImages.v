(** Actual marker-1/base-4 images of all ten fixed NumericalCoreAxioms. *)
From CoreFixed Require Import OldCoreFixed.
From PAModel Require Import ThmConstructorBridge OldNamedSyntaxBridge OldQuotationSyntaxBridge
  ExtensionalityImage ExtensionalityNormalization Model CodeExpressions
  NumericalProofs NumericalEquivalence NamedLeibnizSteps BootstrapSpecializations
  FixedAxiomCertificates ZFCFiniteAxiomTemplates ZFCFiniteSourceCodes NumericalCoreAxioms
  NumericalQuotation QuotationQTrans QuotientAtomTemplates FiniteNamedPolicies
  FinitePolicyBounded FiniteTemplateRebase SetCodeDescent TargetNumeralLift.
From K230L Require Import Thm230.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From Stdlib Require Import Lia Lists.List.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition current_core_tag tag :=
  match tag with
  | CoreRefl => ZFCRefl | CoreSym => ZFCSym | CoreTrans => ZFCTrans
  | CoreEqElem => ZFCEqElem | CoreExt => ZFCExt | CoreEmpty => ZFCEmpty
  | CorePair => ZFCPair | CoreUnion => ZFCUnion | CorePower => ZFCPower
  | CoreOmega => ZFCOmega
  end.
Definition current_core_source tag := zfc_fixed_source (current_core_tag tag).
Definition raw_core_formula tag := source_qtrans $0 (current_core_source tag).
Definition old_core_expression tag :=
  named_policy_formula true (named_bottom_expression (CEconst 0))
    depth_binder_policy (fun i=>CEconst (2*i+1)) (CEconst 0) (raw_core_formula tag).

Lemma core_source_syntax_exact tag :
  isolated_formula (core_fixed_source tag) = current_core_source tag.
Proof. destruct tag;reflexivity. Qed.

Lemma core_quotient_expression_value tag :
  code_value (fun _=>0) (old_core_expression tag) = core_quotient_code tag.
Proof.
  symmetry.
  pose proof (isolated_tr_code_value
    (OldK230S.KQuotFormula.qtrans
      (@OldUndecidability.FOL.Syntax.Core.var
        OldUndecidability.FOL.Syntax.BinSig.sig_empty 0)
      (core_fixed_source tag)) OldZF.Std_glue.eta0 (CEconst 0) (fun _=>0)) as H.
  rewrite isolated_quotient_translation_exact,core_source_syntax_exact in H.
  exact H.
Qed.

Lemma core_marker_expression_value tag :
  code_value (fun _=>0) (E_wim specialized_marker_expression (old_core_expression tag)) =
  core_marker_code tag.
Proof.
  rewrite core_marker_code_shape,code_value_wim,core_quotient_expression_value.
  reflexivity.
Qed.

Lemma raw_core_formula_bounded tag : bounded 1 (raw_core_formula tag).
Proof. apply set_formula_boundb_sound. destruct tag;vm_compute;reflexivity. Qed.

Lemma raw_core_template_exact tag :
  template_set_formula (fun _=>CEconst 1) (CEconst 4) (raw_core_formula tag) =
  finite_source_quotation_expression (current_core_source tag).
Proof.
  unfold raw_core_formula. rewrite template_qtrans_exact. destruct tag;reflexivity.
Qed.

Theorem core_old_code_normalization tag M old q :
  code_relation M (fun _=>zeroM M) (old_core_expression tag) old ->
  code_relation M (fun _=>zeroM M)
    (finite_source_quotation_expression (current_core_source tag)) q ->
  numerical_equivalent M old q.
Proof.
  intros HO HQ.
  apply (finite_bounded_depth_to_sequential_codes M (raw_core_formula tag) 1
    (fun _=>zeroM M) (fun _=>zeroM M) true
    (fun i=>CEconst (2*i+1)) (fun _=>CEconst 1)
    (CEconst 0) (CEconst 4) (CEconst 0)
    (fun i=>code_numeral M (2*i+1)) (fun _=>code_numeral M 1)
    (code_numeral M 4) old q).
  - exact (raw_core_formula_bounded tag).
  - intros i Hi. assert (i=0) by lia. now subst i.
  - intro i. reflexivity.
  - intro i. reflexivity.
  - intros i m Hm. apply target_numerals_distinct. lia.
  - reflexivity.
  - apply template_hygienic_below.
    + exact (sf_numeral_lt M 0 4 ltac:(lia)).
    + intro i. exact (sf_numeral_lt M 1 4 ltac:(lia)).
  - exact HO.
  - rewrite raw_core_template_exact. exact HQ.
Qed.

Theorem actual_core_marker_expression tag M :
  ns_proof M (fun _=>zeroM M)
    (E_wim specialized_marker_expression (old_core_expression tag)).
Proof.
  destruct tag.
  5: exact (actual_extensionality_marker_expression M).
  all: apply current_certificate_expression;rewrite core_marker_expression_value;
    apply original_thm230_to_current,original_core_marker_certificate.
Qed.

Lemma core_marker_image_from_expression tag M marker f q :
  ns_proof M (fun _=>zeroM M)
    (E_wim specialized_marker_expression (old_core_expression tag)) ->
  code_relation M (fun _=>zeroM M) specialized_marker_expression marker ->
  zfc_source_graph M (current_core_tag tag) f ->
  numerical_quotation M f (zeroM M) (zeroM M) (zeroM M)
    (code_numeral M 4) (code_numeral M 1) q ->
  numerical_implies M marker q.
Proof.
  intros HP HM HF HQ.
  destruct (code_relation_total M (old_core_expression tag) (fun _=>zeroM M)) as [old HO].
  apply (numerical_implies_trans M marker old q).
  - apply (proj1 (numerical_implies_expression M (fun _=>zeroM M)
      specialized_marker_expression (old_core_expression tag) marker old HM HO)).
    exact HP.
  - exact (proj1 (core_old_code_normalization tag M old q HO
      (finite_source_quotation_graph M (current_core_source tag) f q HF HQ))).
Qed.

Theorem actual_core_fixed_marker_image tag M marker f q :
  code_relation M (fun _=>zeroM M) specialized_marker_expression marker ->
  zfc_source_graph M (current_core_tag tag) f ->
  numerical_quotation M f (zeroM M) (zeroM M) (zeroM M)
    (code_numeral M 4) (code_numeral M 1) q ->
  numerical_implies M marker q.
Proof.
  destruct tag.
  5: apply actual_extensionality_marker_image.
  all: apply core_marker_image_from_expression,actual_core_marker_expression.
Qed.

Lemma current_core_tags_complete tag :
  In tag zfc_core_fixed_tags -> exists core,current_core_tag core=tag.
Proof.
  destruct tag;intro H.
  - exists CoreRefl;reflexivity.
  - exists CoreSym;reflexivity.
  - exists CoreTrans;reflexivity.
  - exists CoreEqElem;reflexivity.
  - exists CoreExt;reflexivity.
  - exists CoreEmpty;reflexivity.
  - exists CorePair;reflexivity.
  - exists CoreUnion;reflexivity.
  - exists CorePower;reflexivity.
  - exists CoreOmega;reflexivity.
  - cbn [zfc_core_fixed_tags List.In] in H. intuition discriminate.
  - cbn [zfc_core_fixed_tags List.In] in H. intuition discriminate.
Qed.

Theorem actual_all_fixed_core_marker_images M tag marker f q :
  In tag zfc_core_fixed_tags ->
  code_relation M (fun _=>zeroM M) specialized_marker_expression marker ->
  zfc_source_graph M tag f ->
  numerical_quotation M f (zeroM M) (zeroM M) (zeroM M)
    (code_numeral M 4) (code_numeral M 1) q ->
  numerical_implies M marker q.
Proof.
  intro HT. destruct (current_core_tags_complete tag HT) as [core <-].
  apply actual_core_fixed_marker_image.
Qed.

Print Assumptions core_source_syntax_exact.
Print Assumptions core_marker_expression_value.
Print Assumptions core_old_code_normalization.
Print Assumptions actual_core_marker_expression.
Print Assumptions actual_core_fixed_marker_image.
Print Assumptions actual_all_fixed_core_marker_images.
