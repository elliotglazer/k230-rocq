(** Exact current templates for the four actual closed raw KLogic certificates. *)
From RawLogic Require Import RawLogicCertificates.
From PAModel Require Import Model FiniteCoding CodeExpressions SourceNumeralLift
  NamedLeibnizSteps NumericalEquivalence OldNamedSyntaxBridge ThmConstructorBridge
  ExtensionalityImage ProofTemplates QuotientAtomTemplates FiniteNamedPolicies
  FinitePolicyBounded FiniteTemplateRebase ZFCFiniteAxiomTemplates TargetNumeralLift.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lia.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition current_raw_body law := isolated_formula (raw_law_body law).
Definition current_raw_source law := isolated_formula (raw_law_source law).
Definition raw_named_expression law :=
  named_policy_formula true (named_bottom_expression (CEconst 0))
    depth_binder_policy (fun index =>CEconst (2 * index + 1)) (CEconst 0) (current_raw_source law).

Lemma current_raw_source_closed law : bounded 0 (current_raw_source law).
Proof. apply set_formula_boundb_sound. destruct law;vm_compute;reflexivity. Qed.

Lemma raw_named_expression_value law :
  code_value (fun _ =>0) (raw_named_expression law) = raw_law_code law.
Proof.
  symmetry. exact (isolated_tr_code_value (raw_law_source law)
    OldZF.Std_glue.eta0 (CEconst 0) (fun _ =>0)).
Qed.

Theorem raw_named_expression_proved law M :
  ns_proof M (fun _ =>zeroM M) (raw_named_expression law).
Proof.
  apply current_certificate_expression. rewrite raw_named_expression_value.
  apply original_thm230_to_current,original_raw_law_certificate.
Qed.

Theorem raw_closed_template_proved law M rho fresh k :
  code_relation M rho fresh k -> coding_lt M (zeroM M) k ->
  ns_proof M rho (template_set_formula (fun _ =>CEconst 0) fresh (current_raw_source law)).
Proof.
  intros HK Hpos g HG.
  destruct (code_relation_total M (raw_named_expression law) (fun _ =>zeroM M)) as [f HF].
  apply (numerical_implies_apply M f g).
  - apply (proj1 (finite_bounded_depth_to_sequential_codes M (current_raw_source law) 0
      (fun _ =>zeroM M) rho true (fun index =>CEconst (2 * index + 1)) (fun _ =>CEconst 0)
      (CEconst 0) fresh (CEconst 0)
      (fun index =>code_numeral M (2 * index + 1)) (fun _ =>zeroM M) k f g
      (current_raw_source_closed law)
      ltac:(intros;lia) ltac:(intro;reflexivity) ltac:(intro;reflexivity)
      ltac:(intros i n Hn;change (code_numeral M (2*n)<>code_numeral M 0);
        apply target_numerals_distinct;lia)
      HK (template_hygienic_below M (current_raw_source law) (fun _ =>zeroM M) k
        Hpos (fun _ =>Hpos)) HF HG)).
  - exact (raw_named_expression_proved law M f HF).
Qed.

Print Assumptions current_raw_source_closed.
Print Assumptions raw_named_expression_value.
Print Assumptions raw_named_expression_proved.
Print Assumptions raw_closed_template_proved.
