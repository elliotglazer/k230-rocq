(** A canonical numerical quotation for closed source formulas.  This is a
    syntax translation, not an axiom-provability or proof-transfer theorem. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  SourceBounded NumericalQuotation QuotationFunctionality QuotationRules
  QuotationHygiene QuotationBoundedEnvironment NumericalZFCAxioms FixedSourceBounds.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition closed_source_quotation M f v :=
  numerical_quotation M f (zeroM M) (zeroM M) (zeroM M)
    (succM M (zeroM M)) (zeroM M) v.

Definition closed_source_quotation_formula (f v : term) : form :=
  numerical_quotation_formula f zero zero zero (σ zero) zero v.

Local Opaque holds numerical_quotation_formula.
Lemma closed_source_quotation_formula_correct M rho f v :
  holds M rho (closed_source_quotation_formula f v) <->
  closed_source_quotation M (evalM M rho f) (evalM M rho v).
Proof.
  unfold closed_source_quotation_formula,closed_source_quotation.
  rewrite numerical_quotation_formula_correct. reflexivity.
Qed.

Theorem closed_source_quotation_total M f : exists v, closed_source_quotation M f v.
Proof. apply numerical_quotation_total. Qed.

Theorem closed_source_quotation_functional M f v w :
  closed_source_quotation M f v -> closed_source_quotation M f w -> v=w.
Proof. apply numerical_quotation_functional. Qed.

Theorem closed_source_quotation_environment M f b c n v :
  source_bounded M f (zeroM M) ->
  (closed_source_quotation M f v <->
   numerical_quotation M f b c n (succM M (zeroM M)) (zeroM M) v).
Proof.
  intro Hclosed. split; intro Hv.
  - destruct (numerical_quotation_total M f b c n (succM M (zeroM M)) (zeroM M)) as [w Hw].
    pose proof (numerical_quotation_closed_environment M f (zeroM M) (zeroM M)
      (zeroM M) b c n (succM M (zeroM M)) (zeroM M) v w Hclosed Hv Hw) as E.
    now subst w.
  - destruct (closed_source_quotation_total M f) as [w Hw].
    pose proof (numerical_quotation_closed_environment M f b c n (zeroM M)
      (zeroM M) (zeroM M) (succM M (zeroM M)) (zeroM M) v w Hclosed Hv Hw) as E.
    now subst w.
Qed.

Theorem closed_source_quotation_safe M :
  quotation_safe M (zeroM M) (zeroM M) (zeroM M)
    (succM M (zeroM M)) (zeroM M).
Proof. apply quotation_safe_empty. Qed.

Theorem closed_source_quotation_false M v :
  closed_source_quotation M (zeroM M) v <-> v=code_numeral M 1.
Proof.
  split.
  - apply numerical_quotation_invalid. now left.
  - intro E. subst v. apply numerical_quotation_leaf. left. split; [now left|reflexivity].
Qed.

Theorem numerical_zfc_source_axiom_closed M f :
  numerical_zfc_source_axiom M f -> source_bounded M f (zeroM M).
Proof.
  intros [[tag Htag]|[Hsep|Hrep]].
  - exact (zfc_source_graph_closed M tag f Htag).
  - exact (proj1 Hsep).
  - exact (proj1 Hrep).
Qed.

Corollary numerical_zfc_axiom_quotation_environment M f b c n v :
  numerical_zfc_source_axiom M f ->
  (closed_source_quotation M f v <->
   numerical_quotation M f b c n (succM M (zeroM M)) (zeroM M) v).
Proof.
  intro H. apply closed_source_quotation_environment.
  exact (numerical_zfc_source_axiom_closed M f H).
Qed.

Print Assumptions closed_source_quotation_formula_correct.
Print Assumptions closed_source_quotation_total.
Print Assumptions closed_source_quotation_environment.
Print Assumptions closed_source_quotation_false.
Print Assumptions numerical_zfc_source_axiom_closed.
Print Assumptions numerical_zfc_axiom_quotation_environment.

