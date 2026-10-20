(** Literal port of the pinned KQuotFormula.qtrans definition, followed by
    exact equality of its named-code compilation with quotation_expression.
    This is a finite syntax theorem, not a theorem about nonstandard proofs. *)
From PAModel Require Import CodeExpressions ProofTemplates QuotientAtomTemplates
  SetFormulaCodes QuotationPayloads QuotationSource StandardModel
  NumericalEnvironments NumericalQuotation.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
Import Vector.VectorNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Fixpoint source_qtrans {ff} (t : set_term)
    (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) : set_form :=
  match phi with
  | falsity => falsity
  | atom P v =>
      match P return Vector.t set_term (ar_preds P) -> set_form with
      | elem => fun v => source_dmem t (Vector.hd v) (Vector.hd (Vector.tl v))
      | equal => fun v => source_deqv t (Vector.hd v) (Vector.hd (Vector.tl v))
      end v
  | bin op a b => bin op (source_qtrans t a) (source_qtrans t b)
  | quant All a => ∀ (t`[↑] ∈' $0 → source_qtrans t`[↑] a)
  | quant Ex a => ∃ (t`[↑] ∈' $0 ∧ source_qtrans t`[↑] a)
  end.

Lemma template_term_index env t : template_term env t = env (sf_index t).
Proof. destruct t as [i|[]]; reflexivity. Qed.

Lemma template_term_shift env fresh t :
  template_term (fresh .: env) t`[↑] = template_term env t.
Proof. destruct t as [i|[]]; reflexivity. Qed.

Lemma template_dmem_exact env fresh t x y :
  template_set_formula env fresh (source_dmem t x y) =
  code_subst (quotation_atom_parameters (template_term env x)
    (template_term env y) (template_term env t) fresh (CEconst 0))
    (quotation_atom_expression false).
Proof.
  destruct t as [i|[]], x as [j|[]], y as [k|[]]. reflexivity.
Qed.

Lemma template_deqv_exact env fresh t x y :
  template_set_formula env fresh (source_deqv t x y) =
  code_subst (quotation_atom_parameters (template_term env x)
    (template_term env y) (template_term env t) fresh (CEconst 0))
    (quotation_atom_expression true).
Proof.
  destruct t as [i|[]], x as [j|[]], y as [k|[]]. reflexivity.
Qed.

Theorem template_qtrans_exact {ff}
    (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) env fresh t :
  template_set_formula env fresh (source_qtrans t phi) =
  quotation_expression env fresh (template_term env t) phi.
Proof.
  induction phi in env,fresh,t |- *.
  - reflexivity.
  - destruct P; cbn [source_qtrans quotation_expression].
    + rewrite template_dmem_exact, !template_term_index. reflexivity.
    + rewrite template_deqv_exact, !template_term_index. reflexivity.
  - destruct b0; cbn [source_qtrans template_set_formula quotation_expression];
      rewrite IHphi1, IHphi2; reflexivity.
  - destruct q; destruct t as [j|[]];
      cbn [source_qtrans template_set_formula quotation_expression];
      rewrite IHphi; reflexivity.
Qed.

Corollary template_qtrans_value {ff} rho
    (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) env fresh t :
  code_value rho (template_set_formula env fresh (source_qtrans t phi)) =
  quotation_number (fun i => code_value rho (env i))
    (code_value rho fresh) (code_value rho (template_term env t)) phi.
Proof. rewrite template_qtrans_exact. apply quotation_expression_value. Qed.

Corollary template_qtrans_certified {ff} rho
    (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) env fresh t b c n :
  (forall i, environment_lookup natModel b c n i (code_value rho (env i))) ->
  numerical_quotation natModel (sf_encode phi) b c n (code_value rho fresh)
    (code_value rho (template_term env t))
    (code_value rho (template_set_formula env fresh (source_qtrans t phi))).
Proof. rewrite template_qtrans_exact. apply quotation_expression_certified. Qed.

Print Assumptions template_dmem_exact.
Print Assumptions template_deqv_exact.
Print Assumptions template_qtrans_exact.
Print Assumptions template_qtrans_value.
Print Assumptions template_qtrans_certified.
