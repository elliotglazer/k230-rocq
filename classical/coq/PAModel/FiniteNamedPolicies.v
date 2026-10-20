(** Fixed named-formula compilation with an explicit binder policy. This
    isolates normalization of the old negated-reflexivity bottom from the
    separate problem of converting between binder policies. *)
From PAModel Require Import Model CodeExpressions NumericalProofs ProofTemplates
  TemplateCD TemplatePropositional ProofMacros NumericalEquality NamedLeibnizSteps
  NumericalEquivalence NumericalVacuitySteps QuotientAtomTemplates SetFormulaCodes.
From Undecidability.FOL Require Import Syntax.BinSig Syntax.Facts Sets.minZF.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List Arith.PeanoNat.
Import ListNotations.
Unset Implicit Arguments.

Definition named_bottom_expression x := E_wn (E_wal x (E_weq x x)).

Lemma named_reflexivity_all_proved M rho x :
  ns_proof M rho (E_wal x (E_weq x x)).
Proof.
  apply (ns_proof_macro M rho (E_weq x x :: nil)).
  - intros e [<-|[]] f HF. destruct (code_relation_total M x rho) as [v HV].
    exact (numerical_expression_reflexivity M rho x v f HV HF).
  - apply PM_gen,PM_input. now left.
Qed.

Theorem named_bottom_normalization M rho x :
  expression_equivalent M rho (named_bottom_expression x) (CEconst 1).
Proof.
  split.
  - apply (ns_proof_macro M rho (E_wal x (E_weq x x) :: nil)).
    + intros e [<-|[]]. apply named_reflexivity_all_proved.
    + unfold named_bottom_expression,E_wn.
      apply macro_discharge,macro_deduction.
      eapply md_mp.
      * apply md_global,PM_input. now left.
      * apply md_hyp. now left.
  - apply ns_proof_template,template_F.
Qed.

Fixpoint named_policy_depth {ff}
    (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) : nat :=
  match phi with
  | falsity => 0
  | atom _ _ => 0
  | bin _ a b => Nat.max (named_policy_depth a) (named_policy_depth b)
  | quant _ a => S (named_policy_depth a)
  end.

Definition named_binder_policy := code_expr -> nat -> code_expr.
Definition sequential_binder_policy : named_binder_policy := fun fresh _ => fresh.
Definition depth_binder_policy : named_binder_policy := fun _ depth => CEconst (2 * depth + 2).

Fixpoint named_policy_formula {ff} (legacy_negation : bool) (bottom : code_expr)
    (policy : named_binder_policy) (env : nat -> code_expr) (fresh : code_expr)
    (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) : code_expr :=
  match phi with
  | falsity => bottom
  | atom P args =>
      match P return Vector.t set_term (ar_preds P) -> code_expr with
      | elem => fun args => E_wel (template_term env (Vector.hd args))
          (template_term env (Vector.hd (Vector.tl args)))
      | equal => fun args => E_weq (template_term env (Vector.hd args))
          (template_term env (Vector.hd (Vector.tl args)))
      end args
  | bin Conj a b => E_wa (named_policy_formula legacy_negation bottom policy env fresh a)
      (named_policy_formula legacy_negation bottom policy env fresh b)
  | bin Disj a b => E_or (named_policy_formula legacy_negation bottom policy env fresh a)
      (named_policy_formula legacy_negation bottom policy env fresh b)
  | bin Impl a b =>
      if legacy_negation then
        match b with
        | falsity => E_wn (named_policy_formula legacy_negation bottom policy env fresh a)
        | _ => E_wim (named_policy_formula legacy_negation bottom policy env fresh a)
            (named_policy_formula legacy_negation bottom policy env fresh b)
        end
      else E_wim (named_policy_formula legacy_negation bottom policy env fresh a)
        (named_policy_formula legacy_negation bottom policy env fresh b)
  | quant q a =>
      let x := policy fresh (named_policy_depth a) in
      let body := named_policy_formula legacy_negation bottom policy (x .: env)
        (CEadd fresh (CEconst 1)) a in
      match q with All => E_wal x body | Ex => E_wex x body end
  end.

Theorem sequential_policy_exact {ff}
    (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) :
  forall env fresh, named_policy_formula false (CEconst 1)
    sequential_binder_policy env fresh phi = template_set_formula env fresh phi.
Proof.
  induction phi as [|ff P args|ff op a IHa b IHb|ff q a IH]; intros env fresh.
  - reflexivity.
  - destruct P;reflexivity.
  - destruct op;cbn [named_policy_formula template_set_formula];now rewrite IHa,IHb.
  - destruct q;cbn [named_policy_formula sequential_binder_policy template_set_formula];now rewrite IH.
Qed.

Theorem named_policy_bottom_normalization M rho {ff}
    (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) :
  forall legacy policy env fresh bottom_name,
    expression_equivalent M rho
      (named_policy_formula legacy (named_bottom_expression bottom_name) policy env fresh phi)
      (named_policy_formula false (CEconst 1) policy env fresh phi).
Proof.
  induction phi as [|ff P args|ff op a IHa b IHb|ff q a IH];
    intros legacy policy env fresh bottom_name.
  - apply named_bottom_normalization.
  - destruct P;apply expression_equivalent_refl.
  - destruct op.
    + apply expression_equivalent_conjunction;[apply IHa|apply IHb].
    + apply expression_equivalent_disjunction;[apply IHa|apply IHb].
    + destruct legacy.
      * destruct b;cbn [named_policy_formula].
        -- apply expression_equivalent_negation. apply IHa.
        -- apply expression_equivalent_implication;[apply IHa|exact (IHb true policy env fresh bottom_name)].
        -- apply expression_equivalent_implication;[apply IHa|exact (IHb true policy env fresh bottom_name)].
        -- apply expression_equivalent_implication;[apply IHa|exact (IHb true policy env fresh bottom_name)].
      * apply expression_equivalent_implication;[apply IHa|apply IHb].
  - destruct q;cbn [named_policy_formula].
    + apply expression_equivalent_all. apply IH.
    + apply expression_equivalent_exists. apply IH.
Qed.

Corollary sequential_bottom_normalization M rho {ff}
    (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) env fresh bottom_name :
  expression_equivalent M rho
    (named_policy_formula true (named_bottom_expression bottom_name)
      sequential_binder_policy env fresh phi)
    (template_set_formula env fresh phi).
Proof.
  rewrite <- sequential_policy_exact.
  apply named_policy_bottom_normalization.
Qed.

Corollary named_policy_normalization_codes M rho {ff}
    (phi : @Core.form sig_empty ZF_pred_sig full_operators ff)
    legacy policy env fresh bottom_name old normalized :
  code_relation M rho
    (named_policy_formula legacy (named_bottom_expression bottom_name) policy env fresh phi) old ->
  code_relation M rho (named_policy_formula false (CEconst 1) policy env fresh phi) normalized ->
  numerical_equivalent M old normalized.
Proof.
  intros HO HN. apply (proj1 (numerical_equivalent_expression M rho _ _ old normalized HO HN)).
  apply named_policy_bottom_normalization.
Qed.

Corollary named_policy_normalized_proof M rho {ff}
    (phi : @Core.form sig_empty ZF_pred_sig full_operators ff)
    legacy policy env fresh bottom_name :
  ns_proof M rho
    (named_policy_formula legacy (named_bottom_expression bottom_name) policy env fresh phi) ->
  ns_proof M rho (named_policy_formula false (CEconst 1) policy env fresh phi).
Proof.
  intros HP normalized HN.
  destruct (code_relation_total M
    (named_policy_formula legacy (named_bottom_expression bottom_name) policy env fresh phi) rho)
    as [old HO].
  apply (numerical_implies_apply M old normalized);[|exact (HP old HO)].
  exact (proj1 (named_policy_normalization_codes M rho phi legacy policy env fresh bottom_name
    old normalized HO HN)).
Qed.

Corollary sequential_normalized_proof M rho {ff}
    (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) env fresh bottom_name :
  ns_proof M rho
    (named_policy_formula true (named_bottom_expression bottom_name)
      sequential_binder_policy env fresh phi) ->
  ns_proof M rho (template_set_formula env fresh phi).
Proof.
  rewrite <- sequential_policy_exact. apply named_policy_normalized_proof.
Qed.

Print Assumptions named_bottom_normalization.
Print Assumptions sequential_policy_exact.
Print Assumptions named_policy_bottom_normalization.
Print Assumptions sequential_bottom_normalization.
Print Assumptions named_policy_normalization_codes.
Print Assumptions named_policy_normalized_proof.
Print Assumptions sequential_normalized_proof.
