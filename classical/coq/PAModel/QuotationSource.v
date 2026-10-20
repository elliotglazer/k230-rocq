(** Source correspondence for numerical quotation in the natural-number
    model. This is structural calibration, not nonstandard semantic
    correctness of the set-theoretic interpretation. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
  NumericalProofs ProofTemplates StandardModel SetFormulaCodes SetCodeDescent
  NumericalEnvironments QuotationPayloads QuotationRules NumericalQuotation.
From FOL Require Import FullSyntax Arithmetics.
From Undecidability.FOL Require Import Syntax.BinSig Sets.Signatures.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Fixpoint quotation_number {ff} (env : nat -> nat) (fresh domain : nat)
    (phi : @Core.form sig_empty ZFSignature.ZF_pred_sig full_operators ff) : nat :=
  match phi with
  | falsity => 1
  | atom P v =>
      match P return Vector.t sf_term (ZF_pred_ar P) -> nat with
      | elem => fun v => code_value
          (quotation_atom_parameters (env (sf_index (Vector.hd v)))
            (env (sf_index (Vector.hd (Vector.tl v)))) domain fresh 0)
          (quotation_atom_expression false)
      | equal => fun v => code_value
          (quotation_atom_parameters (env (sf_index (Vector.hd v)))
            (env (sf_index (Vector.hd (Vector.tl v)))) domain fresh 0)
          (quotation_atom_expression true)
      end v
  | bin op a b => code_value
      (quotation_number env fresh domain a .: quotation_number env fresh domain b .: fun _ => 0)
      (quotation_binary_expression
        (match op with Conj => SFAnd | Disj => SFOr | Impl => SFImpl end))
  | quant q a => code_value
      (fresh .: domain .: quotation_number (fresh .: env) (S fresh) domain a .: fun _ => 0)
      (quotation_quantifier_expression (match q with All => true | Ex => false end))
  end.

Fixpoint quotation_expression {ff} (env : nat -> code_expr) (fresh domain : code_expr)
    (phi : @Core.form sig_empty ZFSignature.ZF_pred_sig full_operators ff) : code_expr :=
  match phi with
  | falsity => CEconst 1
  | atom P v =>
      match P return Vector.t sf_term (ZF_pred_ar P) -> code_expr with
      | elem => fun v => code_subst
          (quotation_atom_parameters (env (sf_index (Vector.hd v)))
            (env (sf_index (Vector.hd (Vector.tl v)))) domain fresh (CEconst 0))
          (quotation_atom_expression false)
      | equal => fun v => code_subst
          (quotation_atom_parameters (env (sf_index (Vector.hd v)))
            (env (sf_index (Vector.hd (Vector.tl v)))) domain fresh (CEconst 0))
          (quotation_atom_expression true)
      end v
  | bin op a b => code_subst
      (quotation_expression env fresh domain a .: quotation_expression env fresh domain b .:
        fun _ => CEconst 0)
      (quotation_binary_expression
        (match op with Conj => SFAnd | Disj => SFOr | Impl => SFImpl end))
  | quant q a => code_subst
      (fresh .: domain .:
        quotation_expression (fresh .: env) (CEadd fresh (CEconst 1)) domain a .:
        fun _ => CEconst 0)
      (quotation_quantifier_expression (match q with All => true | Ex => false end))
  end.

Local Opaque KCode230.P.

Lemma quotation_code_value_ext rho rho' e :
  (forall i, rho i = rho' i) -> code_value rho e = code_value rho' e.
Proof. intro H. induction e; cbn; congruence. Qed.

Lemma quotation_code_subst_value rho s e :
  code_value rho (code_subst s e) = code_value (fun i => code_value rho (s i)) e.
Proof. induction e; cbn; congruence. Qed.

Theorem quotation_expression_value_as {ff} rho
    (phi : @Core.form sig_empty ZFSignature.ZF_pred_sig full_operators ff) :
  forall env fresh domain eta k dom,
  (forall i, code_value rho (env i) = eta i) ->
  code_value rho fresh = k -> code_value rho domain = dom ->
  code_value rho (quotation_expression env fresh domain phi) = quotation_number eta k dom phi.
Proof.
  induction phi; intros env fresh domain eta k dom Henv Hk Ht.
  - reflexivity.
  - destruct P; cbn [quotation_expression quotation_number];
      rewrite quotation_code_subst_value; apply quotation_code_value_ext;
      intros [|[|[|[|i]]]]; cbn [quotation_atom_parameters scons]; auto.
  - cbn [quotation_expression quotation_number]. rewrite quotation_code_subst_value.
    apply quotation_code_value_ext. intros [|[|i]]; cbn.
    + now apply IHphi1.
    + now apply IHphi2.
    + reflexivity.
  - cbn [quotation_expression quotation_number]. rewrite quotation_code_subst_value.
    apply quotation_code_value_ext. intros [|[|[|i]]]; cbn.
    + exact Hk.
    + exact Ht.
    + apply IHphi.
      * intros [|j]; cbn; auto.
      * cbn [code_value]. rewrite Hk. lia.
      * exact Ht.
    + reflexivity.
Qed.

Corollary quotation_expression_value {ff} rho env fresh domain
    (phi : @Core.form sig_empty ZFSignature.ZF_pred_sig full_operators ff) :
  code_value rho (quotation_expression env fresh domain phi) =
  quotation_number (fun i => code_value rho (env i))
    (code_value rho fresh) (code_value rho domain) phi.
Proof. apply quotation_expression_value_as; reflexivity. Qed.

Lemma source_constructor_nat h a b :
  sf_relation natModel h a b (sf_make h a b).
Proof. unfold sf_relation,sf_make. rewrite code_relation_natModel. reflexivity. Qed.

Theorem quotation_number_certified {ff}
    (phi : @Core.form sig_empty ZFSignature.ZF_pred_sig full_operators ff) :
  forall env b c n fresh domain,
  (forall i, environment_lookup natModel b c n i (env i)) ->
  numerical_quotation natModel (sf_encode phi) b c n fresh domain
    (quotation_number env fresh domain phi).
Proof.
  induction phi; intros env dividend modulus length fresh domain Henv.
  - apply numerical_quotation_leaf. left. split; [now left|reflexivity].
  - destruct P; apply numerical_quotation_leaf.
    + right; left. exists (sf_index (Vector.hd t)),(sf_index (Vector.hd (Vector.tl t))),
        (env (sf_index (Vector.hd t))),(env (sf_index (Vector.hd (Vector.tl t)))).
      split; [apply source_constructor_nat|].
      split; [apply Henv|]. split; [apply Henv|].
      unfold quotation_atom. rewrite code_relation_natModel. reflexivity.
    + right; right. exists (sf_index (Vector.hd t)),(sf_index (Vector.hd (Vector.tl t))),
        (env (sf_index (Vector.hd t))),(env (sf_index (Vector.hd (Vector.tl t)))).
      split; [apply source_constructor_nat|].
      split; [apply Henv|]. split; [apply Henv|].
      unfold quotation_atom. rewrite code_relation_natModel. reflexivity.
  - destruct b0.
    + eapply numerical_quotation_binary.
      * unfold sf_binary. left. reflexivity.
      * apply source_constructor_nat.
      * apply IHphi1. exact Henv.
      * apply IHphi2. exact Henv.
      * unfold quotation_binary. rewrite code_relation_natModel. reflexivity.
    + eapply numerical_quotation_binary.
      * unfold sf_binary. right; left. reflexivity.
      * apply source_constructor_nat.
      * apply IHphi1. exact Henv.
      * apply IHphi2. exact Henv.
      * unfold quotation_binary. rewrite code_relation_natModel. reflexivity.
    + eapply numerical_quotation_binary.
      * unfold sf_binary. right; right. reflexivity.
      * apply source_constructor_nat.
      * apply IHphi1. exact Henv.
      * apply IHphi2. exact Henv.
      * unfold quotation_binary. rewrite code_relation_natModel. reflexivity.
  - destruct (environment_cons_total natModel dividend modulus length fresh) as [d [e [m Hcons]]].
    assert (Henv' : forall i, environment_lookup natModel d e m i ((fresh .: env) i)).
    { intros [|i]; cbn.
      - apply (proj2 (environment_cons_head natModel dividend modulus length fresh d e m fresh Hcons)). reflexivity.
      - apply (proj2 (environment_cons_tail natModel dividend modulus length fresh d e m i (env i) Hcons)).
        apply Henv. }
    specialize (IHphi (fresh .: env) d e m (S fresh) domain Henv').
    destruct q.
    + eapply (numerical_quotation_unary natModel true).
      * apply source_constructor_nat.
      * exact Hcons.
      * exact IHphi.
      * unfold quotation_quantifier. rewrite code_relation_natModel. reflexivity.
    + eapply (numerical_quotation_unary natModel false).
      * apply source_constructor_nat.
      * exact Hcons.
      * exact IHphi.
      * unfold quotation_quantifier. rewrite code_relation_natModel. reflexivity.
Qed.

Corollary quotation_expression_certified {ff} rho env fresh domain
    (phi : @Core.form sig_empty ZFSignature.ZF_pred_sig full_operators ff) b c n :
  (forall i, environment_lookup natModel b c n i (code_value rho (env i))) ->
  numerical_quotation natModel (sf_encode phi) b c n
    (code_value rho fresh) (code_value rho domain)
    (code_value rho (quotation_expression env fresh domain phi)).
Proof. rewrite quotation_expression_value. apply quotation_number_certified. Qed.

Corollary quotation_zero_environment {ff}
    (phi : @Core.form sig_empty ZFSignature.ZF_pred_sig full_operators ff) fresh domain :
  numerical_quotation natModel (sf_encode phi) 0 0 0 fresh domain
    (quotation_number (fun _ => 0) fresh domain phi).
Proof.
  apply quotation_number_certified. intro i.
  apply (proj2 (environment_empty natModel 0 0 i 0)). reflexivity.
Qed.

Print Assumptions quotation_expression_value.
Print Assumptions quotation_number_certified.
Print Assumptions quotation_expression_certified.
Print Assumptions quotation_zero_environment.
