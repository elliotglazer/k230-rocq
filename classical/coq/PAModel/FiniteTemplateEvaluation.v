(** A structural interface to the existing finite-template code compiler.
    The source formula is externally finite; all names and output codes may
    belong to a nonstandard PA model. This is not induction over arbitrary
    internal source syntax. *)
From PAModel Require Import Model FiniteCoding CodeExpressions CodeDescent CodeTags
  NumericalProofs ProofTemplates SetFormulaCodes QuotientAtomTemplates
  QuotationPayloads QuotationFixedSource NamedLeibnizSteps NumericalVacuitySteps
  NamedExistential NamedBinderFresh TemplateBinderFresh TemplateNamedExclusions TemplateAlpha.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Definition template_binary_head op :=
  match op with Conj=>SFAnd | Disj=>SFOr | Impl=>SFImpl end.
Definition template_quantified M (universal : bool) x a f :=
  if universal then universal_graph M x a f else named_exists_graph M x a f.

Fixpoint template_evaluation M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff)
  (eta : nat -> carrier M) (k f : carrier M) : Prop :=
  match phi with
  | falsity => f=code_numeral M 1
  | atom P args =>
      tagged_pair_graph M (match P with elem=>1 | equal=>3 end)
        (eta (sf_index (Vector.hd args)))
        (eta (sf_index (Vector.hd (Vector.tl args)))) f
  | bin op a b => exists x y,
      template_evaluation M a eta k x /\ template_evaluation M b eta k y /\
      quotation_binary M (template_binary_head op) x y f
  | quant q a => exists x,
      template_evaluation M a (k .: eta) (succM M k) x /\
      template_quantified M (match q with All=>true | Ex=>false end) k x f
  end.

Lemma template_term_graph M rho env eta t :
  (forall i,code_relation M rho (env i) (eta i)) ->
  code_relation M rho (template_term env t) (eta (sf_index t)).
Proof. intro H. destruct t as [i|[]]. exact (H i). Qed.

Lemma template_binary_graph M rho op A B a b f :
  code_relation M rho A a -> code_relation M rho B b ->
  (code_relation M rho
    (match op with Conj=>E_wa A B | Disj=>E_or A B | Impl=>E_wim A B end) f <->
   quotation_binary M (template_binary_head op) a b f).
Proof.
  intros HA HB. destruct op.
  - exact (quotation_binary_substitution_graph M rho SFAnd A B a b f HA HB).
  - exact (quotation_binary_substitution_graph M rho SFOr A B a b f HA HB).
  - exact (quotation_binary_substitution_graph M rho SFImpl A B a b f HA HB).
Qed.

Lemma template_quantified_graph M rho (universal : bool) X A x a f :
  code_relation M rho X x -> code_relation M rho A a ->
  (code_relation M rho (if universal then E_wal X A else E_wex X A) f <->
   template_quantified M universal x a f).
Proof.
  intros HX HA. destruct universal;[now apply expression_universal_iff|now apply named_exists_expression].
Qed.

Theorem template_evaluation_graph M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) :
  forall env fresh rho eta k f,
    (forall i,code_relation M rho (env i) (eta i)) -> code_relation M rho fresh k ->
    (code_relation M rho (template_set_formula env fresh phi) f <->
      template_evaluation M phi eta k f).
Proof.
  induction phi as [|flag P args|flag op a IHa b IHb|flag q a IH];
    intros env fresh rho eta k f HE HK;cbn [template_set_formula template_evaluation].
  - reflexivity.
  - destruct P.
    + exact (ns_atom_expression M rho false _ _ _ _ f
        (template_term_graph M rho env eta _ HE) (template_term_graph M rho env eta _ HE)).
    + exact (ns_atom_expression M rho true _ _ _ _ f
        (template_term_graph M rho env eta _ HE) (template_term_graph M rho env eta _ HE)).
  - split.
    + intro HF.
      destruct (code_relation_total M (template_set_formula env fresh a) rho) as [x HX].
      destruct (code_relation_total M (template_set_formula env fresh b) rho) as [y HY].
      exists x,y. split;[exact (proj1 (IHa env fresh rho eta k x HE HK) HX)|].
      split;[exact (proj1 (IHb env fresh rho eta k y HE HK) HY)|].
      exact (proj1 (template_binary_graph M rho op _ _ x y f HX HY) HF).
    + intros [x [y [HX [HY HF]]]].
      apply (proj2 (template_binary_graph M rho op _ _ x y f
        (proj2 (IHa env fresh rho eta k x HE HK) HX)
        (proj2 (IHb env fresh rho eta k y HE HK) HY))). exact HF.
  - assert (HE' : forall i,code_relation M rho ((fresh .: env) i) ((k .: eta) i)).
    { intros [|i];cbn;auto. }
    pose proof (template_fresh_increment_graph M rho fresh k HK) as HS.
    split.
    + intro HF.
      destruct (code_relation_total M
        (template_set_formula (fresh .: env) (CEadd fresh (CEconst 1)) a) rho) as [x HX].
      exists x. split.
      * exact (proj1 (IH _ _ rho (k .: eta) (succM M k) x HE' HS) HX).
      * destruct q.
        -- exact (proj1 (template_quantified_graph M rho true _ _ k x f HK HX) HF).
        -- exact (proj1 (template_quantified_graph M rho false _ _ k x f HK HX) HF).
    + intros [x [HX HF]].
      pose proof (proj2 (IH _ _ rho (k .: eta) (succM M k) x HE' HS) HX) as HG.
      destruct q.
      * exact (proj2 (template_quantified_graph M rho true _ _ k x f HK HG) HF).
      * exact (proj2 (template_quantified_graph M rho false _ _ k x f HK HG) HF).
Qed.

Definition template_canonical_environment i := CEvar (S i).
Lemma template_evaluation_canonical M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) eta k f :
  code_relation M (k .: eta)
    (template_set_formula template_canonical_environment (CEvar 0) phi) f <->
  template_evaluation M phi eta k f.
Proof. apply template_evaluation_graph;reflexivity. Qed.

Theorem template_evaluation_total M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) eta k :
  exists f,template_evaluation M phi eta k f.
Proof.
  destruct (code_relation_total M
    (template_set_formula template_canonical_environment (CEvar 0) phi) (k .: eta)) as [f HF].
  exists f. exact (proj1 (template_evaluation_canonical M phi eta k f) HF).
Qed.

Lemma template_evaluation_alpha_body M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) eta k x f :
  alpha_template_body M phi eta k x f <-> template_evaluation M phi (x .: eta) k f.
Proof. apply template_evaluation_graph;[intros [|i];reflexivity|reflexivity]. Qed.

Theorem template_evaluation_binder_exclusion M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) eta k y f :
  template_allocations_avoid M phi k y -> template_evaluation M phi eta k f ->
  named_binder_absent M f y.
Proof.
  intros HY HF. apply (template_set_formula_binder_exclusion M phi
    template_canonical_environment (CEvar 0) (k .: eta) k y eq_refl HY f).
  exact (proj2 (template_evaluation_canonical M phi eta k f) HF).
Qed.

Print Assumptions template_evaluation_graph.
Print Assumptions template_evaluation_total.
