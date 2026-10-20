(** Binder absence below the fresh-name base of finite named templates. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT Pairing
  CodeExpressions NumericalProofs CodeDescent CodeTags FreshNames
  NamedBinderFresh NamedBinderConstructors ProofTemplates QuotientAtomTemplates QuotationPayloads.
From FOL Require Import FullSyntax Arithmetics.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Definition expression_binder_absent M env y e :=
  forall v, code_relation M env e v -> named_binder_absent M v y.

Lemma expression_tagged_graph M env tag a b x y f :
  code_relation M env a x -> code_relation M env b y ->
  code_relation M env (CEadd (E_wim a b) (CEconst tag)) f ->
  tagged_pair_graph M tag x y f.
Proof.
  intros Ha Hb [q [n [Hq [Hn Hf]]]]. change (n=code_numeral M tag) in Hn. subst n.
  apply (expression_implication_graph M env a b x y q Ha Hb) in Hq.
  apply implication_graph_tagged in Hq. destruct Hq as [p [Hp Hq]].
  exists p. split; [exact Hp|]. now rewrite (coding_add_zero_r M) in Hq; rewrite Hq in Hf.
Qed.

Lemma named_binder_absent_one M y : named_binder_absent M (code_numeral M 1) y.
Proof.
  apply (named_binder_absent_membership M (zeroM M) (zeroM M)).
  exists (zeroM M). split; [apply pair_zero|].
  rewrite (mul_comm M (code_numeral M 4)), (Arithmetic.mul_zero M), (Arithmetic.add_zero M). reflexivity.
Qed.

Lemma expression_binder_absent_one M env y : expression_binder_absent M env y (CEconst 1).
Proof. intros v H. change (v=code_numeral M 1) in H. subst v. apply named_binder_absent_one. Qed.

Lemma expression_binder_absent_atom M env tag a b y :
  tag=1 \/ tag=3 -> expression_binder_absent M env y (CEadd (E_wim a b) (CEconst tag)).
Proof.
  intros Htag f Hf. destruct (code_relation_total M a env) as [x Hx].
  destruct (code_relation_total M b env) as [z Hz].
  apply (named_binder_absent_atom M tag x z f y Htag).
  exact (expression_tagged_graph M env tag a b x z f Hx Hz Hf).
Qed.

Lemma expression_binder_absent_implication M env y a b :
  expression_binder_absent M env y a -> expression_binder_absent M env y b ->
  expression_binder_absent M env y (E_wim a b).
Proof.
  intros Ha Hb f Hf. destruct (code_relation_total M a env) as [x Hx].
  destruct (code_relation_total M b env) as [z Hz].
  exact (named_binder_absent_implication M x z f y
    (expression_implication_graph M env a b x z f Hx Hz Hf) (Ha x Hx) (Hb z Hz)).
Qed.

Lemma expression_binder_absent_negation M env y a :
  expression_binder_absent M env y a -> expression_binder_absent M env y (E_wn a).
Proof. intro H. apply expression_binder_absent_implication; [exact H|apply expression_binder_absent_one]. Qed.

Lemma expression_binder_absent_conjunction M env y a b :
  expression_binder_absent M env y a -> expression_binder_absent M env y b ->
  expression_binder_absent M env y (E_wa a b).
Proof.
  intros Ha Hb. apply expression_binder_absent_negation.
  apply expression_binder_absent_implication; [exact Ha|now apply expression_binder_absent_negation].
Qed.

Lemma expression_binder_absent_disjunction M env y a b :
  expression_binder_absent M env y a -> expression_binder_absent M env y b ->
  expression_binder_absent M env y (E_or a b).
Proof.
  intros Ha Hb. apply expression_binder_absent_implication;
    [now apply expression_binder_absent_negation|exact Hb].
Qed.

Lemma expression_binder_absent_universal M env y a b :
  (forall k, code_relation M env a k -> k<>y) -> expression_binder_absent M env y b ->
  expression_binder_absent M env y (E_wal a b).
Proof.
  intros Ha Hb f Hf. destruct (code_relation_total M a env) as [x Hx].
  destruct (code_relation_total M b env) as [z Hz].
  exact (named_binder_absent_universal M x z f y
    (expression_universal_graph M env a b x z f Hx Hz Hf) (Ha x Hx) (Hb z Hz)).
Qed.

Lemma expression_binder_absent_existential M env y a b :
  (forall k, code_relation M env a k -> k<>y) -> expression_binder_absent M env y b ->
  expression_binder_absent M env y (E_wex a b).
Proof.
  intros Ha Hb. apply expression_binder_absent_negation.
  apply expression_binder_absent_universal; [exact Ha|now apply expression_binder_absent_negation].
Qed.

Lemma template_fresh_increment_graph M env fresh k :
  code_relation M env fresh k ->
  code_relation M env (CEadd fresh (CEconst 1)) (succM M k).
Proof.
  intro H. exists k,(code_numeral M 1). split;[exact H|]. split;[reflexivity|].
  change (succM M k = addM M k (succM M (zeroM M))).
  now rewrite (Arithmetic.add_comm M k), (Arithmetic.add_succ M), (Arithmetic.add_zero M).
Qed.

Theorem template_set_formula_binder_absent M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) :
  forall env fresh values k y,
    code_relation M values fresh k -> coding_lt M y k ->
    expression_binder_absent M values y (template_set_formula env fresh phi).
Proof.
  induction phi as [|fl P ts|fl op a IHa b IHb|fl quant a IHa];
    intros env fresh values k y Hk Hy; cbn [template_set_formula].
  - apply expression_binder_absent_one.
  - destruct P; apply expression_binder_absent_atom; auto.
  - destruct op.
    + apply expression_binder_absent_conjunction; [exact (IHa env fresh values k y Hk Hy)|exact (IHb env fresh values k y Hk Hy)].
    + apply expression_binder_absent_disjunction; [exact (IHa env fresh values k y Hk Hy)|exact (IHb env fresh values k y Hk Hy)].
    + apply expression_binder_absent_implication; [exact (IHa env fresh values k y Hk Hy)|exact (IHb env fresh values k y Hk Hy)].
  - assert (Hne : forall z, code_relation M values fresh z -> z<>y).
    { intros z Hz. rewrite (code_relation_functional M fresh values z k Hz Hk).
      intro E. subst k. exact (@Peano.lt_neq (carrier M) (raw_interpretation M)
        (fun ax H rho => axioms M ax rho H) y y Hy eq_refl). }
    assert (Hbody : expression_binder_absent M values y
      (template_set_formula (fresh .: env) (CEadd fresh (CEconst 1)) a)).
    { apply (IHa (fresh .: env) (CEadd fresh (CEconst 1)) values (succM M k) y).
      - now apply template_fresh_increment_graph.
      - exact (coding_lt_trans M y k (succM M k) Hy (coding_lt_succ M k)). }
    destruct quant.
    + now apply expression_binder_absent_universal.
    + now apply expression_binder_absent_existential.
Qed.

Theorem quotation_atom_binder_absent M equality x z t k v y :
  quotation_atom M equality x z t k v -> coding_lt M y k -> named_binder_absent M v y.
Proof.
  intros Hv Hy. destruct equality; unfold quotation_atom,quotation_atom_expression in Hv.
  - exact (template_set_formula_binder_absent M (source_deqv $0 $1 $2)
      quotient_atom_environment (CEvar 3) (quotation_atom_parameters x z t k (zeroM M)) k y eq_refl Hy v Hv).
  - exact (template_set_formula_binder_absent M (source_dmem $0 $1 $2)
      quotient_atom_environment (CEvar 3) (quotation_atom_parameters x z t k (zeroM M)) k y eq_refl Hy v Hv).
Qed.

Print Assumptions template_set_formula_binder_absent.
Print Assumptions quotation_atom_binder_absent.
