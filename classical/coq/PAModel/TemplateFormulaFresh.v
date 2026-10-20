(** Full name freshness for finite templates. The zero name is excluded
    explicitly because encoded falsity is the raw membership atom 0 in 0. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT Pairing
  CodeExpressions NumericalProofs CodeDescent CodeTags FreshNames
  FormulaFreshConstructors ProofTemplates TemplateBinderFresh
  QuotientAtomTemplates QuotationPayloads.
From FOL Require Import FullSyntax Arithmetics.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Definition expression_fresh M env y e :=
  forall v, code_relation M env e v -> formula_fresh M v y.
Definition expression_name_avoids M env y e :=
  forall v, code_relation M env e v -> v<>y.

Lemma formula_fresh_one M y : y<>zeroM M -> formula_fresh M (code_numeral M 1) y.
Proof.
  intro Hy. apply (formula_fresh_membership_intro M (zeroM M) (zeroM M));
    try (intro E; apply Hy; symmetry; exact E).
  exists (zeroM M). split; [apply pair_zero|].
  rewrite (mul_comm M (code_numeral M 4)), (Arithmetic.mul_zero M), (Arithmetic.add_zero M).
  reflexivity.
Qed.

Lemma expression_fresh_one M env y : y<>zeroM M -> expression_fresh M env y (CEconst 1).
Proof. intros Hy v Hv. change (v=code_numeral M 1) in Hv. subst v. now apply formula_fresh_one. Qed.

Lemma expression_fresh_atom M env tag a b y :
  tag=1 \/ tag=3 -> expression_name_avoids M env y a -> expression_name_avoids M env y b ->
  expression_fresh M env y (CEadd (E_wim a b) (CEconst tag)).
Proof.
  intros Htag Ha Hb f Hf. destruct (code_relation_total M a env) as [x Hx].
  destruct (code_relation_total M b env) as [z Hz].
  exact (formula_fresh_atom M tag x z f y Htag
    (expression_tagged_graph M env tag a b x z f Hx Hz Hf) (Ha x Hx) (Hb z Hz)).
Qed.

Lemma expression_fresh_implication M env y a b :
  expression_fresh M env y a -> expression_fresh M env y b -> expression_fresh M env y (E_wim a b).
Proof.
  intros Ha Hb f Hf. destruct (code_relation_total M a env) as [x Hx].
  destruct (code_relation_total M b env) as [z Hz].
  exact (formula_fresh_implication_intro M x z f y
    (expression_implication_graph M env a b x z f Hx Hz Hf) (Ha x Hx) (Hb z Hz)).
Qed.

Lemma expression_fresh_negation M env y a :
  y<>zeroM M -> expression_fresh M env y a -> expression_fresh M env y (E_wn a).
Proof.
  intros Hy H. apply expression_fresh_implication; [exact H|now apply expression_fresh_one].
Qed.

Lemma expression_fresh_conjunction M env y a b :
  y<>zeroM M -> expression_fresh M env y a -> expression_fresh M env y b ->
  expression_fresh M env y (E_wa a b).
Proof.
  intros Hy Ha Hb. apply expression_fresh_negation; [exact Hy|].
  apply expression_fresh_implication; [exact Ha|now apply expression_fresh_negation].
Qed.

Lemma expression_fresh_disjunction M env y a b :
  y<>zeroM M -> expression_fresh M env y a -> expression_fresh M env y b ->
  expression_fresh M env y (E_or a b).
Proof.
  intros Hy Ha Hb. apply expression_fresh_implication;
    [now apply expression_fresh_negation|exact Hb].
Qed.

Lemma expression_fresh_universal M env y a b :
  expression_name_avoids M env y a -> expression_fresh M env y b ->
  expression_fresh M env y (E_wal a b).
Proof.
  intros Ha Hb f Hf. destruct (code_relation_total M a env) as [x Hx].
  destruct (code_relation_total M b env) as [z Hz].
  exact (formula_fresh_universal_intro M x z f y
    (expression_universal_graph M env a b x z f Hx Hz Hf) (Ha x Hx) (Hb z Hz)).
Qed.

Lemma expression_fresh_existential M env y a b :
  y<>zeroM M -> expression_name_avoids M env y a -> expression_fresh M env y b ->
  expression_fresh M env y (E_wex a b).
Proof.
  intros Hy Ha Hb. apply expression_fresh_negation; [exact Hy|].
  apply expression_fresh_universal; [exact Ha|now apply expression_fresh_negation].
Qed.

Lemma template_term_name_avoids M env values y t :
  (forall i, expression_name_avoids M values y (env i)) ->
  expression_name_avoids M values y (template_term env t).
Proof. intro H. destruct t as [i|[]]. exact (H i). Qed.

Theorem template_set_formula_fresh M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) :
  forall env fresh values k y,
    code_relation M values fresh k -> coding_lt M y k -> y<>zeroM M ->
    (forall i, expression_name_avoids M values y (env i)) ->
    expression_fresh M values y (template_set_formula env fresh phi).
Proof.
  induction phi as [|fl P ts|fl op a IHa b IHb|fl quant a IHa];
    intros env fresh values k y Hk Hy Hzero Henv; cbn [template_set_formula].
  - now apply expression_fresh_one.
  - destruct P; apply expression_fresh_atom; try (now left); try (now right);
      apply template_term_name_avoids; exact Henv.
  - destruct op.
    + apply expression_fresh_conjunction; [exact Hzero| |];
        [exact (IHa env fresh values k y Hk Hy Hzero Henv)|exact (IHb env fresh values k y Hk Hy Hzero Henv)].
    + apply expression_fresh_disjunction; [exact Hzero| |];
        [exact (IHa env fresh values k y Hk Hy Hzero Henv)|exact (IHb env fresh values k y Hk Hy Hzero Henv)].
    + apply expression_fresh_implication;
        [exact (IHa env fresh values k y Hk Hy Hzero Henv)|exact (IHb env fresh values k y Hk Hy Hzero Henv)].
  - assert (Hne : expression_name_avoids M values y fresh).
    { intros z Hz. rewrite (code_relation_functional M fresh values z k Hz Hk).
      intro E. subst k. exact (@Peano.lt_neq (carrier M) (raw_interpretation M)
        (fun ax H rho => axioms M ax rho H) y y Hy eq_refl). }
    assert (Hbody : expression_fresh M values y
      (template_set_formula (fresh .: env) (CEadd fresh (CEconst 1)) a)).
    { apply (IHa (fresh .: env) (CEadd fresh (CEconst 1)) values (succM M k) y).
      - now apply template_fresh_increment_graph.
      - exact (coding_lt_trans M y k (succM M k) Hy (coding_lt_succ M k)).
      - exact Hzero.
      - intros [|i]; [exact Hne|apply Henv]. }
    destruct quant.
    + now apply expression_fresh_universal.
    + now apply expression_fresh_existential.
Qed.

Theorem quotation_atom_fresh M equality x z t k v y :
  quotation_atom M equality x z t k v -> coding_lt M y k ->
  y<>zeroM M -> x<>y -> z<>y -> t<>y -> formula_fresh M v y.
Proof.
  intros Hv Hy Hzero Hx Hz Ht.
  assert (Henv : forall i, expression_name_avoids M
    (quotation_atom_parameters x z t k (zeroM M)) y (quotient_atom_environment i)).
  { intros [|[|i]] u Hu; cbn [quotient_atom_environment code_relation quotation_atom_parameters] in Hu;
      subst u; assumption. }
  destruct equality; unfold quotation_atom,quotation_atom_expression in Hv.
  - exact (template_set_formula_fresh M (source_deqv $0 $1 $2)
      quotient_atom_environment (CEvar 3) (quotation_atom_parameters x z t k (zeroM M)) k y
      eq_refl Hy Hzero Henv v Hv).
  - exact (template_set_formula_fresh M (source_dmem $0 $1 $2)
      quotient_atom_environment (CEvar 3) (quotation_atom_parameters x z t k (zeroM M)) k y
      eq_refl Hy Hzero Henv v Hv).
Qed.

Print Assumptions template_set_formula_fresh.
Print Assumptions quotation_atom_fresh.
