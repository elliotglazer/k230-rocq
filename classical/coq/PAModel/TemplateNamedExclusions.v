(** Finite template substitution with name-specific binder exclusions.
    Unlike the below-base theorem, replacement names may be above every
    allocated binder. Free names themselves need not be below the base. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  CodeExpressions NumericalProofs NamedSubstitutionRules NamedSubstitution
  QuotientAtomTemplates TemplateBinderFresh TemplateNamedSubstitution.
From FOL Require Import FullSyntax Arithmetics.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
Unset Implicit Arguments.

Fixpoint template_allocations_avoid M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) (k y : carrier M) : Prop :=
  match phi with
  | falsity => True
  | atom _ _ => True
  | bin _ a b => template_allocations_avoid M a k y /\ template_allocations_avoid M b k y
  | quant _ a => k<>y /\ template_allocations_avoid M a (succM M k) y
  end.

Lemma template_allocations_avoid_below M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) :
  forall k y, coding_lt M y k -> template_allocations_avoid M phi k y.
Proof.
  induction phi; intros k y Hy; cbn [template_allocations_avoid]; try exact I.
  - split; [now apply IHphi1|now apply IHphi2].
  - split; [now apply template_lt_different|].
    apply IHphi. exact (coding_lt_trans M y k (succM M k) Hy (coding_lt_succ M k)).
Qed.

Theorem template_set_formula_binder_exclusion M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) :
  forall env fresh values k y,
    code_relation M values fresh k -> template_allocations_avoid M phi k y ->
    expression_binder_absent M values y (template_set_formula env fresh phi).
Proof.
  induction phi as [|fl P ts|fl op a IHa b IHb|fl quant a IHa];
    intros env fresh values k y Hk Havoid; cbn [template_set_formula].
  - apply expression_binder_absent_one.
  - destruct P; apply expression_binder_absent_atom; auto.
  - destruct Havoid as [Ha Hb]. destruct op.
    + apply expression_binder_absent_conjunction; [eapply IHa|eapply IHb];eassumption.
    + apply expression_binder_absent_disjunction; [eapply IHa|eapply IHb];eassumption.
    + apply expression_binder_absent_implication; [eapply IHa|eapply IHb];eassumption.
  - destruct Havoid as [Hky Havoid].
    assert (Hfresh : forall z, code_relation M values fresh z -> z<>y).
    { intros z Hz. now rewrite (code_relation_functional M fresh values z k Hz Hk). }
    assert (Hbody : expression_binder_absent M values y
      (template_set_formula (fresh .: env) (CEadd fresh (CEconst 1)) a)).
    { apply (IHa (fresh .: env) (CEadd fresh (CEconst 1)) values (succM M k) y).
      - now apply template_fresh_increment_graph.
      - exact Havoid. }
    destruct quant; [now apply expression_binder_absent_universal|now apply expression_binder_absent_existential].
Qed.

Theorem template_set_formula_named_substitution_exclusions M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) :
  forall env env' fresh fresh' values values' k x y,
    x<>zeroM M -> code_relation M values fresh k -> code_relation M values' fresh' k ->
    template_allocations_avoid M phi k x -> template_allocations_avoid M phi k y ->
    (forall i, expression_named_replace M values values' x y (env i) (env' i)) ->
    expression_named_substitution M values values' x y
      (template_set_formula env fresh phi) (template_set_formula env' fresh' phi).
Proof.
  induction phi as [|fl P ts|fl op a IHa b IHb|fl quant a IHa];
    intros env env' fresh fresh' values values' k x y Hx Hk Hk' Hax Hay He;
    cbn [template_set_formula].
  - now apply expression_ns_one.
  - assert (Ht : forall term, expression_named_replace M values values' x y
      (template_term env term) (template_term env' term)).
    { intros [i|f args];[apply He|destruct f]. }
    destruct P; [apply (expression_ns_atom M values values' x y false)|
      apply (expression_ns_atom M values values' x y true)]; apply Ht.
  - destruct Hax as [Haxa Haxb], Hay as [Haya Hayb]. destruct op.
    + apply expression_ns_conjunction;[exact Hx|eapply IHa|eapply IHb];eassumption.
    + apply expression_ns_disjunction;[exact Hx|eapply IHa|eapply IHb];eassumption.
    + apply expression_ns_implication;[eapply IHa|eapply IHb];eassumption.
  - destruct Hax as [Hkx Hax], Hay as [Hky Hay].
    assert (He' : forall i, expression_named_replace M values values' x y
      ((fresh .: env) i) ((fresh' .: env') i)).
    { intros [|i]; [|apply He]. intros u u' Hu Hu'.
      rewrite (code_relation_functional M fresh values u k Hu Hk),
        (code_relation_functional M fresh' values' u' k Hu' Hk').
      right. auto. }
    assert (Hbody : expression_named_substitution M values values' x y
      (template_set_formula (fresh .: env) (CEadd fresh (CEconst 1)) a)
      (template_set_formula (fresh' .: env') (CEadd fresh' (CEconst 1)) a)).
    { apply (IHa (fresh .: env) (fresh' .: env')
        (CEadd fresh (CEconst 1)) (CEadd fresh' (CEconst 1))
        values values' (succM M k) x y Hx).
      - now apply template_fresh_increment_graph.
      - now apply template_fresh_increment_graph.
      - exact Hax.
      - exact Hay.
      - exact He'. }
    destruct quant.
    + eapply expression_ns_universal; eassumption.
    + eapply expression_ns_existential; eassumption.
Qed.

Print Assumptions template_allocations_avoid_below.
Print Assumptions template_set_formula_binder_exclusion.
Print Assumptions template_set_formula_named_substitution_exclusions.
