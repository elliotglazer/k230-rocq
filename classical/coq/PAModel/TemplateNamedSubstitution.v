(** Named substitution commutes with finite quotient templates below their
    fresh binder base. The actual membership code 1 is fixed only because
    the substituted name is explicitly different from 0. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT Pairing
  CodeExpressions CodeDescent CodeTags NumericalProofs NumericalVacuity ProofTemplates
  NamedSubstitutionRules NamedSubstitution NamedSubstitutionFunctionality NamedSubstitutionLaws
  QuotientAtomTemplates TemplateBinderFresh QuotationPayloads.
From FOL Require Import FullSyntax Arithmetics.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Lemma ns_combine_atom M equality a b f a' b' g x y :
  tagged_pair_graph M (named_atom_tag equality) a b f ->
  tagged_pair_graph M (named_atom_tag equality) a' b' g ->
  named_replace M x y a a' -> named_replace M x y b b' ->
  named_substitution M f x y g.
Proof.
  intros Hf Hg Ha Hb.
  destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) x y) as [E|Hxy].
  - subst y. pose proof (named_replace_identity M x a a' Ha) as Ea.
    pose proof (named_replace_identity M x b b' Hb) as Eb. subst a' b'.
    rewrite <- (tagged_pair_functional M (named_atom_tag equality) a b f g Hf Hg).
    apply named_substitution_identity.
  - apply (proj2 (named_substitution_atom_iff M equality a b f x y g Hxy Hf)).
    exists a',b'. auto.
Qed.

Lemma ns_zero_implication M : implication_graph M (zeroM M) (zeroM M) (zeroM M).
Proof.
  apply implication_graph_tagged. exists (zeroM M). split; [apply pair_zero|].
  change (zeroM M=addM M (mulM M (code_numeral M 4) (zeroM M)) (zeroM M)).
  rewrite (Arithmetic.mul_comm M),Arithmetic.mul_zero,Arithmetic.add_zero. reflexivity.
Qed.

Lemma ns_combine_implication M a b f a' b' g x y :
  implication_graph M a b f -> implication_graph M a' b' g ->
  named_substitution M a x y a' -> named_substitution M b x y b' ->
  named_substitution M f x y g.
Proof.
  intros Hf Hg Ha Hb.
  destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) x y) as [E|Hxy].
  - subst y. pose proof (named_substitution_identity_inv M a x a' Ha) as Ea.
    pose proof (named_substitution_identity_inv M b x b' Hb) as Eb. subst a' b'.
    apply implication_graph_tagged in Hf,Hg.
    rewrite <- (tagged_pair_functional M 0 a b f g Hf Hg).
    apply named_substitution_identity.
  - destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
      (fun ax H rho => axioms M ax rho H) f (zeroM M)) as [E|Hnz].
    + subst f. pose proof (ns_zero_implication M) as Hz.
      apply implication_graph_tagged in Hf,Hz.
      destruct (tagged_pair_decode_unique M 0 0 a b (zeroM M) (zeroM M) (zeroM M)
        ltac:(lia) ltac:(lia) Hf Hz) as [_ [Ea Eb]]. subst a b.
      pose proof (named_substitution_zero_inv M x y a' Ha) as Ea.
      pose proof (named_substitution_zero_inv M x y b' Hb) as Eb. subst a' b'.
      apply implication_graph_tagged in Hg.
      rewrite (tagged_pair_functional M 0 (zeroM M) (zeroM M) g (zeroM M) Hg Hz).
      apply named_substitution_zero.
    + apply (proj2 (named_substitution_implication_iff M a b f x y g Hxy Hnz Hf)).
      exists a',b'. auto.
Qed.

Lemma ns_combine_universal M z a f a' g x y :
  z<>x -> z<>y -> universal_graph M z a f -> universal_graph M z a' g ->
  named_substitution M a x y a' -> named_substitution M f x y g.
Proof.
  intros Hzx Hzy Hf Hg Ha.
  destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) x y) as [E|Hxy].
  - subst y. pose proof (named_substitution_identity_inv M a x a' Ha) as Ea. subst a'.
    apply universal_graph_tagged in Hf,Hg.
    rewrite <- (tagged_pair_functional M 2 z a f g Hf Hg).
    apply named_substitution_identity.
  - apply (proj2 (named_substitution_universal_iff M z a f x y g Hxy Hzx Hf)).
    split;[exact Hzy|]. exists a'. auto.
Qed.

Lemma named_substitution_one_fixed M x y :
  x<>zeroM M -> named_substitution M (code_numeral M 1) x y (code_numeral M 1).
Proof.
  intro Hx. assert (Hone : membership_graph M (zeroM M) (zeroM M) (code_numeral M 1)).
  { exists (zeroM M). split;[apply pair_zero|].
    rewrite (Arithmetic.mul_comm M),Arithmetic.mul_zero,Arithmetic.add_zero. reflexivity. }
  apply (ns_combine_atom M false (zeroM M) (zeroM M) (code_numeral M 1)
    (zeroM M) (zeroM M) (code_numeral M 1) x y Hone Hone);
    right; split; congruence.
Qed.

Definition expression_named_replace M values values' x y a a' :=
  forall u u',code_relation M values a u -> code_relation M values' a' u' ->
    named_replace M x y u u'.
Definition expression_named_substitution M values values' x y a a' :=
  forall u u',code_relation M values a u -> code_relation M values' a' u' ->
    named_substitution M u x y u'.

Lemma expression_ns_one M values values' x y : x<>zeroM M ->
  expression_named_substitution M values values' x y (CEconst 1) (CEconst 1).
Proof. intros Hx u u' -> ->. now apply named_substitution_one_fixed. Qed.

Lemma expression_ns_atom M values values' x y equality a b a' b' :
  expression_named_replace M values values' x y a a' ->
  expression_named_replace M values values' x y b b' ->
  expression_named_substitution M values values' x y
    (E_atom equality a b) (E_atom equality a' b').
Proof.
  intros Ha Hb u u' Hu Hu'.
  destruct (code_relation_total M a values) as [v Hv].
  destruct (code_relation_total M b values) as [w Hw].
  destruct (code_relation_total M a' values') as [v' Hv'].
  destruct (code_relation_total M b' values') as [w' Hw'].
  apply (ns_combine_atom M equality v w u v' w' u' x y).
  - destruct equality; exact (expression_tagged_graph M values _ a b v w u Hv Hw Hu).
  - destruct equality; exact (expression_tagged_graph M values' _ a' b' v' w' u' Hv' Hw' Hu').
  - exact (Ha v v' Hv Hv').
  - exact (Hb w w' Hw Hw').
Qed.

Lemma expression_ns_implication M values values' x y a b a' b' :
  expression_named_substitution M values values' x y a a' ->
  expression_named_substitution M values values' x y b b' ->
  expression_named_substitution M values values' x y (E_wim a b) (E_wim a' b').
Proof.
  intros Ha Hb u u' Hu Hu'.
  destruct (code_relation_total M a values) as [v Hv].
  destruct (code_relation_total M b values) as [w Hw].
  destruct (code_relation_total M a' values') as [v' Hv'].
  destruct (code_relation_total M b' values') as [w' Hw'].
  exact (ns_combine_implication M v w u v' w' u' x y
    (expression_implication_graph M values a b v w u Hv Hw Hu)
    (expression_implication_graph M values' a' b' v' w' u' Hv' Hw' Hu')
    (Ha v v' Hv Hv') (Hb w w' Hw Hw')).
Qed.

Lemma expression_ns_negation M values values' x y a a' :
  x<>zeroM M -> expression_named_substitution M values values' x y a a' ->
  expression_named_substitution M values values' x y (E_wn a) (E_wn a').
Proof. intros Hx Ha. apply expression_ns_implication;[exact Ha|now apply expression_ns_one]. Qed.
Lemma expression_ns_conjunction M values values' x y a b a' b' :
  x<>zeroM M -> expression_named_substitution M values values' x y a a' ->
  expression_named_substitution M values values' x y b b' ->
  expression_named_substitution M values values' x y (E_wa a b) (E_wa a' b').
Proof.
  intros Hx Ha Hb. apply expression_ns_negation;[exact Hx|].
  apply expression_ns_implication;[exact Ha|now apply expression_ns_negation].
Qed.
Lemma expression_ns_disjunction M values values' x y a b a' b' :
  x<>zeroM M -> expression_named_substitution M values values' x y a a' ->
  expression_named_substitution M values values' x y b b' ->
  expression_named_substitution M values values' x y (E_or a b) (E_or a' b').
Proof.
  intros Hx Ha Hb. apply expression_ns_implication;[now apply expression_ns_negation|exact Hb].
Qed.
Lemma expression_ns_universal M values values' x y fresh fresh' a a' k :
  code_relation M values fresh k -> code_relation M values' fresh' k ->
  k<>x -> k<>y -> expression_named_substitution M values values' x y a a' ->
  expression_named_substitution M values values' x y (E_wal fresh a) (E_wal fresh' a').
Proof.
  intros Hk Hk' Hkx Hky Ha u u' Hu Hu'.
  destruct (code_relation_total M a values) as [v Hv].
  destruct (code_relation_total M a' values') as [v' Hv'].
  exact (ns_combine_universal M k v u v' u' x y Hkx Hky
    (expression_universal_graph M values fresh a k v u Hk Hv Hu)
    (expression_universal_graph M values' fresh' a' k v' u' Hk' Hv' Hu')
    (Ha v v' Hv Hv')).
Qed.
Lemma expression_ns_existential M values values' x y fresh fresh' a a' k :
  x<>zeroM M -> code_relation M values fresh k -> code_relation M values' fresh' k ->
  k<>x -> k<>y -> expression_named_substitution M values values' x y a a' ->
  expression_named_substitution M values values' x y (E_wex fresh a) (E_wex fresh' a').
Proof.
  intros Hx Hk Hk' Hkx Hky Ha. apply expression_ns_negation;[exact Hx|].
  apply (expression_ns_universal M values values' x y fresh fresh' (E_wn a) (E_wn a') k Hk Hk' Hkx Hky).
  now apply expression_ns_negation.
Qed.

Lemma template_lt_different M x k : coding_lt M x k -> k<>x.
Proof.
  intros H E. subst k.
  exact (@Peano.lt_neq (carrier M) (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) x x H eq_refl).
Qed.

Theorem template_set_formula_named_substitution M {ff}
  (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) :
  forall env env' fresh fresh' values values' k x y,
  x<>zeroM M -> code_relation M values fresh k -> code_relation M values' fresh' k ->
  coding_lt M x k -> coding_lt M y k ->
  (forall i, expression_named_replace M values values' x y (env i) (env' i)) ->
  expression_named_substitution M values values' x y
    (template_set_formula env fresh phi) (template_set_formula env' fresh' phi).
Proof.
  induction phi as [|fl P ts|fl op a IHa b IHb|fl quant a IHa];
    intros env env' fresh fresh' values values' k x y Hx Hk Hk' Hxl Hyl He;
    cbn [template_set_formula].
  - now apply expression_ns_one.
  - assert (Ht : forall term,expression_named_replace M values values' x y
        (template_term env term) (template_term env' term)).
    { intros [i|f args];[apply He|destruct f]. }
    destruct P.
    + apply (expression_ns_atom M values values' x y false); apply Ht.
    + apply (expression_ns_atom M values values' x y true); apply Ht.
  - destruct op.
    + apply expression_ns_conjunction;[exact Hx|eapply IHa|eapply IHb];eassumption.
    + apply expression_ns_disjunction;[exact Hx|eapply IHa|eapply IHb];eassumption.
    + apply expression_ns_implication;[eapply IHa|eapply IHb];eassumption.
  - assert (He' : forall i, expression_named_replace M values values' x y
        ((fresh .: env) i) ((fresh' .: env') i)).
    { intros [|i];[|apply He]. intros u u' Hu Hu'.
      rewrite (code_relation_functional M fresh values u k Hu Hk),
        (code_relation_functional M fresh' values' u' k Hu' Hk').
      right. split;[now apply template_lt_different|reflexivity]. }
    assert (Hb : expression_named_substitution M values values' x y
      (template_set_formula (fresh .: env) (CEadd fresh (CEconst 1)) a)
      (template_set_formula (fresh' .: env') (CEadd fresh' (CEconst 1)) a)).
    { apply (IHa _ _ _ _ _ _ (succM M k) x y Hx).
      - now apply template_fresh_increment_graph.
      - now apply template_fresh_increment_graph.
      - exact (coding_lt_trans M x k (succM M k) Hxl (coding_lt_succ M k)).
      - exact (coding_lt_trans M y k (succM M k) Hyl (coding_lt_succ M k)).
      - exact He'. }
    destruct quant.
    + eapply expression_ns_universal;[exact Hk|exact Hk'| | |exact Hb];now apply template_lt_different.
    + eapply expression_ns_existential;[exact Hx|exact Hk|exact Hk'| | |exact Hb];now apply template_lt_different.
Qed.

Theorem quotation_atom_named_substitution M equality a b a' b' t k x y v v' :
  x<>zeroM M -> t<>x -> coding_lt M x k -> coding_lt M y k ->
  named_replace M x y a a' -> named_replace M x y b b' ->
  quotation_atom M equality a b t k v -> quotation_atom M equality a' b' t k v' ->
  named_substitution M v x y v'.
Proof.
  intros Hx Ht Hxl Hyl Ha Hb Hv Hv'.
  assert (He : forall i, expression_named_replace M
    (quotation_atom_parameters a b t k (zeroM M))
    (quotation_atom_parameters a' b' t k (zeroM M)) x y
    (quotient_atom_environment i) (quotient_atom_environment i)).
  { intros [|[|i]] u u' Hu Hu';cbn in Hu,Hu';subst u u'.
    - right;auto.
    - exact Ha.
    - exact Hb. }
  destruct equality; eapply (template_set_formula_named_substitution M _
    quotient_atom_environment quotient_atom_environment (CEvar 3) (CEvar 3)
    _ _ k x y Hx eq_refl eq_refl Hxl Hyl He);eassumption.
Qed.
