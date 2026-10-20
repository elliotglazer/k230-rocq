(** Internally finite collection and witness selection in every PA model.
    The relation is an ordinary PA formula, with value/index in slots 0/1
    and arbitrary fixed parameters thereafter. No functionality assumption
    on that relation, or external induction on a model length, is used. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  FiniteCRTFormula BetaExtension.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Definition collection_total M theta rho n :=
  forall i,coding_lt M i n -> exists y,holds M (y .: i .: rho) theta.
Definition collection_table M theta rho n b c :=
  forall i y,coding_lt M i n -> beta M b c i y -> holds M (y .: i .: rho) theta.

Definition collection_skip_parameters (count : nat) theta :=
  theta[($0 .: $1 .: fun i => var (2+count+i))].

Lemma collection_skip_parameters_correct M theta rho count params y i :
  (forall j,params (2+count+j)=rho j) -> params 0=y -> params 1=i ->
  (holds M params (collection_skip_parameters count theta) <-> holds M (y .: i .: rho) theta).
Proof.
  intros Htail Hzero Hone. unfold collection_skip_parameters,holds.
  rewrite sat_comp. apply sat_ext. intros [|[|j]];cbn;auto. exact (Htail j).
Qed.

Definition collection_total_formula theta : form :=
  ∀ (Peano.sless $0 $1 → ∃ collection_skip_parameters 1 theta).
Definition collection_table_exists_formula theta : form :=
  ∃∃∀∀ (Peano.sless $1 $4 → beta_formula $3 $2 $1 $0 → collection_skip_parameters 3 theta).
Definition collection_induction_formula theta : form :=
  collection_total_formula theta → collection_table_exists_formula theta.

Local Opaque holds Peano.sless beta_formula collection_skip_parameters.
Lemma collection_total_formula_correct M theta rho n :
  holds M (n .: rho) (collection_total_formula theta) <-> collection_total M theta rho n.
Proof.
  unfold collection_total_formula,collection_total.
  setoid_rewrite holds_forall. setoid_rewrite holds_imp. setoid_rewrite holds_sless.
  setoid_rewrite holds_exists.
  split;intros H i Hi.
  - destruct (H i Hi) as [y Hy]. exists y.
    apply (proj1 (collection_skip_parameters_correct M theta rho 1
      (y .: i .: n .: rho) y i ltac:(reflexivity) eq_refl eq_refl)). exact Hy.
  - destruct (H i Hi) as [y Hy]. exists y.
    apply (proj2 (collection_skip_parameters_correct M theta rho 1
      (y .: i .: n .: rho) y i ltac:(reflexivity) eq_refl eq_refl)). exact Hy.
Qed.

Lemma collection_table_exists_formula_correct M theta rho n :
  holds M (n .: rho) (collection_table_exists_formula theta) <->
  exists b c,collection_table M theta rho n b c.
Proof.
  unfold collection_table_exists_formula,collection_table.
  repeat setoid_rewrite holds_exists. repeat setoid_rewrite holds_forall.
  repeat setoid_rewrite holds_imp. setoid_rewrite holds_sless.
  setoid_rewrite beta_formula_correct.
  split;intros [b [c H]];exists b,c;intros i y Hi Hy.
  - apply (proj1 (collection_skip_parameters_correct M theta rho 3
      (y .: i .: c .: b .: n .: rho) y i ltac:(reflexivity) eq_refl eq_refl)).
    exact (H i y Hi Hy).
  - apply (proj2 (collection_skip_parameters_correct M theta rho 3
      (y .: i .: c .: b .: n .: rho) y i ltac:(reflexivity) eq_refl eq_refl)).
    exact (H i y Hi Hy).
Qed.

Lemma collection_induction_definable M theta rho :
  Definable1 M (fun n => collection_total M theta rho n -> exists b c,collection_table M theta rho n b c).
Proof.
  exists (collection_induction_formula theta),rho. intro n.
  unfold collection_induction_formula. rewrite holds_imp,
    collection_total_formula_correct,collection_table_exists_formula_correct. reflexivity.
Qed.

Theorem bounded_collection_table M theta rho n :
  collection_total M theta rho n -> exists b c,collection_table M theta rho n b c.
Proof.
  revert n. apply (definable_induction M
    (fun n => collection_total M theta rho n -> exists b c,collection_table M theta rho n b c)
    (collection_induction_definable M theta rho)).
  - intros _. exists (zeroM M),(zeroM M). intros i y Hi _.
    exfalso. exact (coding_not_lt_zero M i Hi).
  - intros n IH Htotal.
    assert (Hprevious : collection_total M theta rho n).
    { intros i Hi. apply Htotal. apply coding_lt_succ_cases;now left. }
    destruct (IH Hprevious) as [b [c Htable]].
    destruct (Htotal n (coding_lt_succ M n)) as [y Hy].
    destruct (beta_extension M b c n y) as [b' [c' [Hprefix Hlast]]].
    exists b',c'. intros i z Hi Hz.
    destruct (proj1 (coding_lt_succ_cases M i n) Hi) as [Hlt|E].
    + destruct (beta_total M b c i) as [w Hw].
      pose proof (Hprefix i w Hlt Hw) as Hw'.
      assert (E : z=w) by (eapply beta_unique;eassumption). subst z.
      exact (Htable i w Hlt Hw).
    + subst i. assert (E : z=y) by (eapply beta_unique;eassumption). now subst z.
Qed.

Theorem bounded_collection_witnesses M theta rho n :
  (forall i,coding_lt M i n -> exists y,holds M (y .: i .: rho) theta) ->
  exists b c bound,
    (forall i y,coding_lt M i n -> beta M b c i y ->
      coding_lt M y bound /\ holds M (y .: i .: rho) theta) /\
    (forall i,coding_lt M i n -> exists y,beta M b c i y /\
      coding_lt M y bound /\ holds M (y .: i .: rho) theta).
Proof.
  intro H. destruct (bounded_collection_table M theta rho n H) as [b [c Htable]].
  exists b,c,(succM M b).
  assert (Hentry : forall i y,coding_lt M i n -> beta M b c i y ->
    coding_lt M y (succM M b) /\ holds M (y .: i .: rho) theta).
  { intros i y Hi Hy. split.
    - exact (remainder_le_dividend M b (beta_modulus M c i) y Hy).
    - exact (Htable i y Hi Hy). }
  split;[exact Hentry|]. intros i Hi. destruct (beta_total M b c i) as [y Hy].
  exists y. split;[exact Hy|exact (Hentry i y Hi Hy)].
Qed.

Corollary bounded_collection M theta rho n :
  (forall i,coding_lt M i n -> exists y,holds M (y .: i .: rho) theta) ->
  exists bound,forall i,coding_lt M i n ->
    exists y,coding_lt M y bound /\ holds M (y .: i .: rho) theta.
Proof.
  intro H. destruct (bounded_collection_witnesses M theta rho n H) as [b [c [bound [_ Htable]]]].
  exists bound. intros i Hi. destruct (Htable i Hi) as [y [_ Hy]]. now exists y.
Qed.
