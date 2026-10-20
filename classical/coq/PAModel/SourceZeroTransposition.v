(** An actual internally coded transposition of0 and an arbitrary PA-model
    variable name. Its prefix length may be nonstandard. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  BetaPacking NumericalProofs NumericalEnvironments NumericalRenamingMaps.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition source_zero_transposition_index M x i v :=
  (i = zeroM M /\ v = x) \/ (i = x /\ v = zeroM M) \/ (i <> zeroM M /\ i <> x /\ v = i).
Definition source_zero_transposition_index_formula (x i v:term):form :=
  ((i == zero) ∧ (v == x)) ∨ (((i == x) ∧ (v == zero)) ∨
    ((i == zero → ⊥) ∧ ((i == x → ⊥) ∧ (v == i)))).
Lemma source_zero_transposition_index_correct M rho x i v :
  holds M rho(source_zero_transposition_index_formula x i v) <->
  source_zero_transposition_index M(evalM M rho x)(evalM M rho i)(evalM M rho v).
Proof. reflexivity. Qed.

Definition source_zero_transposition M x b c :=forall i v,
  renaming_lookup M b c(succM M x)(zeroM M) i v <->source_zero_transposition_index M x i v.

Lemma source_zero_transposition_index_total M x i :exists v,source_zero_transposition_index M x i v.
Proof.
  destruct(@Peano.D_eq_dec(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H) i(zeroM M)) as[E|H0].
  - exists x. left. auto.
  - destruct(@Peano.D_eq_dec(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H) i x) as[E|HX].
    + exists(zeroM M). right;left. auto.
    + exists i. right;right. auto.
Qed.
Lemma source_zero_transposition_index_functional M x i v w :
  source_zero_transposition_index M x i v ->source_zero_transposition_index M x i w ->v=w.
Proof.
  unfold source_zero_transposition_index.
  intros [[H E]|[[H E]|[H0[HX E]]]] [[H' E']|[[H' E']|[H0'[HX' E']]]];congruence.
Qed.
Lemma source_zero_transposition_index_symmetric M x i v :
  source_zero_transposition_index M x i v ->source_zero_transposition_index M x v i.
Proof.
  intros [[-> ->]|[[-> ->]|[H0[HX ->]]]].
  - right;left. auto.
  - left. auto.
  - right;right. auto.
Qed.

Theorem source_zero_transposition_total M x :exists b c,source_zero_transposition M x b c.
Proof.
  set(rho:=x .:fun _=>zeroM M). set(F:=source_zero_transposition_index_formula $2 $1 $0).
  assert(HT:forall i,coding_lt M i(succM M x) ->exists v,holds M(v .:i .:rho) F).
  { intros i _. exact(source_zero_transposition_index_total M x i). }
  assert(HB:forall i v,coding_lt M i(succM M x) ->holds M(v .:i .:rho) F ->coding_lt M v(succM M x)).
  { intros i v Hi [[_ ->]|[[_ ->]|[_[_ ->]]]];[apply coding_lt_succ|apply coding_zero_lt_succ|exact Hi]. }
  assert(HU:forall i v w,coding_lt M i(succM M x) ->
    holds M(v .:i .:rho) F ->holds M(w .:i .:rho) F ->v=w).
  { intros i v w _ HV HW. exact(source_zero_transposition_index_functional M x i v w HV HW). }
  destruct(beta_pack_function M rho F(succM M x) x HT HB HU) as(b&c&Hbc).
  exists b,c. intros i v. split.
  - intros[[Hi HV]|[Hi HV]].
    + exact(proj1(Hbc i v Hi) HV).
    + right;right. split.
      * intro E. subst i. exact(Hi(coding_zero_lt_succ M x)).
      * split;[intro E;subst i;exact(Hi(coding_lt_succ M x))|]. now rewrite coding_add_zero_r in HV.
  - intro H. destruct(environment_lt_cases M i(succM M x)) as[Hi|Hi].
    + left. split;[exact Hi|exact(proj2(Hbc i v Hi) H)].
    + right. split;[exact Hi|]. destruct H as[[E _]|[[E _]|[_[_ E]]]].
      * subst i. contradiction(Hi(coding_zero_lt_succ M x)).
      * subst i. contradiction(Hi(coding_lt_succ M x)).
      * rewrite E. symmetry. apply coding_add_zero_r.
Qed.

Theorem source_zero_transposition_zero M x b c :source_zero_transposition M x b c ->
  renaming_lookup M b c(succM M x)(zeroM M)(zeroM M) x.
Proof. intro H. apply H. left. auto. Qed.
Theorem source_zero_transposition_name M x b c :source_zero_transposition M x b c ->
  renaming_lookup M b c(succM M x)(zeroM M) x(zeroM M).
Proof. intro H. apply H. right;left. auto. Qed.
Theorem source_zero_transposition_other M x b c i :source_zero_transposition M x b c ->
  i<>zeroM M ->i<>x ->renaming_lookup M b c(succM M x)(zeroM M) i i.
Proof. intros H H0 HX. apply H. right;right. auto. Qed.

Print Assumptions source_zero_transposition_total.
Print Assumptions source_zero_transposition_index_symmetric.
Print Assumptions source_zero_transposition_zero.
Print Assumptions source_zero_transposition_name.
Print Assumptions source_zero_transposition_other.
