(** The arbitrary internal tagged matrix has a genuine numerical KP0
    instance with its prescribed pair seed. This does not yet finish the
    existential-witness assembly for tagged comprehension. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions CodeDescent
  CodeTags NumericalProofs NumericalEquality NamedLeibnizSteps ProofTemplates QuotientAtomTemplates FreshNames FreshPropagation
  NamedBinderFresh TemplateBinderFresh NumericalMatrixPadding
  NumericalSingleton NumericalTaggedComprehension NumericalFixedSeed
  KP0SeedSpecialization NamedSubstitution.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Lemma mentions_implication_left M a b f name :
  implication_graph M a b f -> formula_mentions M a name -> formula_mentions M f name.
Proof.
  intros Hf Ha. apply (formula_mentions_step M f a name);[|exact Ha].
  exists a,b. left. split.
  - intro E. subst f. destruct (padding_zero_implication_inputs M a b Hf) as [E _].
    subst a. exact (coding_not_lt_zero M name (formula_mentions_bounded M (zeroM M) name Ha)).
  - split;[now apply implication_graph_tagged|now left].
Qed.

Lemma mentions_implication_right M a b f name :
  implication_graph M a b f -> formula_mentions M b name -> formula_mentions M f name.
Proof.
  intros Hf Hb. apply (formula_mentions_step M f b name);[|exact Hb].
  exists a,b. left. split.
  - intro E. subst f. destruct (padding_zero_implication_inputs M a b Hf) as [_ E].
    subst b. exact (coding_not_lt_zero M name (formula_mentions_bounded M (zeroM M) name Hb)).
  - split;[now apply implication_graph_tagged|now right].
Qed.

Definition expression_mentions M rho name e :=
  forall f,code_relation M rho e f -> formula_mentions M f name.

Lemma expression_mentions_implication_left M rho name A B :
  expression_mentions M rho name A -> expression_mentions M rho name (E_wim A B).
Proof.
  intros HA f Hf. destruct (code_relation_total M A rho) as [a Ha].
  destruct (code_relation_total M B rho) as [b Hb].
  exact (mentions_implication_left M a b f name
    (expression_implication_graph M rho A B a b f Ha Hb Hf) (HA a Ha)).
Qed.
Lemma expression_mentions_implication_right M rho name A B :
  expression_mentions M rho name B -> expression_mentions M rho name (E_wim A B).
Proof.
  intros HB f Hf. destruct (code_relation_total M A rho) as [a Ha].
  destruct (code_relation_total M B rho) as [b Hb].
  exact (mentions_implication_right M a b f name
    (expression_implication_graph M rho A B a b f Ha Hb Hf) (HB b Hb)).
Qed.
Lemma expression_mentions_conjunction_left M rho name A B :
  expression_mentions M rho name A -> expression_mentions M rho name (E_wa A B).
Proof.
  intro HA. unfold E_wa,E_wn. apply expression_mentions_implication_left.
  apply expression_mentions_implication_left. exact HA.
Qed.
Lemma expression_mentions_disjunction_left M rho name A B :
  expression_mentions M rho name A -> expression_mentions M rho name (E_or A B).
Proof.
  intro HA. unfold E_or,E_wn. apply expression_mentions_implication_left.
  apply expression_mentions_implication_left. exact HA.
Qed.
Lemma expression_mentions_equality_right M rho A B a b :
  code_relation M rho A a -> code_relation M rho B b -> expression_mentions M rho b (E_weq A B).
Proof.
  intros HA HB f Hf. apply formula_node_is_mentioned.
  exists a,b. left. split;[right|now right].
  exact (proj1 (expression_equality_graph M rho A B a b f HA HB) Hf).
Qed.

Definition E_tagged_matrix y input carrier marker root theta z :=
  E_tagged_choices y input carrier marker root theta (E_raw_singleton y input z).

Lemma tagged_matrix_mentions_root M rho y input carrier marker root theta z r :
  code_relation M rho root r -> expression_mentions M rho r
    (E_tagged_matrix y input carrier marker root theta z).
Proof.
  intro HR. unfold E_tagged_matrix,E_tagged_choices.
  apply expression_mentions_disjunction_left,expression_mentions_conjunction_left.
  destruct (code_relation_total M input rho) as [a HA].
  exact (expression_mentions_equality_right M rho input root a r HA HR).
Qed.

Lemma tagged_matrix_binder_absent M rho name y input carrier marker root theta z zv :
  code_relation M rho z zv -> zv<>name -> expression_binder_absent M rho name theta ->
  expression_binder_absent M rho name
    (E_tagged_matrix y input carrier marker root theta z).
Proof.
  intros HZ HZN HTheta. apply tagged_choices_binder_absent;[exact HTheta|].
  unfold E_raw_singleton. apply expression_binder_absent_conjunction.
  - apply expression_binder_absent_atom;now left.
  - apply expression_binder_absent_universal.
    + intros v Hv. now rewrite (code_relation_functional M z rho v zv Hv HZ).
    + apply expression_binder_absent_implication;apply expression_binder_absent_atom;auto.
Qed.

Definition tagged_matrix_parameters M input y carrier marker root theta z :=
  input .: y .: carrier .: marker .: root .: theta .: z .: fun _=>zeroM M.

Theorem numerical_tagged_matrix_instance M input y carrier marker root theta z m :
  input<>zeroM M -> y<>input -> input<>root -> y<>root -> z<>input -> z<>root ->
  named_binder_absent M theta input -> named_binder_absent M theta root ->
  code_relation M (tagged_matrix_parameters M input y carrier marker root theta z)
    (E_tagged_matrix (CEvar 1) (CEvar 0) (CEvar 2) (CEvar 3)
      (CEvar 4) (CEvar 5) (CEvar 6)) m ->
  exists k p mp f,
    k<>input /\ k<>y /\ k<>root /\ input<>p /\ y<>p /\ k<>p /\ p<>root /\
    p<>zeroM M /\ formula_fresh M m k /\ formula_fresh M m p /\
    named_substitution M m input p mp /\
    code_relation M (kp0_seed_parameters M input y k p m mp root)
      (E_kp_with_seed (CEvar 6) (CEvar 0) (CEvar 1) (CEvar 2)
        (CEvar 3) (CEvar 4) (CEvar 5)) f /\ numerically_provable M f.
Proof.
  intros H0 HYI HIR HYR HZI HZR HTI HTR HM.
  set (rho:=tagged_matrix_parameters M input y carrier marker root theta z).
  apply (numerical_uniform_kp0_fixed_seed M input y m root H0 HYI HIR HYR).
  - exact (tagged_matrix_binder_absent M rho input (CEvar 1) (CEvar 0) (CEvar 2)
      (CEvar 3) (CEvar 4) (CEvar 5) (CEvar 6) z eq_refl HZI
      ltac:(intros v Hv;change (v=theta) in Hv;now subst v) m HM).
  - exact (tagged_matrix_binder_absent M rho root (CEvar 1) (CEvar 0) (CEvar 2)
      (CEvar 3) (CEvar 4) (CEvar 5) (CEvar 6) z eq_refl HZR
      ltac:(intros v Hv;change (v=theta) in Hv;now subst v) m HM).
  - exact (tagged_matrix_mentions_root M rho (CEvar 1) (CEvar 0) (CEvar 2)
      (CEvar 3) (CEvar 4) (CEvar 5) (CEvar 6) root eq_refl m HM).
Qed.

Print Assumptions tagged_matrix_mentions_root.
Print Assumptions tagged_matrix_binder_absent.
Print Assumptions numerical_tagged_matrix_instance.
