(** A fixed propositional padding makes a matrix code larger than two
    specified names without changing its K-provable equivalence class.
    No iteration over a model-valued length is needed. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT Pairing
  CodeExpressions CodeDescent CodeTags NumericalProofs NumericalEquivalence
  ProofTemplates TemplateCD TemplatePropositional NamedLeibnizSteps
  NumericalVacuitySteps FreshNames.
From FOL.Tennenbaum Require Import Peano.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.

Definition E_matrix_padding a b m :=
  E_wim (E_wim a a) (E_wim (E_wim b b) (E_wn (E_wn m))).

Lemma matrix_padding_forward G a b m :
  template_proof G (E_wim m (E_matrix_padding a b m)).
Proof.
  unfold E_matrix_padding,E_wn.
  apply template_discharge. do 4 apply template_deduction.
  eapply dmp with (a:=m); apply dhyp; cbn; tauto.
Qed.

Lemma matrix_padding_reverse G a b m :
  template_proof G (E_wim (E_matrix_padding a b m) m).
Proof.
  apply template_discharge,template_deduction.
  eapply dmp with (a:=E_wn (E_wn m));[apply dthm,template_DNE|].
  eapply dmp with (a:=E_wim b b);[|apply dthm,template_I].
  eapply dmp with (a:=E_wim a a);[|apply dthm,template_I].
  apply dhyp. now left.
Qed.

Lemma padding_zero_implication_inputs M a b :
  implication_graph M a b (zeroM M) -> a=zeroM M /\ b=zeroM M.
Proof.
  intro H. apply implication_graph_tagged in H.
  assert (HZ : tagged_pair_graph M 0 (zeroM M) (zeroM M) (zeroM M)).
  { exists (zeroM M). split;[apply pair_zero|].
    rewrite (Arithmetic.mul_comm M (code_numeral M 4) (zeroM M)),
      Arithmetic.mul_zero,Arithmetic.add_zero. reflexivity. }
  destruct (tagged_pair_decode_unique M 0 0 a b (zeroM M) (zeroM M)
    (zeroM M) ltac:(lia) ltac:(lia) H HZ) as [_ Hinputs]. exact Hinputs.
Qed.

Lemma padding_implication_nonzero M a b f :
  b<>zeroM M -> implication_graph M a b f -> f<>zeroM M.
Proof.
  intros HB H E. subst f.
  exact (HB (proj2 (padding_zero_implication_inputs M a b H))).
Qed.

Lemma padding_reflexive_below M a aa c :
  implication_graph M a a aa -> coding_lt M aa c -> coding_lt M a c.
Proof.
  intros H Hlt.
  destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) aa (zeroM M)) as [E|E].
  - subst aa. destruct (padding_zero_implication_inputs M a a H) as [-> _]. exact Hlt.
  - exact (coding_lt_trans M a aa c
      (proj1 (tagged_pair_zero_descent M a a aa E (proj1 (implication_graph_tagged M a a aa) H))) Hlt).
Qed.

Definition matrix_padding M a b m c :=
  code_relation M (a .: b .: m .: fun _=>zeroM M)
    (E_matrix_padding (CEvar 0) (CEvar 1) (CEvar 2)) c.

Theorem matrix_padding_equivalent M a b m c :
  matrix_padding M a b m c -> numerical_equivalent M m c.
Proof.
  intro HC. apply (proj1 (numerical_equivalent_expression M
    (a .: b .: m .: fun _=>zeroM M) (CEvar 2)
    (E_matrix_padding (CEvar 0) (CEvar 1) (CEvar 2)) m c eq_refl HC)).
  split;apply ns_proof_template.
  - apply matrix_padding_forward.
  - apply matrix_padding_reverse.
Qed.

Theorem matrix_padding_bounds M a b m c :
  matrix_padding M a b m c ->
  coding_lt M a c /\ coding_lt M b c /\ coding_lt M m c.
Proof.
  intro HC. set (env:=a .: b .: m .: fun _=>zeroM M).
  destruct (code_relation_total M (E_wim (CEvar 0) (CEvar 0)) env) as [aa HAA].
  destruct (code_relation_total M (E_wim (CEvar 1) (CEvar 1)) env) as [bb HBB].
  destruct (code_relation_total M (E_wn (CEvar 2)) env) as [nm HNM].
  destruct (code_relation_total M (E_wn (E_wn (CEvar 2))) env) as [nnm HNNM].
  destruct (code_relation_total M
    (E_wim (E_wim (CEvar 1) (CEvar 1)) (E_wn (E_wn (CEvar 2)))) env) as [tail HT].
  assert (HA : implication_graph M a a aa).
  { exact (proj1 (expression_implication_iff M env (CEvar 0) (CEvar 0) a a aa eq_refl eq_refl) HAA). }
  assert (HB : implication_graph M b b bb).
  { exact (proj1 (expression_implication_iff M env (CEvar 1) (CEvar 1) b b bb eq_refl eq_refl) HBB). }
  assert (HN : implication_graph M m (code_numeral M 1) nm).
  { exact (proj1 (expression_implication_iff M env (CEvar 2) (CEconst 1)
      m (code_numeral M 1) nm eq_refl eq_refl) HNM). }
  assert (HNN : implication_graph M nm (code_numeral M 1) nnm).
  { exact (proj1 (expression_implication_iff M env (E_wn (CEvar 2)) (CEconst 1)
      nm (code_numeral M 1) nnm HNM eq_refl) HNNM). }
  assert (HTail : implication_graph M bb nnm tail).
  { exact (proj1 (expression_implication_iff M env
      (E_wim (CEvar 1) (CEvar 1)) (E_wn (E_wn (CEvar 2))) bb nnm tail HBB HNNM) HT). }
  assert (HRoot : implication_graph M aa tail c).
  { exact (proj1 (expression_implication_iff M env
      (E_wim (CEvar 0) (CEvar 0))
      (E_wim (E_wim (CEvar 1) (CEvar 1)) (E_wn (E_wn (CEvar 2)))) aa tail c HAA HT) HC). }
  assert (HOne : code_numeral M 1 <> zeroM M).
  { intro E. apply (zero_ne_succ M (zeroM M)). symmetry. exact E. }
  assert (Hnm : nm<>zeroM M) by exact (padding_implication_nonzero M m _ nm HOne HN).
  assert (Hnnm : nnm<>zeroM M) by exact (padding_implication_nonzero M nm _ nnm HOne HNN).
  assert (Htail : tail<>zeroM M) by exact (padding_implication_nonzero M bb nnm tail Hnnm HTail).
  assert (Hc : c<>zeroM M) by exact (padding_implication_nonzero M aa tail c Htail HRoot).
  pose proof (tagged_pair_zero_descent M aa tail c Hc
    (proj1 (implication_graph_tagged M aa tail c) HRoot)) as [Haac Htailc].
  pose proof (tagged_pair_zero_descent M bb nnm tail Htail
    (proj1 (implication_graph_tagged M bb nnm tail) HTail)) as [Hbbtail Hnnmtail].
  split;[exact (padding_reflexive_below M a aa c HA Haac)|]. split.
  - exact (coding_lt_trans M b tail c (padding_reflexive_below M b bb tail HB Hbbtail) Htailc).
  - pose proof (proj1 (tagged_pair_zero_descent M m (code_numeral M 1) nm Hnm
      (proj1 (implication_graph_tagged M m (code_numeral M 1) nm) HN))) as Hmnm.
    pose proof (proj1 (tagged_pair_zero_descent M nm (code_numeral M 1) nnm Hnnm
      (proj1 (implication_graph_tagged M nm (code_numeral M 1) nnm) HNN))) as Hnmnnm.
    exact (coding_lt_trans M m tail c
      (coding_lt_trans M m nnm tail (coding_lt_trans M m nm nnm Hmnm Hnmnnm) Hnnmtail) Htailc).
Qed.

Theorem numerical_matrix_padding M a b m :
  exists c, numerical_equivalent M m c /\
    coding_lt M a c /\ coding_lt M b c /\ coding_lt M m c /\ formula_fresh M m c.
Proof.
  destruct (code_relation_total M
    (E_matrix_padding (CEvar 0) (CEvar 1) (CEvar 2))
    (a .: b .: m .: fun _=>zeroM M)) as [c HC].
  destruct (matrix_padding_bounds M a b m c HC) as [HA [HB HM]].
  exists c. split;[exact (matrix_padding_equivalent M a b m c HC)|].
  split;[exact HA|]. split;[exact HB|]. split;[exact HM|].
  exact (formula_above_is_fresh M m c HM).
Qed.

Print Assumptions matrix_padding_equivalent.
Print Assumptions matrix_padding_bounds.
Print Assumptions numerical_matrix_padding.
