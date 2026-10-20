(** A concrete arithmetic syntax transformation. Implication is mapped
    homomorphically; zero, atoms and universal quantification use fixed
    code-expression templates. This includes the shape of the quotient map.
    No totality or correctness of a recursive syntax map is assumed. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  FiniteCRTFormula Pairing CodeExpressions NumericalProofs ProofClosure
  CodeDescent CodeTags InternalRecursion.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Record SyntaxFoldSpec := {
  fold_zero : code_expr;
  fold_member : code_expr;
  fold_equal : code_expr;
  fold_universal : code_expr
}.

Definition fold_parameters {D} (a b : D) (rho : nat -> D) i :=
  match i with 0 => a | 1 => b | S (S k) => rho k end.

Definition fold_step M spec rho b c n v :=
  (n=zeroM M /\ code_relation M rho (fold_zero spec) v) \/
  (n<>zeroM M /\
    ((exists a d, tagged_pair_graph M 1 a d n /\
       code_relation M (fold_parameters a d rho) (fold_member spec) v) \/
     (exists a d, tagged_pair_graph M 3 a d n /\
       code_relation M (fold_parameters a d rho) (fold_equal spec) v) \/
     (exists a d a' d', tagged_pair_graph M 0 a d n /\
       beta M b c a a' /\ beta M b c d d' /\ implication_graph M a' d' v) \/
     (exists a d d', tagged_pair_graph M 2 a d n /\
       beta M b c d d' /\
       code_relation M (fold_parameters a d' rho) (fold_universal spec) v))).

Definition fold_atom_terms i : term :=
  match i with 0 => $1 | 1 => $0 | S (S k) => var (6+k) end.
Definition fold_all_terms i : term :=
  match i with 0 => $2 | 1 => $0 | S (S k) => var (7+k) end.

Definition fold_atom_formula tag expr : form :=
  ∃∃ (tagged_pair_formula tag $1 $0 $3 ∧ code_formula expr fold_atom_terms $2).
Definition fold_imp_formula : form :=
  ∃∃∃∃ (tagged_pair_formula 0 $3 $2 $5 ∧
    beta_formula $7 $6 $3 $1 ∧ beta_formula $7 $6 $2 $0 ∧
    implication_formula $1 $0 $4).
Definition fold_all_formula expr : form :=
  ∃∃∃ (tagged_pair_formula 2 $2 $1 $4 ∧ beta_formula $6 $5 $1 $0 ∧
    code_formula expr fold_all_terms $3).
Definition fold_step_formula spec : form :=
  (($1 == zero) ∧ code_formula (fold_zero spec) (fun i => var (4+i)) $0) ∨
  ((¬($1 == zero)) ∧
    (fold_atom_formula 1 (fold_member spec) ∨
     fold_atom_formula 3 (fold_equal spec) ∨ fold_imp_formula ∨
     fold_all_formula (fold_universal spec))).

Lemma fold_zero_formula_correct M rho expr b c n v :
  holds M (v .: n .: c .: b .: rho)
    (code_formula expr (fun i => var (4+i)) $0) <-> code_relation M rho expr v.
Proof. rewrite code_formula_correct. apply code_relation_ext. intro i. reflexivity. Qed.

Lemma fold_atom_code_correct M rho expr a d b c n v :
  holds M (d .: a .: v .: n .: c .: b .: rho)
    (code_formula expr fold_atom_terms $2) <->
  code_relation M (fold_parameters a d rho) expr v.
Proof.
  rewrite code_formula_correct. apply code_relation_ext.
  intros [|[|i]]; reflexivity.
Qed.

Lemma fold_all_code_correct M rho expr a d d' b c n v :
  holds M (d' .: d .: a .: v .: n .: c .: b .: rho)
    (code_formula expr fold_all_terms $3) <->
  code_relation M (fold_parameters a d' rho) expr v.
Proof.
  rewrite code_formula_correct. apply code_relation_ext.
  intros [|[|i]]; reflexivity.
Qed.

Local Opaque holds code_formula tagged_pair_formula beta_formula implication_formula.

Lemma fold_atom_formula_correct M rho tag expr b c n v :
  holds M (v .: n .: c .: b .: rho) (fold_atom_formula tag expr) <->
  exists a d, tagged_pair_graph M tag a d n /\
    code_relation M (fold_parameters a d rho) expr v.
Proof.
  unfold fold_atom_formula. repeat setoid_rewrite holds_ex.
  setoid_rewrite holds_and. setoid_rewrite tagged_pair_formula_correct.
  setoid_rewrite fold_atom_code_correct. reflexivity.
Qed.

Lemma fold_imp_formula_correct M rho b c n v :
  holds M (v .: n .: c .: b .: rho) fold_imp_formula <->
  exists a d a' d', tagged_pair_graph M 0 a d n /\
    beta M b c a a' /\ beta M b c d d' /\ implication_graph M a' d' v.
Proof.
  unfold fold_imp_formula. repeat setoid_rewrite holds_ex.
  repeat setoid_rewrite holds_and. setoid_rewrite tagged_pair_formula_correct.
  setoid_rewrite beta_formula_correct. setoid_rewrite implication_formula_correct.
  split; intros [a [d [a' [d' H]]]]; exists a,d,a',d'; tauto.
Qed.

Lemma fold_all_formula_correct M rho expr b c n v :
  holds M (v .: n .: c .: b .: rho) (fold_all_formula expr) <->
  exists a d d', tagged_pair_graph M 2 a d n /\ beta M b c d d' /\
    code_relation M (fold_parameters a d' rho) expr v.
Proof.
  unfold fold_all_formula. repeat setoid_rewrite holds_ex.
  repeat setoid_rewrite holds_and. setoid_rewrite tagged_pair_formula_correct.
  setoid_rewrite beta_formula_correct. setoid_rewrite fold_all_code_correct.
  split; intros [a [d [d' H]]]; exists a,d,d'; tauto.
Qed.

Local Opaque fold_atom_formula fold_imp_formula fold_all_formula.

Lemma fold_step_formula_correct M spec rho b c n v :
  recursion_step M (fold_step_formula spec) rho b c n v <->
  fold_step M spec rho b c n v.
Proof.
  unfold recursion_step,fold_step_formula,fold_step.
  repeat setoid_rewrite holds_or. repeat setoid_rewrite holds_and.
  repeat setoid_rewrite holds_or.
  rewrite fold_zero_formula_correct.
  rewrite !fold_atom_formula_correct,fold_imp_formula_correct,fold_all_formula_correct.
  tauto.
Qed.

Theorem fold_step_total M spec rho b c n : exists v, fold_step M spec rho b c n v.
Proof.
  destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
    (fun ax H axrho => axioms M ax axrho H) n (zeroM M)) as [Hz|Hnz].
  - destruct (code_relation_total M (fold_zero spec) rho) as [v Hv].
    exists v. left. auto.
  - destruct (formula_code_cases M n) as
      [[a [d H]]|[[a [d H]]|[[a [d H]]|[a [d H]]]]].
    + destruct (beta_total M b c a) as [a' Ha].
      destruct (beta_total M b c d) as [d' Hd].
      destruct (tagged_pair_total M 0 a' d') as [v Hv].
      exists v. right. split; [exact Hnz|]. right; right; left.
      exists a,d,a',d'. split; [exact H|]. split; [exact Ha|]. split; [exact Hd|].
      exact (proj2 (implication_graph_tagged M a' d' v) Hv).
    + destruct (code_relation_total M (fold_member spec) (fold_parameters a d rho)) as [v Hv].
      exists v. right. split; [exact Hnz|]. left. exists a,d. auto.
    + destruct (beta_total M b c d) as [d' Hd].
      destruct (code_relation_total M (fold_universal spec) (fold_parameters a d' rho)) as [v Hv].
      exists v. right. split; [exact Hnz|]. right; right; right. exists a,d,d'. auto.
    + destruct (code_relation_total M (fold_equal spec) (fold_parameters a d rho)) as [v Hv].
      exists v. right. split; [exact Hnz|]. right; left. exists a,d. auto.
Qed.

Definition fold_payload M spec rho b c tag a d v :=
  match tag with
  | 0 => exists a' d', beta M b c a a' /\ beta M b c d d' /\ implication_graph M a' d' v
  | 1 => code_relation M (fold_parameters a d rho) (fold_member spec) v
  | 2 => exists d', beta M b c d d' /\
      code_relation M (fold_parameters a d' rho) (fold_universal spec) v
  | 3 => code_relation M (fold_parameters a d rho) (fold_equal spec) v
  | _ => False
  end.

Lemma fold_step_decode M spec rho b c n v : n<>zeroM M ->
  (fold_step M spec rho b c n v <-> exists tag a d,
    tag<4 /\ tagged_pair_graph M tag a d n /\ fold_payload M spec rho b c tag a d v).
Proof.
  intro Hnz. split.
  - intros [[Hz _]|[_ [Ha|[Ha|[Ha|Ha]]]]]; [contradiction| | | |].
    + destruct Ha as [a [d [Htag Hpay]]]. exists 1,a,d. split; [lia|auto].
    + destruct Ha as [a [d [Htag Hpay]]]. exists 3,a,d. split; [lia|auto].
    + destruct Ha as [a [d [a' [d' [Htag Hpay]]]]].
      exists 0,a,d. split; [lia|]. split; [exact Htag|]. now exists a',d'.
    + destruct Ha as [a [d [d' [Htag Hpay]]]].
      exists 2,a,d. split; [lia|]. split; [exact Htag|]. now exists d'.
  - intros [tag [a [d [Hlt [Htag Hpay]]]]]. right. split; [exact Hnz|].
    destruct tag as [|[|[|[|tag]]]]; try lia.
    + right; right; left. destruct Hpay as [a' [d' Hpay]]. now exists a,d,a',d'.
    + left. now exists a,d.
    + right; right; right. destruct Hpay as [d' Hpay]. now exists a,d,d'.
    + right; left. now exists a,d.
Qed.

Lemma fold_payload_functional M spec rho b c tag a d v w :
  fold_payload M spec rho b c tag a d v ->
  fold_payload M spec rho b c tag a d w -> v=w.
Proof.
  destruct tag as [|[|[|[|tag]]]]; cbn [fold_payload].
  - intros [a' [d' [Ha [Hd Hv]]]] [a'' [d'' [Ha' [Hd' Hw]]]].
    assert (a'=a'') by (eapply beta_unique; eassumption).
    assert (d'=d'') by (eapply beta_unique; eassumption). subst a'' d''.
    unfold implication_graph in Hv,Hw. eapply code_relation_functional; eassumption.
  - intros Hv Hw. eapply code_relation_functional; eassumption.
  - intros [d' [Hd Hv]] [d'' [Hd' Hw]].
    assert (d'=d'') by (eapply beta_unique; eassumption). subst d''.
    eapply code_relation_functional; eassumption.
  - intros Hv Hw. eapply code_relation_functional; eassumption.
  - contradiction.
Qed.

Theorem fold_step_functional M spec rho b c n v w :
  fold_step M spec rho b c n v -> fold_step M spec rho b c n w -> v=w.
Proof.
  intros H H'.
  destruct H as [[Hz Hv]|[Hnz Hpay]].
  - destruct H' as [[_ Hw]|[Hnz _]]; [|contradiction].
    exact (code_relation_functional M (fold_zero spec) rho v w Hv Hw).
  - assert (H : fold_step M spec rho b c n v) by (right;auto).
    apply (proj1 (fold_step_decode M spec rho b c n v Hnz)) in H.
    apply (proj1 (fold_step_decode M spec rho b c n w Hnz)) in H'.
    destruct H as [tag [a [d [Ht [Htag Hv]]]]].
    destruct H' as [tag' [a' [d' [Ht' [Htag' Hw]]]]].
    destruct (tagged_pair_decode_unique M tag tag' a d a' d' n Ht Ht' Htag Htag')
      as [Et [Ea Ed]]. subst tag' a' d'.
    exact (fold_payload_functional M spec rho b c tag a d v w Hv Hw).
Qed.

Lemma fold_payload_prefix M spec rho b c b' c' n tag a d v :
  n<>zeroM M -> tag<4 -> tagged_pair_graph M tag a d n ->
  prefix M b c b' c' n -> fold_payload M spec rho b c tag a d v ->
  fold_payload M spec rho b' c' tag a d v.
Proof.
  intros Hnz Hlt Htag Hp. destruct tag as [|[|[|[|tag]]]]; try lia;
    cbn [fold_payload].
  - intros [a' [d' [Ha [Hd Hv]]]].
    destruct (tagged_pair_zero_descent M a d n Hnz Htag) as [Han Hdn].
    exists a',d'. split; [exact (Hp a a' Han Ha)|].
    split; [exact (Hp d d' Hdn Hd)|exact Hv].
  - auto.
  - intros [d' [Hd Hv]].
    destruct (tagged_pair_positive_descent M a d n 2 ltac:(lia) Htag) as [_ Hdn].
    exists d'. split; [exact (Hp d d' Hdn Hd)|exact Hv].
  - auto.
Qed.

Lemma fold_step_prefix_forward M spec rho b c b' c' n v :
  prefix M b c b' c' n -> fold_step M spec rho b c n v ->
  fold_step M spec rho b' c' n v.
Proof.
  intros Hp [[Hz Hv]|[Hnz Hpay]]; [left;auto|].
  apply (proj2 (fold_step_decode M spec rho b' c' n v Hnz)).
  assert (H : fold_step M spec rho b c n v) by (right;auto).
  apply (proj1 (fold_step_decode M spec rho b c n v Hnz)) in H.
  destruct H as [tag [a [d [Ht [Htag Hv]]]]].
  exists tag,a,d. split; [exact Ht|]. split; [exact Htag|].
  exact (fold_payload_prefix M spec rho b c b' c' n tag a d v Hnz Ht Htag Hp Hv).
Qed.

Theorem fold_step_respects_prefix M spec rho b c b' c' n :
  prefix M b c b' c' n -> forall v,
  (fold_step M spec rho b c n v <-> fold_step M spec rho b' c' n v).
Proof.
  intros Hp v. split.
  - exact (fold_step_prefix_forward M spec rho b c b' c' n v Hp).
  - apply (fold_step_prefix_forward M spec rho b' c' b c n v).
    exact (prefix_back M b c b' c' n Hp).
Qed.

Definition numerical_fold M spec rho := recursion_graph M (fold_step_formula spec) rho.
Definition numerical_fold_formula spec := recursion_graph_formula (fold_step_formula spec).

Theorem numerical_fold_formula_correct M spec rho n v :
  holds M rho (numerical_fold_formula spec n v) <->
  numerical_fold M spec rho (evalM M rho n) (evalM M rho v).
Proof. apply recursion_graph_formula_correct. Qed.

Theorem numerical_fold_total M spec rho n : exists v, numerical_fold M spec rho n v.
Proof.
  apply recursion_graph_total.
  - intros b c i. destruct (fold_step_total M spec rho b c i) as [v Hv].
    exists v. now apply fold_step_formula_correct.
  - intros b c b' c' i Hp v. rewrite !fold_step_formula_correct.
    exact (fold_step_respects_prefix M spec rho b c b' c' i Hp v).
Qed.

Theorem numerical_fold_functional M spec rho n v w :
  numerical_fold M spec rho n v -> numerical_fold M spec rho n w -> v=w.
Proof.
  apply recursion_graph_functional.
  - intros b c i x y. rewrite !fold_step_formula_correct.
    apply fold_step_functional.
  - intros b c b' c' i Hp x. rewrite !fold_step_formula_correct.
    exact (fold_step_respects_prefix M spec rho b c b' c' i Hp x).
Qed.

Print Assumptions fold_step_formula_correct.
Print Assumptions numerical_fold_total.
Print Assumptions numerical_fold_functional.
Print Assumptions numerical_fold_formula_correct.
