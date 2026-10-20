(** Uniform raw K-core instances. Padding supplies a private variable,
    and proof-producing congruence replaces the padded matrix by the
    requested arbitrary internal formula code. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions
  NumericalProofs NumericalEquivalence NumericalVacuitySteps NamedLeibnizSteps
  KInternalLogic NumericalMatrixPadding FreshNames.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Lemma expression_krequest_equivalent M rho b k m n :
  expression_equivalent M rho m n ->
  expression_equivalent M rho (E_krequest b k m) (E_krequest b k n).
Proof.
  intro H. unfold E_krequest.
  apply expression_equivalent_all,expression_equivalent_implication;[exact H|].
  apply expression_equivalent_exists,expression_equivalent_conjunction;[exact H|].
  apply expression_equivalent_refl.
Qed.
Lemma expression_kcore_equivalent M rho a b k m n :
  expression_equivalent M rho m n ->
  expression_equivalent M rho (E_kcore a b k m) (E_kcore a b k n).
Proof.
  intro H. unfold E_kcore.
  apply expression_equivalent_exists,expression_equivalent_conjunction.
  - apply expression_equivalent_implication;[exact H|apply expression_equivalent_refl].
  - apply expression_equivalent_all,expression_equivalent_implication;
      [apply expression_equivalent_refl|].
    apply expression_equivalent_exists,expression_equivalent_conjunction;[exact H|].
    apply expression_equivalent_all,expression_equivalent_implication;
      [apply expression_equivalent_refl|].
    exact (expression_krequest_equivalent M rho b k m n H).
Qed.

Theorem numerical_kcore_matrix_equivalent M a b k m n f g :
  numerical_equivalent M m n ->
  code_relation M (code_parameters a b k m)
    (E_kcore (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)) f ->
  code_relation M (code_parameters a b k n)
    (E_kcore (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)) g ->
  numerical_equivalent M f g.
Proof.
  intros H HF HG. set (rho:=a .: b .: k .: m .: n .: fun _=>zeroM M).
  assert (Hf : code_relation M rho
    (E_kcore (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)) f) by exact HF.
  assert (Hg : code_relation M rho
    (E_kcore (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 4)) g) by exact HG.
  apply (proj1 (numerical_equivalent_expression M rho _ _ f g Hf Hg)).
  apply expression_kcore_equivalent.
  exact (proj2 (numerical_equivalent_expression M rho (CEvar 3) (CEvar 4) m n eq_refl eq_refl) H).
Qed.

Theorem numerical_uniform_kcore M a b m :
  exists k f, k<>a /\ k<>b /\ formula_fresh M m k /\
    code_relation M (code_parameters a b k m)
      (E_kcore (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)) f /\
    numerically_provable M f.
Proof.
  destruct (numerical_matrix_padding M a b m) as [k [HE [Ha [Hb [Hm HFresh]]]]].
  assert (Hka:k<>a).
  { intro E. subst k. exact (@Peano.lt_neq (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) a a Ha eq_refl). }
  assert (Hkb:k<>b).
  { intro E. subst k. exact (@Peano.lt_neq (carrier M) (raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) b b Hb eq_refl). }
  destruct (code_relation_total M (E_k230 (CEvar 0) (CEvar 1) (CEvar 2))
    (code_parameters a b k (zeroM M))) as [p HP].
  pose proof (numerical_K_core M a b k p Hka Hkb HP) as PP.
  destruct (code_relation_total M (E_kcore (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3))
    (code_parameters a b k m)) as [f HF].
  assert (HP' : code_relation M (code_parameters a b k k)
    (E_kcore (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)) p) by exact HP.
  pose proof (numerical_kcore_matrix_equivalent M a b k k m p f
    (numerical_equivalent_sym M m k HE) HP' HF) as EQ.
  exists k,f. split;[exact Hka|]. split;[exact Hkb|]. split;[exact HFresh|].
  split;[exact HF|]. exact (numerical_implies_apply M p f (proj1 EQ) PP).
Qed.

Print Assumptions numerical_kcore_matrix_equivalent.
Print Assumptions numerical_uniform_kcore.
