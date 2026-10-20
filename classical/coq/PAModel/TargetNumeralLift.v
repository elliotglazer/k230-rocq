(** A fixed external K230 derivation yields a numerical K proof in every
    PA model. This does not identify internally nonstandard proofs with
    externally finite derivations. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  NumericalProofs ProofClosure ProofTemplates SourceNumeralLift.
From K230L Require Import Codes230 Thm230.
From Stdlib Require Import Arith Lia.
Unset Implicit Arguments.
Local Opaque KCode230.P.

Lemma target_numeral_parameters_graph M a b c u expression :
  code_relation M
    (code_parameters (code_numeral M a) (code_numeral M b)
      (code_numeral M c) (code_numeral M u)) expression
    (code_numeral M (code_value (code_parameters a b c u) expression)).
Proof.
  apply (proj2 (code_relation_ext M expression
    (code_parameters (code_numeral M a) (code_numeral M b)
      (code_numeral M c) (code_numeral M u))
    (fun i => code_numeral M (code_parameters a b c u i)) _
    ltac:(intros [|[|[|i]]];reflexivity))).
  apply code_relation_numeral.
Qed.

Definition target_row_value r a b c u :=
  match r with
  | LR1 => rho1 a b | LR2 => rho2 a b c | LR3 => rho3 a b c
  | LR4 => rho4 a b c | LR5 => rho5 a b c | LR6 => rho6 a b
  | LR7 => rho7 a b c | LR8 => rho8 a b c u
  end.

Lemma target_row_value_correct r a b c u :
  code_value (code_parameters a b c u) (row_expression r) = target_row_value r a b c u.
Proof.
  destruct r; unfold row_expression,code_row1,code_row2,code_row3,code_row4,
    code_row5,code_row6,code_row7,code_row8,target_row_value;
    rewrite ?code_value_rho1,?code_value_rho2,?code_value_rho3,?code_value_rho4,
      ?code_value_rho5,?code_value_rho6,?code_value_rho7,?code_value_rho8; reflexivity.
Qed.

Lemma target_numeral_row M r a b c u :
  numerically_provable M (code_numeral M (target_row_value r a b c u)).
Proof.
  apply numerical_axiom.
  apply (row_axiom M r (code_numeral M a) (code_numeral M b)
    (code_numeral M c) (code_numeral M u)).
  rewrite <- target_row_value_correct. apply target_numeral_parameters_graph.
Qed.

Lemma target_numeral_implication M a b :
  implication_graph M (code_numeral M a) (code_numeral M b)
    (code_numeral M (wim a b)).
Proof.
  unfold implication_graph.
  apply (proj2 (code_relation_ext M (E_wim (CEvar 0) (CEvar 1))
    (arguments2 (code_numeral M a) (code_numeral M b) (zeroM M))
    (code_parameters (code_numeral M a) (code_numeral M b) (code_numeral M 0) (code_numeral M 0)) _
    ltac:(intros [|[|[|i]]];reflexivity))).
  pose proof (target_numeral_parameters_graph M a b 0 0 (E_wim (CEvar 0) (CEvar 1))) as H.
  rewrite code_value_wim in H. exact H.
Qed.

Lemma target_numeral_universal M a b :
  universal_graph M (code_numeral M a) (code_numeral M b)
    (code_numeral M (wal a b)).
Proof.
  unfold universal_graph.
  apply (proj2 (code_relation_ext M (E_wal (CEvar 0) (CEvar 1))
    (arguments2 (code_numeral M a) (code_numeral M b) (zeroM M))
    (code_parameters (code_numeral M a) (code_numeral M b) (code_numeral M 0) (code_numeral M 0)) _
    ltac:(intros [|[|[|i]]];reflexivity))).
  pose proof (target_numeral_parameters_graph M a b 0 0 (E_wal (CEvar 0) (CEvar 1))) as H.
  rewrite code_value_wal in H. exact H.
Qed.

Lemma target_numerals_distinct M a b :
  a <> b -> code_numeral M a <> code_numeral M b.
Proof.
  induction a as [|a IH] in b |- *; destruct b as [|b]; intros H E.
  - apply H. reflexivity.
  - exact (zero_ne_succ M (code_numeral M b) E).
  - apply (zero_ne_succ M (code_numeral M a)). symmetry. exact E.
  - apply (IH b ltac:(lia)). apply (succ_injective M). exact E.
Qed.

Lemma target_numeral_bundle M a b c :
  c<>a -> c<>b -> numerically_provable M (code_numeral M (bundle a b c)).
Proof.
  intros Hca Hcb. apply numerical_axiom. right.
  exists (code_numeral M a),(code_numeral M b),(code_numeral M c),(code_numeral M 0).
  unfold code_axiom_rows. do 8 right.
  split;[exact (target_numerals_distinct M c a Hca)|].
  split;[exact (target_numerals_distinct M c b Hcb)|].
  pose proof (target_numeral_parameters_graph M a b c 0 (E_bundle (CEvar 0) (CEvar 1) (CEvar 2))) as H.
  rewrite code_value_bundle in H. exact H.
Qed.

Theorem thm230_numeral_lift M n :
  thm230 n -> numerically_provable M (code_numeral M n).
Proof.
  intro H. induction H as
    [|t b Ht IHt Htb IHtb|a h Hh IHh|a b|a b c|a b c|a b c|a b c|a b|a b c|a b c u|a b c Hca Hcb].
  - apply numerical_truth.
  - exact (numerical_mp M (code_numeral M t) (code_numeral M b)
      (code_numeral M (wim t b)) IHt IHtb (target_numeral_implication M t b)).
  - exact (numerical_gen M (code_numeral M a) (code_numeral M h)
      (code_numeral M (wal a h)) IHh (target_numeral_universal M a h)).
  - exact (target_numeral_row M LR1 a b 0 0).
  - exact (target_numeral_row M LR2 a b c 0).
  - exact (target_numeral_row M LR3 a b c 0).
  - exact (target_numeral_row M LR4 a b c 0).
  - exact (target_numeral_row M LR5 a b c 0).
  - exact (target_numeral_row M LR6 a b 0 0).
  - exact (target_numeral_row M LR7 a b c 0).
  - exact (target_numeral_row M LR8 a b c u).
  - exact (target_numeral_bundle M a b c Hca Hcb).
Qed.

Print Assumptions target_numerals_distinct.
Print Assumptions thm230_numeral_lift.
