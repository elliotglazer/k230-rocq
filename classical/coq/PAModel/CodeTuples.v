(** A seven-field record code using six exact Cantor pairs. Fields are
    arbitrary elements of an arithmetic Model, not just standard numerals. *)
From PAModel Require Import Model FiniteCoding Pairing CodeExpressions SentenceBounds.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Definition E_tuple7 : code_expr :=
  CEpair (CEvar 0) (CEpair (CEvar 1) (CEpair (CEvar 2)
    (CEpair (CEvar 3) (CEpair (CEvar 4) (CEpair (CEvar 5) (CEvar 6)))))).

Definition tuple7_env {D : Type} (a b c d e f g fallback : D) : nat -> D :=
  a .: b .: c .: d .: e .: f .: g .: (fun _ => fallback).

Definition tuple7_graph M (a b c d e f g r : carrier M) : Prop :=
  code_relation M (tuple7_env a b c d e f g (zeroM M)) E_tuple7 r.

Definition tuple7_formula (a b c d e f g r : term) : form :=
  code_formula E_tuple7 (tuple7_env a b c d e f g zero) r.

Theorem tuple7_formula_correct M rho a b c d e f g r :
  holds M rho (tuple7_formula a b c d e f g r) <->
  tuple7_graph M (evalM M rho a) (evalM M rho b) (evalM M rho c)
    (evalM M rho d) (evalM M rho e) (evalM M rho f) (evalM M rho g) (evalM M rho r).
Proof.
  unfold tuple7_formula,tuple7_graph. rewrite code_formula_correct.
  apply code_relation_ext. intros [|[|[|[|[|[|[|i]]]]]]]; reflexivity.
Qed.

Theorem tuple7_total M a b c d e f g :
  exists r, tuple7_graph M a b c d e f g r.
Proof. apply code_relation_total. Qed.

Theorem tuple7_functional M a b c d e f g r r' :
  tuple7_graph M a b c d e f g r -> tuple7_graph M a b c d e f g r' -> r=r'.
Proof. apply code_relation_functional. Qed.

Lemma paired_code_agreement M env env' A B r :
  code_relation M env (CEpair A B) r -> code_relation M env' (CEpair A B) r ->
  exists x y, code_relation M env A x /\ code_relation M env' A x /\
    code_relation M env B y /\ code_relation M env' B y.
Proof.
  intros [x [y [Hx [Hy Hxy]]]] [x' [y' [Hx' [Hy' Hxy']]]].
  destruct (pair_injective M r x y x' y' Hxy Hxy') as [Ex Ey].
  subst x' y'. exists x,y. auto.
Qed.

Theorem tuple7_injective M a b c d e f g a' b' c' d' e' f' g' r :
  tuple7_graph M a b c d e f g r -> tuple7_graph M a' b' c' d' e' f' g' r ->
  a=a' /\ b=b' /\ c=c' /\ d=d' /\ e=e' /\ f=f' /\ g=g'.
Proof.
  unfold tuple7_graph,E_tuple7. intros H H'.
  destruct (paired_code_agreement M _ _ _ _ _ H H') as [x1 [y1 [H1 [H1' [T1 T1']]]]].
  destruct (paired_code_agreement M _ _ _ _ _ T1 T1') as [x2 [y2 [H2 [H2' [T2 T2']]]]].
  destruct (paired_code_agreement M _ _ _ _ _ T2 T2') as [x3 [y3 [H3 [H3' [T3 T3']]]]].
  destruct (paired_code_agreement M _ _ _ _ _ T3 T3') as [x4 [y4 [H4 [H4' [T4 T4']]]]].
  destruct (paired_code_agreement M _ _ _ _ _ T4 T4') as [x5 [y5 [H5 [H5' [T5 T5']]]]].
  destruct (paired_code_agreement M _ _ _ _ _ T5 T5') as [x6 [y6 [H6 [H6' [H7 H7']]]]].
  clear H H' T1 T1' T2 T2' T3 T3' T4 T4' T5 T5'.
  cbn [code_relation tuple7_env scons] in *.
  repeat split; congruence.
Qed.

(** Seven field variables followed by the result variable. Internal graph
    witnesses introduced by code_formula do not become free variables. *)
Theorem tuple7_formula_bounded :
  bounded 8 (tuple7_formula $0 $1 $2 $3 $4 $5 $6 $7).
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.
