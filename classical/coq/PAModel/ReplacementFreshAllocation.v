(** Fresh names for a binary Collection witness are chosen after the
    actual substituted matrix exists. Thus the later names avoid its code. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions ProofClosure
  FreshNames.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Fixpoint replacement_name_bound M (names:list (carrier M)) :=
  match names with
  | nil=>succM M (zeroM M)
  | a::rest=>succM M (addM M a (replacement_name_bound M rest))
  end.

Lemma replacement_name_bound_above M names a :
  In a names -> coding_lt M a (replacement_name_bound M names).
Proof.
  induction names as [|b names IH];cbn;intro H;[contradiction|].
  destruct H as [<-|H].
  - exists (replacement_name_bound M names). reflexivity.
  - eapply coding_lt_trans with (y:=addM M b (replacement_name_bound M names));[|apply coding_lt_succ].
    rewrite (Arithmetic.add_comm M b). apply lt_left_sum,IH,H.
Qed.


Print Assumptions replacement_name_bound_above.

