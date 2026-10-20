(** Fresh names for a binary Collection witness are chosen after the
    actual substituted matrix exists. Thus the later names avoid its code. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions ProofClosure
  FreshNames NamedBinderFresh NamedSubstitution NamedSubstitutionPreservation.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Fixpoint collection_name_bound M (names:list (carrier M)) :=
  match names with
  | nil=>succM M (zeroM M)
  | a::rest=>succM M (addM M a (collection_name_bound M rest))
  end.

Lemma collection_name_bound_above M names a :
  In a names -> coding_lt M a (collection_name_bound M names).
Proof.
  induction names as [|b names IH];cbn;intro H;[contradiction|].
  destruct H as [<-|H].
  - exists (collection_name_bound M names). reflexivity.
  - eapply coding_lt_trans with (y:=addM M b (collection_name_bound M names));[|apply coding_lt_succ].
    rewrite (Arithmetic.add_comm M b). apply lt_left_sum,IH,H.
Qed.

Theorem collection_fresh_witness_allocation M theta x v (fixed:list (carrier M)) :
  named_binder_absent M theta x -> named_binder_absent M theta v ->
  exists w thetaW input root singleton,
    (forall a,In a (theta::x::v::fixed) -> coding_lt M a w) /\
    formula_fresh M theta w /\ named_substitution M theta x w thetaW /\
    named_binder_absent M thetaW x /\ named_binder_absent M thetaW v /\
    (forall a,In a (thetaW::w::fixed) -> coding_lt M a input) /\
    coding_lt M input root /\ coding_lt M root singleton /\
    formula_fresh M thetaW input /\ formula_fresh M thetaW root /\
    formula_fresh M thetaW singleton.
Proof.
  intros HX HV.
  set (w:=collection_name_bound M (theta::x::v::fixed)).
  assert (HW:forall a,In a (theta::x::v::fixed) -> coding_lt M a w).
  { intros a Ha. apply collection_name_bound_above,Ha. }
  assert (HF:formula_fresh M theta w).
  { apply formula_above_is_fresh,HW;now left. }
  destruct (named_substitution_fresh_total M theta x w HF) as [thetaW HSub].
  set (input:=collection_name_bound M (thetaW::w::fixed)).
  set (root:=succM M input). set (singleton:=succM M root).
  assert (HI:forall a,In a (thetaW::w::fixed) -> coding_lt M a input).
  { intros a Ha. apply collection_name_bound_above,Ha. }
  assert (HIR:coding_lt M input root) by apply coding_lt_succ.
  assert (HRS:coding_lt M root singleton) by apply coding_lt_succ.
  assert (HTI:coding_lt M thetaW input) by (apply HI;now left).
  exists w,thetaW,input,root,singleton.
  split;[exact HW|]. split;[exact HF|]. split;[exact HSub|].
  split;[exact (named_substitution_preserves_binders M theta x w thetaW x HSub HX)|].
  split;[exact (named_substitution_preserves_binders M theta x w thetaW v HSub HV)|].
  split;[exact HI|]. split;[exact HIR|]. split;[exact HRS|].
  split;[exact (formula_above_is_fresh M thetaW input HTI)|].
  split.
  - apply formula_above_is_fresh. exact (coding_lt_trans M thetaW input root HTI HIR).
  - apply formula_above_is_fresh. exact (coding_lt_trans M thetaW input singleton HTI
      (coding_lt_trans M input root singleton HIR HRS)).
Qed.

Print Assumptions collection_name_bound_above.
Print Assumptions collection_fresh_witness_allocation.
