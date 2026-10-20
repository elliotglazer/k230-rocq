(** A singleton query tag is allocated only after the actual K container
    and query names have been produced. The bound is a PA-definable sum. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions FreshNames
  CollectionFreshAllocation TemplateBinderFresh NumericalFreshSingleton.
From Stdlib Require Import Lists.List.
Unset Implicit Arguments.

Theorem collection_query_tag_allocation M theta thetaW (roles:list (carrier M)) :
  exists base tag,
    tag=succM M (succM M base) /\ coding_lt M (zeroM M) base /\
    (forall x,In x roles -> coding_lt M x base) /\
    (forall x,In x roles -> x<>tag) /\
    formula_fresh M theta tag /\ formula_fresh M thetaW tag.
Proof.
  set (base:=collection_name_bound M (zeroM M::theta::thetaW::roles)).
  set (tag:=succM M (succM M base)).
  assert (HB:forall x,In x (zeroM M::theta::thetaW::roles) -> coding_lt M x base).
  { intros x Hx. apply collection_name_bound_above,Hx. }
  assert (HBT:coding_lt M base tag).
  { apply coding_lt_trans with (y:=succM M base);apply coding_lt_succ. }
  exists base,tag. split;[reflexivity|]. split;[apply HB;now left|].
  split;[intros x Hx;apply HB;now right;right;right|].
  split.
  - intros x Hx. apply fresh_singleton_lt_neq. apply coding_lt_trans with (y:=base);[apply HB;now right;right;right|exact HBT].
  - split;apply formula_above_is_fresh;apply coding_lt_trans with (y:=base);try exact HBT;
      apply HB;[now right;left|now right;right;left].
Qed.

Print Assumptions collection_query_tag_allocation.

