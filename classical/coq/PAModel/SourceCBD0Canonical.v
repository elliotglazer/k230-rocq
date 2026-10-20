(** The existing literal D0f recipe is the one-level condition with its
    ordinal and container names inserted above the witness. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceFiniteCutoffShift
  SourceD0Recipe SourceD0At SourceHierarchySyntax SourceCBGoal SourceDn SourceOrdinalPredicate SourceWitnessBoundGoal.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.

Theorem source_d0_recipe_at_canonical M domain level phi p1 p2 out:
  source_LL_instance M(code_numeral M 1)(zeroM M)level ->
  source_cutoff_shift M 1 phi p1 ->source_cutoff_shift M 1 p1 p2 ->
  (source_d0_recipe M domain level phi out <->source_d0_at M domain p2(zeroM M)out).
Proof.
  intros HL HC1 HC2. split.
  - intros(p3&ew&point&(q1&q2&H1&H2&H3)&HE&HP&HO).
    pose proof(SourceQfFunctionality.source_cutoff_shift_functional M 1 phi q1 p1 H1 HC1) as E. subst q1.
    pose proof(SourceQfFunctionality.source_cutoff_shift_functional M 1 p1 q2 p2 H2 HC2) as E. subst q2.
    exists p3,level,ew,point. repeat split;assumption.
  - intros(p3&level'&ew&point&H3&HL'&HE&HP&HO).
    pose proof(source_LL_instance_functional M(code_numeral M 1)(zeroM M)level' level HL' HL) as E. subst level'.
    exists p3,ew,point. split;[exists p1,p2;auto|]. repeat split;assumption.
Qed.

Theorem source_cb_goal_zero_witness M domain level phi p1 out:
  source_LL_instance M(code_numeral M 1)(zeroM M)level ->source_cutoff_shift M 1 phi p1 ->
  (source_cb_goal M domain level(source_ordinal_predicate_code M)(zeroM M)phi out <->
   source_witness_bound_goal M domain p1 out).
Proof.
  intros HL HC1. split.
  - intros(d0&dn&body&HD0&HDN&HBody&HEx). apply source_dn_zero in HDN. subst dn.
    destruct(source_cutoff_shift_total M 1 p1) as(p2&HC2).
    exists p2,d0,body. split;[exact HC2|]. split;[|split;assumption].
    exact(proj1(source_d0_recipe_at_canonical M domain level phi p1 p2 d0 HL HC1 HC2)HD0).
  - intros(p2&d0&body&HC2&HD0&HBody&HEx).
    exists d0,d0,body. split.
    + exact(proj2(source_d0_recipe_at_canonical M domain level phi p1 p2 d0 HL HC1 HC2)HD0).
    + split;[apply(proj2(source_dn_zero M d0 d0));reflexivity|split;assumption].
Qed.

Print Assumptions source_d0_recipe_at_canonical.
Print Assumptions source_cb_goal_zero_witness.
