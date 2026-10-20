(** Actual named existential elimination and elementary preservation of
    source-name vacuity. All eigenvariable restrictions remain explicit. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  SetFormulaCodes SetCodeDescent SourceBounded NumericalContexts NumericalEnvironments
  NumericalContextRenaming NumericalRenaming SourceQuantifierRules SourceSequents
  NumericalSourceFull SourceImplicationAllShift SourceContextTransport SourceUniversalDistribution SourceProofWeakening
  RawBinderRenaming RawPrivateBinderShift SourceNamedVacuity SourceNamedQuantifierRules.
Unset Implicit Arguments.

Theorem source_named_vacuous_above_bound M f x k :
  source_bounded M f k ->coding_lt M k (succM M x) ->source_named_vacuous M x f.
Proof.
  intros HF HK rb rc g shifted HM HR HS.
  exact (numerical_renaming_functional M f (zeroM M)(zeroM M)(zeroM M)
    (succM M (zeroM M)) g shifted
    (raw_binder_above_bound_is_shift M f x k rb rc g HF HK HM HR) HS).
Qed.

Theorem source_named_vacuous_binary M h a d f x :sf_binary h ->sf_relation M h a d f ->
  source_named_vacuous M x a ->source_named_vacuous M x d ->source_named_vacuous M x f.
Proof.
  intros HH HF HA HD rb rc g shifted HM HR HS.
  destruct (proj1(numerical_renaming_binary M h a d f rb rc (succM M x)
    (succM M(zeroM M)) g HH HF) HR) as(ar&dr&HAR&HDR&HG).
  destruct (proj1(numerical_renaming_binary M h a d f (zeroM M)(zeroM M)(zeroM M)
    (succM M(zeroM M)) shifted HH HF) HS) as(as'&ds'&HAS&HDS&HShift).
  rewrite (HA rb rc ar as' HM HAR HAS),(HD rb rc dr ds' HM HDR HDS) in HG.
  exact(sf_relation_functional M h as' ds' g shifted HG HShift).
Qed.

Theorem source_named_context_vacuous_cons M b c n f u v m x :
  environment_cons M b c n f u v m ->source_named_context_vacuous M b c n x ->
  source_named_vacuous M x f ->source_named_context_vacuous M u v m x.
Proof.
  intros HC HOld HF g HG. apply(proj1(context_member_cons M b c n f u v m g HC)) in HG.
  destruct HG as[->|HG];[exact HF|exact(HOld g HG)].
Qed.

Theorem source_full_named_vacuous_exists_elim M b c n x goal exgoal k :
  source_bounded M goal k ->source_named_vacuous M x goal ->
  source_named_quantifier M false x goal exgoal ->source_full_prv M b c n exgoal ->
  source_full_prv M b c n goal.
Proof.
  intros HG HV (rb&rc&body&HM&HR&HEx) HP.
  destruct(numerical_renaming_total M goal (zeroM M)(zeroM M)(zeroM M)
    (succM M(zeroM M))) as(shifted&HS).
  rewrite <-(HV rb rc body shifted HM HR HS) in HS.
  destruct(source_full_prv_wellformed M b c n exgoal HP) as(l&_&HCtx).
  destruct(context_shift_total M b c n) as(u&v&HShift).
  pose proof(source_context_finite_bound_shift M b c n u v (ex_intro _ l HCtx) HShift) as HUC.
  pose proof(source_shift_bound M goal body k HG HS) as HB.
  destruct(environment_cons_total M u v n body) as(d&e&m&HCons).
  pose proof(source_context_finite_bound_cons M u v n body d e m HUC
    (ex_intro _ (succM M k) HB) HCons) as HDC.
  apply(full_source_ExE M b c n body exgoal goal body u v d e m).
  - exact(source_bounded_in_context_wf M b c n goal k HG (ex_intro _ l HCtx)).
  - exact HP.
  - apply full_source_Ctx.
    + exact(source_bounded_in_context_wf M d e m body (succM M k) HB HDC).
    + apply(proj2(context_member_cons M u v n body d e m body HCons)). now left.
  - exact HEx.
  - exact HShift.
  - exact HCons.
  - exact HS.
Qed.

Theorem source_full_named_exists_elim M b c n x f exf goal imp :
  source_named_context_vacuous M b c n x ->source_named_vacuous M x goal ->
  source_named_quantifier M false x f exf ->sf_relation M SFImpl f goal imp ->
  source_full_prv M b c n imp ->source_full_prv M b c n exf ->source_full_prv M b c n goal.
Proof.
  intros HC HG HE HI PI PE.
  destruct(source_full_prv_wellformed M b c n imp PI) as(k&HB&_).
  pose proof(proj2(proj1(source_bounded_accept_binary M SFImpl f goal imp k
    (or_intror(or_intror eq_refl)) HI) HB)) as HGoal.
  destruct(source_named_quantifier_total M false x goal) as(exgoal&HQ).
  exact(source_full_named_vacuous_exists_elim M b c n x goal exgoal k HGoal HG HQ
    (source_full_named_quantifier_ex_map M b c n x f goal exf exgoal imp HC HE HQ HI PI PE)).
Qed.

Print Assumptions source_named_vacuous_binary.
Print Assumptions source_full_named_exists_elim.
