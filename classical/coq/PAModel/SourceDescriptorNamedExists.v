(** Named existential rules for a genuine closed source-theory descriptor.
    Name vacuity of the conclusion remains explicit; no contextual
    generalization or weakening is hidden in these rules. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 NumericalContexts NumericalEnvironments NumericalSourceFull SourceAxiomContexts SourceSequents
 SourceContextProofHelpers SourceDescriptorProvability SourceDescriptorClosure
 SourceNamedVacuity SourceNamedElimination SourceNamedQuantifierRules.
Unset Implicit Arguments.

Theorem source_descriptor_named_exists_introduction_law M T x f exf result k :
 source_bounded M f k ->source_named_quantifier M false x f exf ->
 sf_relation M SFImpl f exf result ->source_descriptor_provable M T result.
Proof.
 intros BF HQ HR.
 pose proof(source_named_quantifier_bound M false x f exf k BF HQ)as BEx.
 pose proof(proj2(source_bounded_accept_binary M SFImpl f exf result k
  (or_intror(or_intror eq_refl)) HR)(conj BF BEx))as BR.
 destruct(environment_cons_total M(zeroM M)(zeroM M)(zeroM M) f)as(b&c&n&HC).
 assert(HCtx:context_bounded M b c n k).
 { exact(proj2(context_bounded_cons M _ _ _ f b c n k HC)
   (conj BF(context_bounded_empty M _ _ k))). }
 pose proof(source_full_cons_head M _ _ _ f b c n k HC BF HCtx)as PF.
 apply(source_descriptor_provable_from_empty M T result).
 exact(full_source_II M _ _ _ f exf result b c n
  (ex_intro _ k(conj BR(context_bounded_empty M _ _ k)))
  (source_full_named_quantifier_ex_intro M b c n x f exf HQ PF) HC HR).
Qed.

Theorem source_descriptor_named_exists_intro M T x f exf :
 source_named_quantifier M false x f exf ->source_descriptor_provable M T f ->
 source_descriptor_provable M T exf.
Proof.
 intros HQ(b&c&n&HC&HP). exists b,c,n. split;[exact HC|].
 exact(source_full_named_quantifier_ex_intro M b c n x f exf HQ HP).
Qed.

Theorem source_descriptor_named_exists_implication M T x f exf goal point result :
 source_named_quantifier M false x f exf ->source_named_vacuous M x goal ->
 sf_relation M SFImpl f goal point ->sf_relation M SFImpl exf goal result ->
 source_descriptor_provable M T point ->source_descriptor_provable M T result.
Proof.
 intros HQ HV HP HR(b&c&n&HC&PP).
 destruct(source_full_prv_wellformed M b c n point PP)as(k&BPoint&C0).
 destruct(proj1(source_bounded_accept_binary M SFImpl f goal point k
  (or_intror(or_intror eq_refl)) HP) BPoint)as[BF BG].
 pose proof(source_named_quantifier_bound M false x f exf k BF HQ)as BEx.
 pose proof(proj2(source_bounded_accept_binary M SFImpl exf goal result k
  (or_intror(or_intror eq_refl)) HR)(conj BEx BG))as BResult.
 destruct(environment_cons_total M b c n exf)as(u&v&m&HCons).
 assert(C1:context_bounded M u v m k).
 { exact(proj2(context_bounded_cons M b c n exf u v m k HCons)(conj BEx C0)). }
 assert(HOld:source_named_context_vacuous M b c n x).
 { intros a HA. exact(source_named_vacuous_above_bound M a x(zeroM M)
   (proj1 HC a HA)(coding_zero_lt_succ M x)). }
 assert(HCtx:source_named_context_vacuous M u v m x).
 { exact(source_named_context_vacuous_cons M b c n exf u v m x HCons HOld
   (source_named_quantifier_is_vacuous M false x f exf k BF HQ)). }
 pose proof(source_full_cons_weaken M b c n exf u v m k point HCons C1 PP)as PP'.
 pose proof(source_full_cons_head M b c n exf u v m k HCons BEx C1)as PEx.
 pose proof(source_full_named_exists_elim M u v m x f exf goal point HCtx HV HQ HP PP' PEx)as PG.
 exists b,c,n. split;[exact HC|].
 exact(full_source_II M b c n exf goal result u v m
   (ex_intro _ k(conj BResult C0)) PG HCons HR).
Qed.

Print Assumptions source_descriptor_named_exists_intro.
Print Assumptions source_descriptor_named_exists_introduction_law.
Print Assumptions source_descriptor_named_exists_implication.
