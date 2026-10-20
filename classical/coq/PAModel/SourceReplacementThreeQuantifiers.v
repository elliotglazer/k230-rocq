(** Turn the actual three guarded universal functionality quantifiers into
    ordinary functionality of the guarded matrix. Context shifts and domain
    renamings are explicit; matrix holes range over arbitrary PA codes. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
  SourceBounded NumericalContexts NumericalContextRenaming NumericalRenaming
  SourceQuantifierRules SourceRelativizationBounds NumericalSourceFull
  SourceUniversalPropositional SourcePropositionalTemplates SourcePropositionalApplication
  SourceReplacementPropositional SourceImplicationAllShift SetSchemaConstructors.
Unset Implicit Arguments.

Definition replacement_point := SPTImpl (SPTSlot 3) (SPTImpl (SPTSlot 4) (SPTSlot 5)).

Theorem source_full_replacement_three_quantifiers M rho k b c n
    point g2 p1 g1 p0 g0 guarded target target1 target2 out :
  context_bounded M b c n k ->
  (forall i,source_bounded M (rho i) (succM M (succM M (succM M k)))) ->
  source_bounded M (rho 2) (code_numeral M 1) ->
  source_formula_shift M (rho 2) (rho 1) -> source_formula_shift M (rho 1) (rho 0) ->
  code_relation M rho (source_prop_expression replacement_point) point ->
  sf_relation M SFImpl (rho 2) point g2 -> sf_relation M SFAll g2 (zeroM M) p1 ->
  sf_relation M SFImpl (rho 2) p1 g1 -> sf_relation M SFAll g1 (zeroM M) p0 ->
  sf_relation M SFImpl (rho 2) p0 g0 -> sf_relation M SFAll g0 (zeroM M) guarded ->
  code_relation M rho (source_prop_expression replacement_unguarded_point) target ->
  sf_relation M SFAll target (zeroM M) target1 ->
  sf_relation M SFAll target1 (zeroM M) target2 ->
  sf_relation M SFAll target2 (zeroM M) out ->
  source_full_prv M b c n guarded -> source_full_prv M b c n out.
Proof.
  intros HC HB HD HS1 HS2 HPt HG2 HQ2 HG1 HQ1 HG0 HQ0 HT HT1 HT2 HT3 PG.
  pose proof (source_prop_template_bound M rho replacement_point
    (succM M (succM M (succM M k))) HB point HPt) as HPointBound.
  assert (HG2Bound:source_bounded M g2 (succM M (succM M (succM M k)))).
  { apply (proj2 (source_bounded_accept_binary M SFImpl (rho 2) point g2
      (succM M (succM M (succM M k))) (or_intror (or_intror eq_refl)) HG2)).
    split;[exact (HB 2)|exact HPointBound]. }
  pose proof (proj2 (source_bounded_accept_unary M SFAll g2 p1
    (succM M (succM M k)) (or_introl eq_refl) HQ2) HG2Bound) as HP1Bound.
  pose proof (source_prop_template_bound M rho replacement_unguarded_point
    (succM M (succM M (succM M k))) HB target HT) as HTBound.
  pose proof (proj2 (source_bounded_accept_unary M SFAll target target1
    (succM M (succM M k)) (or_introl eq_refl) HT1) HTBound) as HT1Bound.
  pose proof (proj2 (source_bounded_accept_unary M SFAll target1 target2
    (succM M k) (or_introl eq_refl) HT2) HT1Bound) as HT2Bound.
  pose proof (proj2 (source_bounded_accept_unary M SFAll target2 out k
    (or_introl eq_refl) HT3) HT2Bound) as HOutBound.
  destruct (context_shift_total M b c n) as [b1 [c1 HC1]].
  destruct (context_shift_total M b1 c1 n) as [b2 [c2 HC2]].
  destruct (context_shift_total M b2 c2 n) as [b3 [c3 HC3]].
  pose proof (context_shift_preserves_bound M b c n b1 c1 k HC1 HC) as HB1.
  pose proof (context_shift_preserves_bound M b1 c1 n b2 c2 (succM M k) HC2 HB1) as HB2.
  pose proof (context_shift_preserves_bound M b2 c2 n b3 c3 (succM M (succM M k)) HC3 HB2) as HB3.
  pose proof (source_full_all_shift M b c n g0 guarded b1 c1 HQ0 PG HC1) as PG0.
  destruct (sf_relation_total M SFImpl (rho 1) g1) as [curried HCurried].
  pose proof (source_full_implication_all_shift M b1 c1 n (rho 2) g1 p0 g0
    b2 c2 (rho 1) curried HQ1 HG0 HC2 HS1 HCurried PG0) as PCurried.
  destruct (sf_relation_total M SFAnd (rho 1) (rho 2)) as [guards HGuards].
  destruct (sf_relation_total M SFImpl guards p1) as [joined HJoined].
  set (env:=schema_env3 (rho 1) (rho 2) p1).
  assert (HEnv:forall i,source_bounded M (env i) (succM M (succM M k))).
  { intros [|[|i]];cbn [env schema_env3].
    - exact (source_shift_bound M (rho 2) (rho 1) (succM M k)
        (sr_domain_bound_succ M (rho 2) k HD) HS1).
    - exact (sr_domain_bound_succ M (rho 2) (succM M k) HD).
    - exact HP1Bound. }
  assert (HCurriedCode:code_relation M env (source_prop_expression source_curry_point) curried).
  { apply (source_prop_template_join M env SFImpl (SPTSlot 0)
      (SPTImpl (SPTSlot 1) (SPTSlot 2)) (rho 1) g1 curried eq_refl).
    - exact (source_prop_template_join M env SFImpl (SPTSlot 1) (SPTSlot 2)
        (rho 2) p1 g1 eq_refl eq_refl HG1).
    - exact HCurried. }
  assert (HJoinedCode:code_relation M env (source_prop_expression source_joined_point) joined).
  { apply (source_prop_template_join M env SFImpl (SPTAnd (SPTSlot 0) (SPTSlot 1))
      (SPTSlot 2) guards p1 joined).
    - exact (source_prop_template_join M env SFAnd (SPTSlot 0) (SPTSlot 1)
        (rho 1) (rho 2) guards eq_refl eq_refl HGuards).
    - reflexivity.
    - exact HJoined. }
  pose proof (source_prop_program_apply M source_curry_point source_joined_point
    source_joined_point_program env (succM M (succM M k)) b2 c2 n curried joined
    HEnv HB2 HCurriedCode HJoinedCode PCurried) as PJoined.
  destruct (sf_relation_total M SFAnd (rho 0) (rho 1)) as [guards' HGuards'].
  assert (HGuardsShift:source_formula_shift M guards guards').
  { apply (proj2 (numerical_renaming_binary M SFAnd (rho 1) (rho 2) guards
      (zeroM M) (zeroM M) (zeroM M) (succM M (zeroM M)) guards'
      (or_introl eq_refl) HGuards)). exists (rho 0),(rho 1). auto. }
  destruct (sf_relation_total M SFImpl guards' g2) as [gathered HGathered].
  pose proof (source_full_implication_all_shift M b2 c2 n guards g2 p1 joined
    b3 c3 guards' gathered HQ2 HJoined HC3 HGuardsShift HGathered PJoined) as PGathered.
  assert (HGatheredCode:code_relation M rho
    (source_prop_expression replacement_gathered_point) gathered).
  { apply (source_prop_template_join M rho SFImpl (SPTAnd (SPTSlot 0) (SPTSlot 1))
      (SPTImpl (SPTSlot 2) replacement_point) guards' g2 gathered).
    - exact (source_prop_template_join M rho SFAnd (SPTSlot 0) (SPTSlot 1)
        (rho 0) (rho 1) guards' eq_refl eq_refl HGuards').
    - exact (source_prop_template_join M rho SFImpl (SPTSlot 2) replacement_point
        (rho 2) point g2 eq_refl HPt HG2).
    - exact HGathered. }
  pose proof (source_prop_program_apply M replacement_gathered_point replacement_unguarded_point
    replacement_gathered_cleanup_program rho (succM M (succM M (succM M k)))
    b3 c3 n gathered target HB HB3 HGatheredCode HT PGathered) as PTarget.
  pose proof (full_source_AllI M b2 c2 n target target1 b3 c3
    (ex_intro _ (succM M (succM M k)) (conj HT1Bound HB2)) PTarget HC3 HT1) as PTarget1.
  pose proof (full_source_AllI M b1 c1 n target1 target2 b2 c2
    (ex_intro _ (succM M k) (conj HT2Bound HB1)) PTarget1 HC2 HT2) as PTarget2.
  exact (full_source_AllI M b c n target2 out b1 c1
    (ex_intro _ k (conj HOutBound HC)) PTarget2 HC1 HT3).
Qed.

Print Assumptions source_full_replacement_three_quantifiers.
