(** Actual proof consumer for the ordinary L-definable witness and the
    literal reflection/transitivity formulas at its hierarchy carrier. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SetSchemaConstructors
  SourceBounded SourceRelativization SourceRelativizationBounds SourceSetRelativization SourceSetRelativizationBounds
  NumericalContexts NumericalContextRenaming NumericalSourceFull SourcePropositionalTemplates SourceFunctionalityShells
  SourceLSeparationPoint SourceLSeparationData SourceLSeparationWitness SourceLSeparationCarrierShell
  SourceLDefinableProfile.
Unset Implicit Arguments.

Theorem source_full_L_separation_carrier_witness M domain matrix lp sp defex allr allt out k b c n u v :
  source_bounded M domain(code_numeral M 1) ->source_bounded M matrix(succM M(succM M k)) ->
  coding_lt M(code_numeral M 3)(succM M(succM M k)) ->
  source_relativization M domain matrix lp ->source_set_relativization M(code_numeral M 2)matrix sp ->
  source_lsep_carrier_def_shell M domain sp defex ->
  code_relation M(L_definable_profile_environment lp sp)(E_L_carrier_reflection(CEvar 0)(CEvar 1))allr ->
  code_relation M(fun _=>zeroM M)E_L_carrier_transitive allt ->
  code_relation M(L_definable_profile_environment lp domain)(E_L_carrier_separation(CEvar 1)(CEvar 0))out ->
  context_bounded M b c n k ->source_bounded M defex k ->context_shift M b c n u v ->
  source_full_prv M b c n defex ->source_full_prv M u v n allr ->source_full_prv M u v n allt ->
  source_full_prv M b c n out.
Proof.
  intros HD HB H3 HLP HSP HShell HReflection HTransitive HOut HC BDef HShift PDef PReflection PTransitive.
  destruct(source_lsep_carrier_definition_graph M domain sp defex lp HShell)
    as(zx&zy&za&definition&alld&defbody&HZX&HZY&HZA&HDefinition&HAllD&HDefBody&HDefEx).
  set(rho:=source_lsep_environment M zx zy za lp sp).
  destruct(sf_relation_total M SFImpl lp sp) as(lps&HLS).
  destruct(sf_relation_total M SFImpl sp lp) as(spl&HSL).
  destruct(sf_relation_total M SFAnd lps spl) as(equivalence&HEquivalence).
  destruct(sf_relation_total M SFImpl zy equivalence) as(reflection&HRef).
  destruct(sf_relation_total M SFAll reflection(zeroM M)) as(allr'&HAllR).
  assert(HRefGraph:code_relation M rho(source_prop_expression lsep_reflection_point)reflection).
  { unfold rho,source_lsep_environment,lsep_reflection_point,lsep_iff,source_prop_expression. functionality_graph. }
  assert(HR:code_relation M(L_definable_profile_environment lp sp)(E_L_carrier_reflection(CEvar 0)(CEvar 1))allr').
  { unfold L_definable_profile_environment,E_L_carrier_reflection,E_sf_iff. functionality_graph. }
  pose proof(code_relation_functional M _ _ allr allr' HReflection HR) as E. subst allr'.
  destruct(sf_relation_total M SFImpl za zy) as(transitive&HTrans).
  destruct(sf_relation_total M SFAll transitive(zeroM M)) as(allt'&HAllT).
  assert(HTransGraph:code_relation M rho(source_prop_expression lsep_transitive_point)transitive).
  { unfold rho,source_lsep_environment,lsep_transitive_point,source_prop_expression. functionality_graph. }
  assert(HT:code_relation M(fun _=>zeroM M)E_L_carrier_transitive allt').
  { unfold E_L_carrier_transitive. functionality_graph. }
  pose proof(code_relation_functional M _ _ allt allt' HTransitive HT) as E. subst allt'.
  destruct(sf_relation_total M SFAnd za lp) as(selected&HSelected).
  destruct(sf_relation_total M SFImpl zx selected) as(lr&HLR).
  destruct(sf_relation_total M SFImpl selected zx) as(rl&HRL).
  destruct(sf_relation_total M SFAnd lr rl) as(result&HResult).
  destruct(sf_relation_total M SFAll result(zeroM M)) as(allresult&HAllResult).
  destruct(sf_relation_total M SFImpl domain result) as(guarded&HGuarded).
  destruct(sf_relation_total M SFAll guarded(zeroM M)) as(guardedall&HGuardedAll).
  destruct(sf_relation_total M SFAnd domain guardedall) as(outbody&HOutBody).
  destruct(sf_relation_total M SFEx outbody(zeroM M)) as(out'&HOutEx).
  assert(HResultGraph:code_relation M rho(source_prop_expression lsep_result_point)result).
  { unfold rho,source_lsep_environment,lsep_result_point,lsep_iff,source_prop_expression. functionality_graph. }
  assert(HO:code_relation M(L_definable_profile_environment lp domain)(E_L_carrier_separation(CEvar 1)(CEvar 0))out').
  { unfold L_definable_profile_environment,E_L_carrier_separation,E_sf_iff. functionality_graph. }
  pose proof(code_relation_functional M _ _ out out' HOut HO) as E. subst out'.
  assert(H2:coding_lt M(code_numeral M 2)(succM M(succM M k))).
  { exact(coding_lt_trans M(code_numeral M 2)(code_numeral M 3)(succM M(succM M k))(coding_lt_succ M(code_numeral M 2))H3). }
  assert(H1:coding_lt M(code_numeral M 1)(succM M(succM M k))).
  { exact(coding_lt_trans M(code_numeral M 1)(code_numeral M 2)(succM M(succM M k))(coding_lt_succ M(code_numeral M 1))H2). }
  assert(HRho:forall j,source_bounded M(rho j)(succM M(succM M k))).
  { intros[|[|[|[|[|j]]]]];unfold rho,source_lsep_environment.
    - apply(proj2(source_bounded_accept_atom M SFMember(zeroM M)(code_numeral M 1)zx _ (or_introl eq_refl)HZX)). split;[apply coding_zero_lt_succ|exact H1].
    - apply(proj2(source_bounded_accept_atom M SFMember(zeroM M)(code_numeral M 2)zy _ (or_introl eq_refl)HZY)). split;[apply coding_zero_lt_succ|exact H2].
    - apply(proj2(source_bounded_accept_atom M SFMember(zeroM M)(code_numeral M 3)za _ (or_introl eq_refl)HZA)). split;[apply coding_zero_lt_succ|exact H3].
    - exact(source_relativization_preserves_bound M matrix domain _ lp HD HB HLP).
    - exact(source_set_relativization_preserves_bound M matrix(code_numeral M 2)_ sp H2 HB HSP).
    - apply source_bounded_accept_falsity. }
  exact(source_full_L_separation_witness M domain rho k b c n u v definition reflection transitive result
    alld allr allt allresult guarded guardedall defbody defex outbody out HD HRho HC BDef HShift
    HDefinition HRefGraph HTransGraph HResultGraph HAllD HAllR HAllT HAllResult HGuarded HGuardedAll HDefBody HDefEx HOutBody HOutEx
    PDef PReflection PTransitive).
Qed.
Print Assumptions source_full_L_separation_carrier_witness.
