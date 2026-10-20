(** The two actual carrier choices for coincident active names. The
    context must be vacuous at the carrier name. The final case split
    will impose that condition only on its own explicit assumptions. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalContexts NumericalEnvironments NumericalSourceFull SourceSequents SourceContextTransport
  SourceUniversalDistribution SourceInstantiationConstructors SourceProofWeakening SourceDerivedRules
  SourceNamedVacuity SourceNamedQuantifierRules SourceNamedElimination SourceNamedProofRules
  NativeKBundle NativeNamedRegularity NativeNamedProofRules NativeEqualClosure NativeEmptyClosure.
Unset Implicit Arguments.

Lemma source_full_weaken_cons M b c n f u v m g k :
  environment_cons M b c n f u v m ->source_bounded M f k ->source_full_prv M b c n g ->
  source_full_prv M u v m g.
Proof.
  intros HCons HF PG.
  destruct(source_full_prv_wellformed M b c n g PG) as(l&_&HC).
  destruct(source_context_finite_bound_cons M b c n f u v m (ex_intro _ l HC)
    (ex_intro _ k HF) HCons) as(q&HQ).
  apply(source_full_prv_weaken_bounded M b c n u v m g q PG);[|exact HQ].
  intros h HH. apply(proj2(context_member_cons M b c n f u v m h HCons)). now right.
Qed.

Lemma source_full_weaken_empty M b c n f k :context_bounded M b c n k ->
  source_full_prv M (zeroM M)(zeroM M)(zeroM M) f ->source_full_prv M b c n f.
Proof.
  intros HC HP. apply(source_full_prv_weaken_bounded M (zeroM M)(zeroM M)(zeroM M) b c n f k HP);[|exact HC].
  intros g HG. exfalso. exact(context_empty M (zeroM M)(zeroM M) g HG).
Qed.

Theorem native_equal_core_true M b c n env name container matrix x y phi member host core :
  code_relation M env name x ->code_relation M env container y ->
  native_named_evaluation M env matrix phi ->sf_relation M SFMember x y member ->
  source_named_quantifier M false y member host ->
  native_named_evaluation M env (NNT_core name name container matrix) core ->
  source_named_context_vacuous M b c n y ->source_full_prv M b c n phi ->
  source_full_prv M b c n host ->source_full_prv M b c n core.
Proof.
  intros HX HY HPhi HM HHost HCore HVac PPhi PHost.
  destruct(native_named_quantifier_view M env false container
    (NNTAnd (NNTImpl matrix (NNTAtom false name container))
      (NNT_equal_closure name container matrix)) core HCore) as(y'&body&HY'&HBody&HCoreQ).
  rewrite(code_relation_functional M container env y' y HY' HY) in HCoreQ.
  destruct(native_named_evaluation_bounded M env
    (NNTAnd (NNTImpl matrix (NNTAtom false name container))
      (NNT_equal_closure name container matrix)) body HBody) as(k&HBodyB).
  pose proof(source_named_quantifier_is_vacuous M false y body core k HBodyB HCoreQ) as HCoreVac.
  destruct(native_named_evaluation_bounded M env matrix phi HPhi) as(l&HPhiB).
  assert (HMemberEval:native_named_evaluation M env (NNTAtom false name container) member).
  { exists x,y. auto. }
  destruct(native_named_evaluation_bounded M env (NNTAtom false name container) member HMemberEval) as(j&HMemberB).
  destruct(environment_cons_total M b c n member) as(u&v&m&HCons).
  pose proof(source_full_prv_wellformed M b c n phi PPhi) as(k0&_&HC).
  pose proof(source_context_finite_bound_cons M b c n member u v m (ex_intro _ k0 HC)
    (ex_intro _ j HMemberB) HCons) as HNew.
  assert (PM:source_full_prv M u v m member).
  { apply full_source_Ctx;[exact(source_bounded_in_context_wf M u v m member j HMemberB HNew)|].
    apply(proj2(context_member_cons M b c n member u v m member HCons)). now left. }
  pose proof(source_full_weaken_cons M b c n member u v m phi j HCons HMemberB PPhi) as PPhi'.
  destruct HBody as(root&closure&(f&a&HF&HA&HRoot)&HClosure&HAnd).
  rewrite(native_named_evaluation_unique M env matrix f phi HF HPhi),
    (native_named_evaluation_unique M env (NNTAtom false name container) a member HA HMemberEval) in HRoot.
  pose proof(source_full_ignore_antecedent M u v m phi member root l HPhiB HRoot PM) as PRoot.
  destruct(sf_relation_total M SFAnd phi member) as(point&HPoint).
  pose proof(source_full_and_intro M u v m phi member point HPoint PPhi' PM) as PPoint.
  destruct(source_named_quantifier_total M false x point) as(witness&HWitness).
  assert (HW:native_named_evaluation M env (NNT_equal_witness name container matrix) witness).
  { apply(native_named_quantifier_join M env false name _ x point witness HX);[|exact HWitness].
    exists phi,member. auto. }
  pose proof(source_full_named_quantifier_ex_intro M u v m x point witness HWitness PPoint) as PW.
  destruct(sf_relation_total M SFImpl witness closure) as(step&HStep).
  pose proof(native_equal_closure_from_witness M env name container matrix x witness closure step
    HX HW HClosure HStep) as PStep.
  destruct HNew as(bound&HCtx).
  pose proof(source_full_modus_ponens M u v m witness closure step HStep
    (source_full_weaken_empty M u v m step bound HCtx PStep) PW) as PClosure.
  pose proof(source_full_and_intro M u v m root closure body HAnd PRoot PClosure) as PBody.
  pose proof(source_full_named_quantifier_ex_intro M u v m y body core HCoreQ PBody) as PCore.
  destruct(sf_relation_total M SFImpl member core) as(imp&HImp).
  assert (PI:source_full_prv M b c n imp).
  { apply(full_source_II M b c n member core imp u v m);[|exact PCore|exact HCons|exact HImp].
    apply(source_wf_binary M b c n SFImpl member core imp (or_intror(or_intror eq_refl)) HImp).
    - exact(source_bounded_in_context_wf M b c n member j HMemberB (ex_intro _ k0 HC)).
    - exact(source_bounded_in_context_wf M b c n core k
        (source_named_quantifier_bound M false y body core k HBodyB HCoreQ)(ex_intro _ k0 HC)). }
  exact(source_full_named_exists_elim M b c n y member host core imp HVac HCoreVac HHost HImp PI PHost).
Qed.

Theorem native_equal_core_false M b c n env name container matrix x y phi negative empty emptyExists core :
  code_relation M env name x ->code_relation M env container y ->
  native_named_evaluation M env matrix phi ->sf_relation M SFImpl phi (zeroM M) negative ->
  source_named_empty M x y empty ->source_named_quantifier M false y empty emptyExists ->
  native_named_evaluation M env (NNT_core name name container matrix) core ->
  source_named_context_vacuous M b c n y ->source_full_prv M b c n negative ->
  source_full_prv M b c n emptyExists ->source_full_prv M b c n core.
Proof.
  intros HX HY HPhi HNeg HEmpty HEmptyExists HCore HVac PNeg PEmpty.
  destruct(native_named_quantifier_view M env false container
    (NNTAnd (NNTImpl matrix (NNTAtom false name container))
      (NNT_equal_closure name container matrix)) core HCore) as(y'&body&HY'&HBody&HCoreQ).
  rewrite(code_relation_functional M container env y' y HY' HY) in HCoreQ.
  destruct(native_named_evaluation_bounded M env
    (NNTAnd (NNTImpl matrix (NNTAtom false name container))
      (NNT_equal_closure name container matrix)) body HBody) as(k&HBodyB).
  pose proof(source_named_quantifier_is_vacuous M false y body core k HBodyB HCoreQ) as HCoreVac.
  pose proof(source_full_prv_wellformed M b c n emptyExists PEmpty) as(k0&_&HC).
  destruct HEmpty as(member&negativeMember&HM&HN&(rb&rc&emptyBody&HEMap&HER&HEQ)).
  assert (HEmptyGraph:source_named_empty M x y empty).
  { exists member,negativeMember. split;[exact HM|]. split;[exact HN|]. exists rb,rc,emptyBody;auto. }
  assert (HMemberEval:native_named_evaluation M env (NNTAtom false name container) member).
  { exists x,y;auto. }
  destruct(native_named_evaluation_bounded M env (NNTAtom false name container) member HMemberEval) as(j&HMemberB).
  assert (HNegMemberB:source_bounded M negativeMember j).
  { apply(proj2(source_bounded_accept_binary M SFImpl member (zeroM M) negativeMember j
      (or_intror(or_intror eq_refl)) HN)). split;[exact HMemberB|apply source_bounded_accept_falsity]. }
  pose proof(source_named_quantifier_bound M true x negativeMember empty j HNegMemberB
    (ex_intro _ rb (ex_intro _ rc (ex_intro _ emptyBody (conj HEMap (conj HER HEQ)))))) as HEmptyB.
  destruct(environment_cons_total M b c n empty) as(u&v&m&HCons).
  pose proof(source_context_finite_bound_cons M b c n empty u v m (ex_intro _ k0 HC)
    (ex_intro _ j HEmptyB) HCons) as HNew.
  assert (PE:source_full_prv M u v m empty).
  { apply full_source_Ctx;[exact(source_bounded_in_context_wf M u v m empty j HEmptyB HNew)|].
    apply(proj2(context_member_cons M b c n empty u v m empty HCons)). now left. }
  pose proof(source_full_weaken_cons M b c n empty u v m negative j HCons HEmptyB PNeg) as PNeg'.
  destruct HBody as(root&closure&(f&a&HF&HA&HRoot)&HClosure&HAnd).
  rewrite(native_named_evaluation_unique M env matrix f phi HF HPhi),
    (native_named_evaluation_unique M env (NNTAtom false name container) a member HA HMemberEval) in HRoot.
  pose proof(source_full_refuted_antecedent M u v m phi negative member root j HMemberB HNeg HRoot PNeg') as PRoot.
  destruct(sf_relation_total M SFImpl empty closure) as(step&HStep).
  pose proof(native_empty_closure M env name container matrix x y empty closure step
    HX HY HEmptyGraph HClosure HStep) as PStep.
  destruct HNew as(bound&HCtx).
  pose proof(source_full_modus_ponens M u v m empty closure step HStep
    (source_full_weaken_empty M u v m step bound HCtx PStep) PE) as PClosure.
  pose proof(source_full_and_intro M u v m root closure body HAnd PRoot PClosure) as PBody.
  pose proof(source_full_named_quantifier_ex_intro M u v m y body core HCoreQ PBody) as PCore.
  destruct(sf_relation_total M SFImpl empty core) as(imp&HImp).
  assert (PI:source_full_prv M b c n imp).
  { apply(full_source_II M b c n empty core imp u v m);[|exact PCore|exact HCons|exact HImp].
    apply(source_wf_binary M b c n SFImpl empty core imp (or_intror(or_intror eq_refl)) HImp).
    - exact(source_bounded_in_context_wf M b c n empty j HEmptyB (ex_intro _ k0 HC)).
    - exact(source_bounded_in_context_wf M b c n core k
        (source_named_quantifier_bound M false y body core k HBodyB HCoreQ)(ex_intro _ k0 HC)). }
  exact(source_full_named_exists_elim M b c n y empty emptyExists core imp HVac HCoreVac HEmptyExists HImp PI PEmpty).
Qed.

Print Assumptions native_equal_core_true.
Print Assumptions native_equal_core_false.
