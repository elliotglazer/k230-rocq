(** Object-level classical case analysis completes the equal-role core.
    The public consumer has an arbitrary source context: freshness is
    proved only for the explicit temporary background and case assumptions. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes
  SourceBounded NumericalContexts NumericalEnvironments SourceSequents NumericalSourceFull
  SourceContextTransport SourceUniversalDistribution SourceInstantiationConstructors
  SourcePropositionalTemplates SourceProofWeakening SourceDerivedRules
  SourceNamedVacuity SourceNamedElimination SourceNamedQuantifierRules SourceNamedProofRules
  NativeKBundle NativeNamedRegularity NativeEqualClosure NativeEmptyClosure NativeEqualCarrierBranches.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Lemma source_case_program A C :source_prop_program
  [SPTImpl A C;SPTImpl (SPTImpl A SPTFalse) C] C.
Proof.
  apply(SPTIE _ (SPTImpl (SPTImpl C SPTFalse) C) C);[apply SPTPc|].
  apply SPTII. apply(SPTIE _ (SPTImpl A SPTFalse) C).
  - apply SPTCtx. cbn;tauto.
  - apply SPTII. apply(SPTIE _ C SPTFalse).
    + apply SPTCtx. cbn;tauto.
    + apply(SPTIE _ A C);apply SPTCtx;cbn;tauto.
Qed.

Theorem source_full_cases M b c n phi neg goal left right :
  sf_relation M SFImpl phi (zeroM M) neg ->sf_relation M SFImpl phi goal left ->
  sf_relation M SFImpl neg goal right ->source_full_prv M b c n left ->
  source_full_prv M b c n right ->source_full_prv M b c n goal.
Proof.
  intros HN HL HR PL PR.
  destruct(source_full_prv_wellformed M b c n left PL) as(k&HB&HC).
  destruct(proj1(source_bounded_accept_binary M SFImpl phi goal left k
    (or_intror(or_intror eq_refl)) HL) HB) as(HP&HG).
  apply(source_prop_program_sound M _ _ (source_case_program (SPTSlot 0)(SPTSlot 1))
    (code_parameters phi goal goal goal) k b c n goal).
  - intros[|[|[|i]]];cbn[code_parameters];assumption.
  - exact HC.
  - intros p [<-|[<-|[]]] f HF.
    + pose proof(source_prop_template_join M (code_parameters phi goal goal goal) SFImpl
        (SPTSlot 0)(SPTSlot 1) phi goal left eq_refl eq_refl HL) as HE.
      rewrite(code_relation_functional M _ _ f left HF HE). exact PL.
    + pose proof(source_prop_template_join M (code_parameters phi goal goal goal) SFImpl
        (SPTImpl (SPTSlot 0) SPTFalse)(SPTSlot 1) neg goal right
        (source_prop_template_join M _ SFImpl (SPTSlot 0) SPTFalse phi (zeroM M) neg
          eq_refl eq_refl HN) eq_refl HR) as HE.
      rewrite(code_relation_functional M _ _ f right HF HE). exact PR.
  - reflexivity.
Qed.

Theorem native_equal_core_with_vacuous_context M b c n env name container matrix x y
    phi member host empty emptyExists core :
  code_relation M env name x ->code_relation M env container y ->
  native_named_evaluation M env matrix phi ->source_bounded M phi y ->
  sf_relation M SFMember x y member ->source_named_quantifier M false y member host ->
  source_named_empty M x y empty ->source_named_quantifier M false y empty emptyExists ->
  native_named_evaluation M env (NNT_core name name container matrix) core ->
  source_named_context_vacuous M b c n y ->source_full_prv M b c n host ->
  source_full_prv M b c n emptyExists ->source_full_prv M b c n core.
Proof.
  intros HX HY HPhi HPhiBound HM HH HE HEE HCore HVac PHost PEmpty.
  pose proof(source_full_prv_wellformed M b c n host PHost) as(k0&_&HC).
  pose proof(source_named_vacuous_above_bound M phi y y HPhiBound (coding_lt_succ M y)) as HPhiVac.
  destruct(native_named_evaluation_bounded M env _ core HCore) as(k&HCoreBound).
  destruct(sf_relation_total M SFImpl phi (zeroM M)) as(negative&HN).
  assert (HNegBound:source_bounded M negative y).
  { apply(proj2(source_bounded_accept_binary M SFImpl phi (zeroM M) negative y
      (or_intror(or_intror eq_refl)) HN)). split;[exact HPhiBound|apply source_bounded_accept_falsity]. }
  pose proof(source_named_vacuous_above_bound M negative y y HNegBound (coding_lt_succ M y)) as HNegVac.
  destruct(sf_relation_total M SFImpl phi core) as(left&HL).
  destruct(sf_relation_total M SFImpl negative core) as(right&HR).
  assert (PLeft:source_full_prv M b c n left).
  { destruct(environment_cons_total M b c n phi) as(u&v&m&HCons).
    pose proof(source_context_finite_bound_cons M b c n phi u v m (ex_intro _ k0 HC)
      (ex_intro _ y HPhiBound) HCons) as HNew.
    apply(full_source_II M b c n phi core left u v m).
    - apply(source_wf_binary M b c n SFImpl phi core left (or_intror(or_intror eq_refl)) HL).
      + exact(source_bounded_in_context_wf M b c n phi y HPhiBound (ex_intro _ k0 HC)).
      + exact(source_bounded_in_context_wf M b c n core k HCoreBound (ex_intro _ k0 HC)).
    - apply(native_equal_core_true M u v m env name container matrix x y phi member host core
        HX HY HPhi HM HH HCore
        (source_named_context_vacuous_cons M b c n phi u v m y HCons HVac HPhiVac)).
      + apply full_source_Ctx;[exact(source_bounded_in_context_wf M u v m phi y HPhiBound HNew)|].
        apply(proj2(context_member_cons M b c n phi u v m phi HCons)). now left.
      + exact(source_full_weaken_cons M b c n phi u v m host y HCons HPhiBound PHost).
    - exact HCons.
    - exact HL. }
  assert (PRight:source_full_prv M b c n right).
  { destruct(environment_cons_total M b c n negative) as(u&v&m&HCons).
    pose proof(source_context_finite_bound_cons M b c n negative u v m (ex_intro _ k0 HC)
      (ex_intro _ y HNegBound) HCons) as HNew.
    apply(full_source_II M b c n negative core right u v m).
    - apply(source_wf_binary M b c n SFImpl negative core right (or_intror(or_intror eq_refl)) HR).
      + exact(source_bounded_in_context_wf M b c n negative y HNegBound (ex_intro _ k0 HC)).
      + exact(source_bounded_in_context_wf M b c n core k HCoreBound (ex_intro _ k0 HC)).
    - apply(native_equal_core_false M u v m env name container matrix x y phi negative empty emptyExists core
        HX HY HPhi HN HE HEE HCore
        (source_named_context_vacuous_cons M b c n negative u v m y HCons HVac HNegVac)).
      + apply full_source_Ctx;[exact(source_bounded_in_context_wf M u v m negative y HNegBound HNew)|].
        apply(proj2(context_member_cons M b c n negative u v m negative HCons)). now left.
      + exact(source_full_weaken_cons M b c n negative u v m emptyExists y HCons HNegBound PEmpty).
    - exact HCons.
    - exact HR. }
  exact(source_full_cases M b c n phi negative core left right HN HL HR PLeft PRight).
Qed.

Theorem native_equal_core_from_empty_host M b c n env name container matrix x y
    phi member host empty emptyExists core :
  code_relation M env name x ->code_relation M env container y ->
  native_named_evaluation M env matrix phi ->source_bounded M phi y ->
  sf_relation M SFMember x y member ->source_named_quantifier M false y member host ->
  source_named_empty M x y empty ->source_named_quantifier M false y empty emptyExists ->
  native_named_evaluation M env (NNT_core name name container matrix) core ->
  source_full_prv M b c n host ->source_full_prv M b c n emptyExists ->source_full_prv M b c n core.
Proof.
  intros HX HY HPhi HPhiBound HM HH HE HEE HCore PHost PEmpty.
  pose proof(source_full_prv_wellformed M b c n host PHost) as(k&HHostBound&HCtx).
  pose proof(source_full_prv_wellformed M b c n emptyExists PEmpty) as(l&HEmptyBound&_).
  destruct HE as(atom&negative&HA&HN&HQ).
  destruct(native_named_evaluation_bounded M env (NNTAtom false name container) member
    (ex_intro _ x (ex_intro _ y (conj HX (conj HY HM))))) as(j&HMemberBound).
  pose proof(source_named_quantifier_is_vacuous M false y member host j HMemberBound HH) as HHostVac.
  assert (EAtom:atom=member) by(exact(sf_relation_functional M SFMember x y atom member HA HM)).
  subst atom.
  assert (HNegativeBound:source_bounded M negative j).
  { apply(proj2(source_bounded_accept_binary M SFImpl member (zeroM M) negative j
      (or_intror(or_intror eq_refl)) HN)). split;[exact HMemberBound|apply source_bounded_accept_falsity]. }
  pose proof(source_named_quantifier_bound M true x negative empty j HNegativeBound HQ) as HEmptyBodyBound.
  pose proof(source_named_quantifier_is_vacuous M false y empty emptyExists j HEmptyBodyBound HEE) as HEmptyVac.
  destruct(sf_relation_total M SFAnd host emptyExists) as(background&HBackground).
  pose proof(source_named_vacuous_binary M SFAnd host emptyExists background y (or_introl eq_refl)
    HBackground HHostVac HEmptyVac) as HBackgroundVac.
  destruct(source_binary_bound_exists M SFAnd host emptyExists background (or_introl eq_refl)
    HBackground (ex_intro _ k HHostBound)(ex_intro _ l HEmptyBound)) as(qb&HBackgroundBound).
  destruct(environment_cons_total M (zeroM M)(zeroM M)(zeroM M) background) as(u&v&m&HCons).
  assert (HBC:context_bounded M u v m qb).
  { apply(proj2(context_bounded_cons M (zeroM M)(zeroM M)(zeroM M) background u v m qb HCons)).
    split;[exact HBackgroundBound|apply context_bounded_empty]. }
  assert (PBG:source_full_prv M u v m background).
  { apply full_source_Ctx;[exists qb;auto|].
    apply(proj2(context_member_cons M (zeroM M)(zeroM M)(zeroM M) background u v m background HCons)). now left. }
  assert (HVC:source_named_context_vacuous M u v m y).
  { intros f HF. apply(proj1(context_member_cons M (zeroM M)(zeroM M)(zeroM M) background u v m f HCons)) in HF.
    destruct HF as[->|HF];[exact HBackgroundVac|]. exfalso. exact(context_empty M (zeroM M)(zeroM M) f HF). }
  assert (PH:source_full_prv M u v m host).
  { apply(full_source_CE1 M u v m host emptyExists background);[|exact PBG|exact HBackground].
    exact(source_wf_binary_left M u v m SFAnd host emptyExists background
      (or_introl eq_refl) HBackground (source_full_prv_wellformed M u v m background PBG)). }
  assert (PE:source_full_prv M u v m emptyExists).
  { apply(full_source_CE2 M u v m host emptyExists background);[|exact PBG|exact HBackground].
    exact(source_wf_binary_right M u v m SFAnd host emptyExists background
      (or_introl eq_refl) HBackground (source_full_prv_wellformed M u v m background PBG)). }
  pose proof(native_equal_core_with_vacuous_context M u v m env name container matrix x y phi member host
    empty emptyExists core HX HY HPhi HPhiBound HM HH
    (ex_intro _ member (ex_intro _ negative (conj HA (conj HN HQ)))) HEE HCore HVC PH PE) as PCore.
  destruct(sf_relation_total M SFImpl background core) as(imp&HImp).
  assert (PImp:source_full_prv M (zeroM M)(zeroM M)(zeroM M) imp).
  { apply(full_source_II M (zeroM M)(zeroM M)(zeroM M) background core imp u v m);
      [|exact PCore|exact HCons|exact HImp].
    destruct(source_binary_bound_exists M SFImpl background core imp (or_intror(or_intror eq_refl)) HImp
      (ex_intro _ qb HBackgroundBound)(native_named_evaluation_bounded M env _ core HCore)) as(bound&HB).
    exists bound;split;[exact HB|apply context_bounded_empty]. }
  exact(source_full_modus_ponens M b c n background core imp HImp
    (source_full_weaken_empty M b c n imp k HCtx PImp)
    (source_full_and_intro M b c n host emptyExists background HBackground PHost PEmpty)).
Qed.

Print Assumptions source_full_cases.
Print Assumptions native_equal_core_from_empty_host.
