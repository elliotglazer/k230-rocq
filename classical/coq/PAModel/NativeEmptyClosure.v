(** An empty carrier has the repeated-active-name closure, independently
    of the arbitrary internal matrix. This is a pure source deduction. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension CodeExpressions
  SetFormulaCodes SourceBounded SourceBoundMonotone NumericalContexts NumericalEnvironments
  NumericalSourceFull SourceSequents SourceTraceBounds SourceContextTransport
  SourceInstantiationConstructors SourceUniversalDistribution SourceProofWeakening SourceDerivedRules
  NativeKBundle NativeNamedRegularity NativeNamedProofRules NativeEqualClosure
  SourceNamedSelfSpecialization SourceNamedQuantifierRules SourceNamedVacuity.
Unset Implicit Arguments.

Definition source_named_empty M x y empty :=exists member negative,
  sf_relation M SFMember x y member /\sf_relation M SFImpl member (zeroM M) negative /\
  source_named_quantifier M true x negative empty.

Theorem source_full_refuted_antecedent M b c n member negative goal out k :
  source_bounded M goal k ->sf_relation M SFImpl member (zeroM M) negative ->
  sf_relation M SFImpl member goal out ->source_full_prv M b c n negative ->
  source_full_prv M b c n out.
Proof.
  intros HG HN HO PN.
  destruct (source_full_prv_wellformed M b c n negative PN) as(l&HBN&HCtx).
  pose proof (proj1 (proj1 (source_bounded_accept_binary M SFImpl member (zeroM M)
    negative l (or_intror(or_intror eq_refl)) HN) HBN)) as HBM.
  destruct (environment_cons_total M b c n member) as(u&v&m&HCons).
  assert (HNew:source_context_finite_bound M u v m).
  { apply (source_context_finite_bound_cons M b c n member u v m
      (ex_intro _ l HCtx)(ex_intro _ l HBM) HCons). }
  assert (PM:source_full_prv M u v m member).
  { apply full_source_Ctx;[apply (source_bounded_in_context_wf M u v m member l HBM HNew)|].
    apply (proj2 (context_member_cons M b c n member u v m member HCons)). now left. }
  assert (PN':source_full_prv M u v m negative).
  { destruct HNew as(q&HQ). apply (source_full_prv_weaken_bounded M b c n u v m negative q PN);[|exact HQ].
    intros f HF. apply (proj2 (context_member_cons M b c n member u v m f HCons)). now right. }
  apply (full_source_II M b c n member goal out u v m).
  - apply (source_wf_binary M b c n SFImpl member goal out (or_intror(or_intror eq_refl)) HO).
    + exists l. auto.
    + apply (source_bounded_in_context_wf M b c n goal k HG). now exists l.
  - apply full_source_Exp.
    + exact (source_bounded_in_context_wf M u v m goal k HG HNew).
    + exact (source_full_modus_ponens M u v m member (zeroM M) negative HN PN' PM).
  - exact HCons.
  - exact HO.
Qed.

Theorem native_empty_closure M env name container matrix x y empty closure imp :
  code_relation M env name x ->code_relation M env container y ->source_named_empty M x y empty ->
  native_named_evaluation M env (NNT_equal_closure name container matrix) closure ->
  sf_relation M SFImpl empty closure imp ->
  source_full_prv M (zeroM M)(zeroM M)(zeroM M) imp.
Proof.
  intros HX HY (member&negative&HM&HN&HEmpty) HC HI.
  assert (HMemberBound:source_bounded M member (succM M (addM M x y))).
  { apply (proj2 (source_bounded_accept_atom M SFMember x y member _ (or_introl eq_refl) HM)).
    split;[apply coding_le_add|rewrite add_comm;apply coding_le_add]. }
  assert (HNegBound:source_bounded M negative (succM M (addM M x y))).
  { apply (proj2 (source_bounded_accept_binary M SFImpl member (zeroM M) negative _
      (or_intror(or_intror eq_refl)) HN)). split;[exact HMemberBound|apply source_bounded_accept_falsity]. }
  pose proof (source_named_quantifier_bound M true x negative empty _ HNegBound HEmpty) as HEB.
  pose proof (source_named_quantifier_is_vacuous M true x negative empty _ HNegBound HEmpty) as HVac.
  destruct(environment_cons_total M (zeroM M)(zeroM M)(zeroM M) empty) as(b&c&n&HCons).
  assert (HCtx:context_bounded M b c n (succM M(addM M x y))).
  { apply (proj2 (context_bounded_cons M (zeroM M)(zeroM M)(zeroM M) empty b c n _ HCons)).
    split;[exact HEB|apply context_bounded_empty]. }
  assert (PE:source_full_prv M b c n empty).
  { apply full_source_Ctx;[exists (succM M(addM M x y));auto|].
    apply (proj2 (context_member_cons M (zeroM M)(zeroM M)(zeroM M) empty b c n empty HCons)). now left. }
  assert (PN:source_full_prv M b c n negative).
  { destruct HEmpty as(rb&rc&body&HB&HR&HQ).
    exact (source_full_named_self_all_elim M b c n negative x rb rc body empty _ HNegBound HB HR HQ PE). }
  assert (HContextVacuous:source_named_context_vacuous M b c n x).
  { intros f HF. apply (proj1(context_member_cons M (zeroM M)(zeroM M)(zeroM M)
      empty b c n f HCons)) in HF. destruct HF as[->|HF];[exact HVac|].
    exfalso. exact(context_empty M (zeroM M)(zeroM M) f HF). }
  assert (PPoint:native_source_proof M b c n env
    (NNTImpl (NNTAtom false name container)
      (NNTEx name (NNTAnd matrix (NNT_equal_rest name container matrix))))).
  { intros out(a&g&(u&v&HU&HV&HA)&HG&HO).
    rewrite(code_relation_functional M name env u x HU HX),
      (code_relation_functional M container env v y HV HY) in HA.
    rewrite(sf_relation_functional M SFMember x y a member HA HM) in HO.
    destruct(native_named_evaluation_bounded M env
      (NNTEx name (NNTAnd matrix (NNT_equal_rest name container matrix))) g HG) as(k&HK).
    exact(source_full_refuted_antecedent M b c n member negative g out k HK HN HO PN). }
  pose proof ((native_source_all_intro M b c n env x name _ HX HContextVacuous PPoint) closure HC) as PClosure.
  apply(full_source_II M (zeroM M)(zeroM M)(zeroM M) empty closure imp b c n);
    [|exact PClosure|exact HCons|exact HI].
  destruct(source_binary_bound_exists M SFImpl empty closure imp (or_intror(or_intror eq_refl)) HI
    (ex_intro _ _ HEB)(native_named_evaluation_bounded M env _ closure HC)) as(bound&HB).
  exists bound. split;[exact HB|apply context_bounded_empty].
Qed.

Print Assumptions native_empty_closure.
