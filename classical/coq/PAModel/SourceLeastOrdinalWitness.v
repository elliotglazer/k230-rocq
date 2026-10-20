(** Actual successor-container and Separation existential elimination for
    the least-ordinal argument. The ambient axiom context is closed; all
    varying formulas, proof codes and parameter counts may be internal. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  SetFormulaCodes SetSchemaConstructors SourceBounded SourceBoundMonotone
  NumericalContexts NumericalEnvironments NumericalContextRenaming NumericalRenaming
  NumericalInstantiation NumericalSourceFull SourceSequents SourceQuantifierRules
  SourceInstantiationConstructors SourceProofWeakening SourceContextTransport
  SourceClosedContextShift SourceTraceBounds SourceDomainInstances SourceImplicationAllShift
  SourceOrdinalPredicate SourceLeastOrdinalGoal SourceLeastOrdinalShift
  SourceFiniteCutoffShift SourceCutoffInstantiation SourceFilteredProfileShift
  SourceLeastOrdinalFixed SourceSuccessorContainerShell SourceSeparationZeroSpecialization
  SourcePropositionalTemplates SourceFilteredMinimumPrograms SchemaConstructorBounds
  SourceCanonicalFilteredMinimum SourceFilterToLeast SourceSeparationFilterShell.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate source_ordinal_predicate_code.

Lemma source_formula_shift_conjunction M x y f x' y' f' :
  sf_relation M SFAnd x y f ->sf_relation M SFAnd x' y' f' ->
  source_formula_shift M x x' ->source_formula_shift M y y' ->source_formula_shift M f f'.
Proof.
  intros HF HF' HX HY.
  apply (proj2 (numerical_renaming_binary M SFAnd x y f (zeroM M) (zeroM M)
    (zeroM M) (code_numeral M 1) f' (or_introl eq_refl) HF)).
  exists x',y'. repeat split;assumption.
Qed.

Lemma source_cons_tail_inclusion M b c n head d e l :
  environment_cons M b c n head d e l ->context_included M b c n d e l.
Proof.
  intros H f HF. apply (proj2 (context_member_cons M b c n head d e l f H)). now right.
Qed.

Lemma source_canonical_profile_bound M phi s a profile k :
  coding_lt M s k ->coding_lt M a k ->source_bounded M phi (succM M k) ->
  code_relation M (canonical_filter_environment phi s a) canonical_filter_profile profile ->
  source_bounded M profile k.
Proof.
  intros HS HA HB HG.
  destruct (canonical_filter_profile_split M phi s a profile HG)
    as (point&smem&amem&HAll&HSmem&HAmem&HPoint).
  apply (proj2 (source_bounded_accept_unary M SFAll point profile k (or_introl eq_refl) HAll)).
  apply (source_prop_template_bound M (schema_env3 smem amem phi)
    filtered_minimum_profile (succM M k));[|exact HPoint].
  intros [|[|index]];cbn [schema_env3];try assumption.
  - apply (proj2 (source_bounded_accept_atom M SFMember _ _ smem _ (or_introl eq_refl) HSmem)).
    split;[apply coding_zero_lt_succ|exact (proj2 (coding_lt_succ_cancel M s k) HS)].
  - apply (proj2 (source_bounded_accept_atom M SFMember _ _ amem _ (or_introl eq_refl) HAmem)).
    split;[apply coding_zero_lt_succ|exact (proj2 (coding_lt_succ_cancel M a k) HA)].
Qed.

Theorem source_full_least_ordinal_witness M b c n count phi p1 p2 p3
    successorlaw ordinallaw regularlaw specialized body implication target :
  context_bounded M b c n (zeroM M) ->source_bounded M phi (succM M count) ->
  source_cutoff_shift M 1 phi p1 ->source_cutoff_shift M 1 p1 p2 ->
  source_cutoff_shift M 1 p2 p3 ->source_least_ordinal_graph M p1 target ->
  code_relation M (fun _=>zeroM M) (least_fixed_parameter_expression LeastSuccessorContainer) successorlaw ->
  code_relation M (fun _=>code_numeral M 1) (least_fixed_parameter_expression LeastOrdinalMember) ordinallaw ->
  code_relation M (schema_env3 (zeroM M) (code_numeral M 2) (zeroM M))
    (least_fixed_parameter_expression LeastRegularMinimum) regularlaw ->
  code_relation M (fun _=>p3) (E_separation_zero (CEvar 0)) specialized ->
  sf_relation M SFAnd (source_ordinal_predicate_code M) phi body ->
  sf_relation M SFImpl body target implication ->
  source_full_prv M b c n successorlaw ->source_full_prv M b c n ordinallaw ->
  source_full_prv M b c n regularlaw ->source_full_prv M b c n specialized ->
  source_full_prv M b c n implication.
Proof.
  intros HC HB HP1 HP2 HP3 HG HSuc HOrd HReg HSep HBody HImp PSuc POrd PReg PSep.
  pose proof (source_cutoff_shift_bounded M 1 phi p1 count HB HP1) as HB1.
  pose proof (source_cutoff_shift_bounded M 1 p1 p2 (succM M count) HB1 HP2) as HB2.
  pose proof (source_cutoff_shift_bounded M 1 p2 p3 (succM M (succM M count)) HB2 HP3) as HB3.
  pose proof (source_least_ordinal_bound M p1 target (succM M count) HB1 HG) as HT.
  assert (HC0:context_bounded M b c n (succM M count)).
  { exact (context_bounded_monotone M b c n (zeroM M) (succM M count) HC
      (coding_zero_lt_succ M (succM M count))). }
  assert (HOrd0:source_bounded M (source_ordinal_predicate_code M) (succM M count)).
  { exact (source_domain_instance_bound M _ (zeroM M) _ (succM M count)
      (source_ordinal_predicate_bounded M) (coding_zero_lt_succ M count)
      (source_domain_instance_zero M _ (source_ordinal_predicate_bounded M))). }
  assert (HBod:source_bounded M body (succM M count)).
  { exact (proj2 (source_bounded_accept_binary M SFAnd _ _ body _ (or_introl eq_refl) HBody)
      (conj HOrd0 HB)). }
  assert (HImpl:source_bounded M implication (succM M count)).
  { exact (proj2 (source_bounded_accept_binary M SFImpl body target implication _
      (or_intror (or_intror eq_refl)) HImp) (conj HBod HT)). }
  pose proof (source_closed_context_shift_self M b c n HC) as HSelf.
  destruct (source_successor_container_shell M (fun _=>zeroM M) successorlaw HSuc)
    as (ord0&container&containerbody&member10&HOrdZero&HSuccessor&HContainer&HContainerBody&HMember10).
  pose proof (numerical_instantiation_functional M _ (zeroM M) ord0
    (source_ordinal_predicate_code M) HOrdZero
    (source_domain_instance_zero M _ (source_ordinal_predicate_bounded M))) as EOrd0.
  subst ord0.
  destruct (source_separation_filter_shell M p3 specialized HSep) as (profile&HSeparation&HProfile).
  destruct (numerical_renaming_total M phi (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1)) as (f1&HF1).
  destruct (numerical_renaming_total M f1 (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1)) as (f2&HF2).
  destruct (numerical_renaming_total M (source_ordinal_predicate_code M)
    (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1)) as (ord1&HO1).
  destruct (numerical_renaming_total M ord1 (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1)) as (ord2&HO2).
  destruct (sf_relation_total M SFAnd ord1 f1) as (body1&HBody1).
  destruct (sf_relation_total M SFAnd ord2 f2) as (body2&HBody2).
  pose proof (source_formula_shift_conjunction M _ _ body _ _ body1 HBody HBody1 HO1 HF1) as HBodyShift1.
  pose proof (source_formula_shift_conjunction M _ _ body1 _ _ body2 HBody1 HBody2 HO2 HF2) as HBodyShift2.
  destruct (sf_relation_total M SFMember (code_numeral M 2) (code_numeral M 1)) as (member21&HMember21).
  assert (HMemberShift:source_formula_shift M member10 member21).
  { apply (proj2 (numerical_renaming_member M (code_numeral M 1) (zeroM M) member10
      (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1) member21 HMember10)).
    exists (code_numeral M 2),(code_numeral M 1). split;[apply source_shift_map_lookup|].
    split;[apply source_shift_map_lookup|exact HMember21]. }
  destruct (sf_relation_total M SFAnd ord1 member21) as (containerbody1&HContainerBody1).
  pose proof (source_formula_shift_conjunction M _ _ containerbody _ _ containerbody1
    HContainerBody HContainerBody1 HO1 HMemberShift) as HContainerBodyShift.
  destruct (numerical_renaming_total M target (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1)) as (target1&HTarget1).
  destruct (numerical_renaming_total M target1 (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1)) as (target2&HTarget2).
  pose proof (source_least_ordinal_shift M p1 p2 target target1 (succM M (succM M count))
    HB1 HP2 HG HTarget1) as HG1.
  pose proof (source_least_ordinal_shift M p2 p3 target1 target2 (succM M (succM M (succM M count)))
    HB2 HP3 HG1 HTarget2) as HG2.
  pose proof (source_shift_bound M body body1 (succM M count) HBod HBodyShift1) as HBod1.
  pose proof (source_shift_bound M body1 body2 (succM M (succM M count)) HBod1 HBodyShift2) as HBod2.
  pose proof (source_least_ordinal_bound M p2 target1 (succM M (succM M count)) HB2 HG1) as HT1.
  pose proof (source_domain_instance_shift M _ (zeroM M) _ ord1
    (source_ordinal_predicate_bounded M)
    (source_domain_instance_zero M _ (source_ordinal_predicate_bounded M)) HO1) as HOrdOne.
  pose proof (source_cutoff_thrice_specialization_two M phi p1 p2 p3 f1 f2 count
    HB HP1 HP2 HP3 HF1 HF2) as HPhiTwo.
  assert (HContainerBodyBound:source_bounded M containerbody (succM M (succM M count))).
  { apply (proj2 (source_bounded_accept_binary M SFAnd _ _ containerbody _
      (or_introl eq_refl) HContainerBody)). split.
    - exact (source_domain_instance_bound M _ (zeroM M) _ (succM M (succM M count))
        (source_ordinal_predicate_bounded M) (coding_zero_lt_succ M (succM M count))
        (source_domain_instance_zero M _ (source_ordinal_predicate_bounded M))).
    - apply (proj2 (source_bounded_accept_atom M SFMember _ _ member10 _ (or_introl eq_refl) HMember10)).
      split;[|apply coding_zero_lt_succ]. schema_small_index. }
  pose proof (source_shift_bound M containerbody containerbody1
    (succM M (succM M count)) HContainerBodyBound HContainerBodyShift) as HContainerBodyBound1.
  assert (HProfileBound:source_bounded M profile (succM M (succM M (succM M count)))).
  { apply (source_canonical_profile_bound M p3 (zeroM M) (code_numeral M 1) profile
      (succM M (succM M (succM M count))));try assumption;schema_small_index. }
  (* Build all three branch contexts over the same closed axiom table. *)
  destruct (environment_cons_total M b c n body) as (u0&v0&n0&HC0Cons).
  destruct (environment_cons_total M b c n body1) as (u1&v1&n1&HC1Cons).
  assert (En1:n1=n0) by (rewrite (proj1 HC1Cons),(proj1 HC0Cons);reflexivity). subst n1.
  destruct (environment_cons_total M b c n body2) as (u2&v2&n2&HC2Cons).
  assert (En2:n2=n0) by (rewrite (proj1 HC2Cons),(proj1 HC0Cons);reflexivity). subst n2.
  pose proof (context_renaming_cons M b c n (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1)
    b c body body1 u0 v0 n0 u1 v1 HSelf HBodyShift1 HC0Cons HC1Cons) as HContextShift0.
  pose proof (context_renaming_cons M b c n (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1)
    b c body1 body2 u1 v1 n0 u2 v2 HSelf HBodyShift2 HC1Cons HC2Cons) as HContextShift1.
  destruct (environment_cons_total M u1 v1 n0 containerbody) as (a0&a1&an&HACons).
  destruct (environment_cons_total M u2 v2 n0 containerbody1) as (sa0&sa1&san&HSACons).
  assert (Ens:san=an) by (rewrite (proj1 HSACons),(proj1 HACons);reflexivity). subst san.
  pose proof (context_renaming_cons M u1 v1 n0 (zeroM M) (zeroM M) (zeroM M) (code_numeral M 1)
    u2 v2 containerbody containerbody1 a0 a1 an sa0 sa1 HContextShift1 HContainerBodyShift
    HACons HSACons) as HContextShiftA.
  destruct (environment_cons_total M sa0 sa1 an profile) as (s0&s1&sn&HSCons).
  assert (HCInitial:context_bounded M u0 v0 n0 (succM M count)).
  { exact (proj2 (context_bounded_cons M b c n body u0 v0 n0 _ HC0Cons) (conj HBod HC0)). }
  pose proof (context_shift_preserves_bound M u0 v0 n0 u1 v1 (succM M count)
    HContextShift0 HCInitial) as HCShift0.
  assert (HCA:context_bounded M a0 a1 an (succM M (succM M count))).
  { exact (proj2 (context_bounded_cons M u1 v1 n0 containerbody a0 a1 an _ HACons)
      (conj HContainerBodyBound HCShift0)). }
  pose proof (context_shift_preserves_bound M a0 a1 an sa0 sa1
    (succM M (succM M count)) HContextShiftA HCA) as HCAShift.
  assert (HCS:context_bounded M s0 s1 sn (succM M (succM M (succM M count)))).
  { exact (proj2 (context_bounded_cons M sa0 sa1 an profile s0 s1 sn _ HSCons)
      (conj HProfileBound HCAShift)). }
  assert (IInitial:context_included M b c n u0 v0 n0) by exact (source_cons_tail_inclusion M _ _ _ _ _ _ _ HC0Cons).
  assert (IA:context_included M b c n a0 a1 an).
  { intros f HF. apply (source_cons_tail_inclusion M _ _ _ _ _ _ _ HACons f).
    exact (source_cons_tail_inclusion M _ _ _ _ _ _ _ HC1Cons f HF). }
  assert (IS:context_included M b c n s0 s1 sn).
  { intros f HF. apply (source_cons_tail_inclusion M _ _ _ _ _ _ _ HSCons f).
    apply (source_cons_tail_inclusion M _ _ _ _ _ _ _ HSACons f).
    exact (source_cons_tail_inclusion M _ _ _ _ _ _ _ HC2Cons f HF). }
  assert (PBody:source_full_prv M u0 v0 n0 body).
  { apply full_source_Ctx;[exists (succM M count);auto|].
    apply (proj2 (context_member_cons M b c n body u0 v0 n0 body HC0Cons)). now left. }
  assert (PContainer:source_full_prv M u0 v0 n0 container).
  { apply (full_source_IE M u0 v0 n0 (source_ordinal_predicate_code M) container successorlaw).
    - exact (source_wf_binary_right M u0 v0 n0 SFImpl _ _ successorlaw
        (or_intror (or_intror eq_refl)) HSuccessor
        (source_full_prv_wellformed M u0 v0 n0 successorlaw
          (source_full_prv_weaken_bounded M b c n u0 v0 n0 _ _ PSuc IInitial HCInitial))).
    - exact (source_full_prv_weaken_bounded M b c n u0 v0 n0 _ _ PSuc IInitial HCInitial).
    - exact (full_source_CE1 M u0 v0 n0 _ phi body (ex_intro _ (succM M count) (conj HOrd0 HCInitial)) PBody HBody).
    - exact HSuccessor. }
  assert (PProfile:source_full_prv M s0 s1 sn profile).
  { apply full_source_Ctx;[exists (succM M (succM M (succM M count)));auto|].
    apply (proj2 (context_member_cons M sa0 sa1 an profile s0 s1 sn profile HSCons)). now left. }
  assert (PContainerBody:source_full_prv M s0 s1 sn containerbody1).
  { apply full_source_Ctx;[exists (succM M (succM M (succM M count)));auto|].
    apply (source_cons_tail_inclusion M _ _ _ _ _ _ _ HSCons).
    apply (proj2 (context_member_cons M u2 v2 n0 containerbody1 sa0 sa1 an containerbody1 HSACons)). now left. }
  assert (PBody2:source_full_prv M s0 s1 sn body2).
  { apply full_source_Ctx;[exists (succM M (succM M (succM M count)));auto|].
    apply (source_cons_tail_inclusion M _ _ _ _ _ _ _ HSCons).
    apply (source_cons_tail_inclusion M _ _ _ _ _ _ _ HSACons).
    apply (proj2 (context_member_cons M b c n body2 u2 v2 n0 body2 HC2Cons)). now left. }
  assert (PLeast2:source_full_prv M s0 s1 sn target2).
  { apply (source_full_filter_to_least M s0 s1 sn (succM M (succM M (succM M count)))
      (zeroM M) (code_numeral M 1) (code_numeral M 2) p3 f2 ord1 ordinallaw regularlaw
      profile member21 target2);try assumption;try schema_small_index.
    - exact (full_source_CE1 M s0 s1 sn ord1 member21 containerbody1
        (source_wf_binary_left M s0 s1 sn SFAnd ord1 member21 containerbody1
          (or_introl eq_refl) HContainerBody1 (source_full_prv_wellformed M s0 s1 sn containerbody1 PContainerBody))
        PContainerBody HContainerBody1).
    - exact (source_full_prv_weaken_bounded M b c n s0 s1 sn _ _ POrd IS HCS).
    - exact (source_full_prv_weaken_bounded M b c n s0 s1 sn _ _ PReg IS HCS).
    - exact (full_source_CE2 M s0 s1 sn ord1 member21 containerbody1
        (source_wf_binary_right M s0 s1 sn SFAnd ord1 member21 containerbody1
          (or_introl eq_refl) HContainerBody1 (source_full_prv_wellformed M s0 s1 sn containerbody1 PContainerBody))
        PContainerBody HContainerBody1).
    - exact (full_source_CE2 M s0 s1 sn ord2 f2 body2
        (source_wf_binary_right M s0 s1 sn SFAnd ord2 f2 body2
          (or_introl eq_refl) HBody2 (source_full_prv_wellformed M s0 s1 sn body2 PBody2)) PBody2 HBody2). }
  assert (PLeast1:source_full_prv M a0 a1 an target1).
  { exact (full_source_ExE M a0 a1 an profile specialized target1 target2 sa0 sa1 s0 s1 sn
      (ex_intro _ (succM M (succM M count)) (conj HT1 HCA))
      (source_full_prv_weaken_bounded M b c n a0 a1 an _ _ PSep IA HCA)
      PLeast2 HSeparation HContextShiftA HSCons HTarget2). }
  assert (PLeast:source_full_prv M u0 v0 n0 target).
  { exact (full_source_ExE M u0 v0 n0 containerbody container target target1 u1 v1 a0 a1 an
      (ex_intro _ (succM M count) (conj HT HCInitial)) PContainer PLeast1 HContainer
      HContextShift0 HACons HTarget1). }
  exact (full_source_II M b c n body target implication u0 v0 n0
    (ex_intro _ (succM M count) (conj HImpl HC0)) PLeast HC0Cons HImp).
Qed.

Print Assumptions source_formula_shift_conjunction.
Print Assumptions source_cons_tail_inclusion.
Print Assumptions source_full_least_ordinal_witness.
