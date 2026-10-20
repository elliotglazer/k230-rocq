(** EnvF successor at arbitrary internally coded assignment values.
    The old witness is closed only after all value freshness conditions
    have been stated; no global parameter replacement is used. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions NumericalProofs SetFormulaCodes
 SourceBounded SourceDefinabilityPrimitives SourceDefinabilityStep SourceDefinabilityBounds
 SourceDefinabilityIteration SourceFiniteCutoffShift NumericalEnvironments NumericalRenamingMaps NumericalRenaming
 NumericalSubstitutionMaps NumericalSubstitution SourceDnAssignments SourceDnAssignedMatrix SourceSubstitutionRenaming
 RawBinderRenaming SourceNamedQuantifierRules SourceEnvInClosureConstructor SourceEnvInClosureRoleMaps
 SourceParameterTransport SourceFiniteParameters SourceFiniteParameterProofs SourceParameterIdentityCalibration
 SourceThreeParameterCommutation.
From FOL.Tennenbaum Require Peano.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Theorem source_env_assignment_named_constructor M count environment next pb pc value vb vc
 old ob oc previous new nb nc target extension pair:
 source_envf M count environment ->source_def_step M true environment next ->
 environment_cons M pb pc count value vb vc(succM M count) ->
 environment_cons M pb pc count old ob oc(succM M count) ->
 environment_cons M vb vc(succM M count)new nb nc(succM M(succM M count)) ->
 numerical_substitution M environment ob oc(succM M count)(zeroM M)previous ->
 numerical_substitution M next nb nc(succM M(succM M count))(zeroM M)target ->
 code_relation M(EIC_ext_roles old new value)EIC_ext_expression extension ->
 sf_relation M SFAnd previous extension pair ->old<>new ->value<>old ->
 (forall i v,coding_lt M i count ->beta M pb pc i v ->v<>old) ->
 source_named_quantifier M false old pair target.
Proof.
 intros HE HStep HV HO HN HP HT HExt HPair HON HVO HFresh.
 destruct(source_def_step_graph M true environment next HStep)as(shifted&body&(first&H1&H2)&HBody&HNext).
 apply(proj1(numerical_substitution_quantifier M false body next nb nc
  (succM M(succM M count))(zeroM M)target HNext))in HT.
 destruct HT as(lb&lc&ln&closedbody&HL&HClosed&HEx).
 apply(proj1(numerical_substitution_binary M SFAnd shifted _ body lb lc ln(code_numeral M 1)closedbody
  (or_introl eq_refl)HBody))in HClosed.
 destruct HClosed as(closedprev&closedext&HCPrev&HCExt&HCBody).
 assert(HA:source_dn_assignment M count pb pc new value nb nc).
 { exists vb,vc. auto. }
 destruct(substitution_lift_total M pb pc count(zeroM M))as(ub&uc&un&HU).
 pose proof(source_dn_assigned_matrix M count pb pc new value nb nc lb lc ln ub uc un
  environment first shifted closedprev(source_envf_bound M count environment HE)H1 H2 HA HL HU HCPrev)as HPrevSub.
 destruct(raw_binder_renaming_total M old)as(rb&rc&HRaw).
 destruct(numerical_renaming_total M previous rb rc(succM M old)(code_numeral M 1))as(candidate&HClose).
 assert(HCandidate:numerical_substitution M environment ub uc un(code_numeral M 1)candidate).
 { apply(numerical_substitution_then_renaming M environment(succM M count)
    ob oc(succM M count)(zeroM M)rb rc(succM M old)(code_numeral M 1)
    ub uc un(code_numeral M 1)previous candidate(source_envf_bound M count environment HE)HP HClose).
   intros i j v HI HJ HJR.
   destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)
    as[->|[q ->]].
   - assert(EJ:j=old).
     { apply(proj1(substitution_lookup_inside M ob oc(succM M count)(zeroM M)(zeroM M)j(coding_zero_lt_succ M count)))in HJ.
       apply(proj2(environment_lookup_inside M ob oc(succM M count)(zeroM M)j(coding_zero_lt_succ M count)))in HJ.
       exact(proj1(environment_cons_head M _ _ _ _ _ _ _ _ HO)HJ). }
     subst j. apply(proj1(HRaw old v))in HJR. destruct HJR as[[_ ->]|[HN' _]];[|contradiction].
     exact(proj2(substitution_lift_head M _ _ _ _ _ _ _ _ HU)eq_refl).
   - assert(HQ:coding_lt M q count)by(exact(proj1(coding_lt_succ_cancel M q count)HI)).
     assert(HValue:beta M pb pc q j).
     { apply(proj1(substitution_lookup_inside M ob oc(succM M count)(zeroM M)(succM M q)j HI))in HJ.
       apply(proj2(environment_lookup_inside M ob oc(succM M count)(succM M q)j HI))in HJ.
       apply(proj1(environment_cons_tail M _ _ _ _ _ _ _ _ _ HO))in HJ.
       exact(proj1(environment_lookup_inside M pb pc count q j HQ)HJ). }
     apply(proj1(HRaw j v))in HJR. destruct HJR as[[E _]|[_ ->]].
     + exact(False_rect _(HFresh q j HQ HValue E)).
     + apply(proj2(substitution_lift_tail M _ _ _ _ _ _ _ _ _ HU)).
       exact(proj2(substitution_lookup_inside M pb pc count(zeroM M)q j HQ)HValue). }
 assert(EP:candidate=closedprev)by(eapply numerical_substitution_functional;eassumption). subst candidate.
 destruct(code_relation_total M EIC_ext_expression(EIC_ext_roles(zeroM M)(succM M new)(succM M value)))as(ext&HExtClosed).
 assert(HExtIdentity:code_relation M(fun i=>code_numeral M i)EIC_ext_expression(code_numeral M(sf_encode source_def_extension021))).
 { exact(source_parameter_identity_calibration M source_def_extension021 source_three_parameter_names
    (fun i=>code_numeral M i)ltac:(intros[|[|[|i]]];reflexivity)). }
 assert(HExtSub:numerical_substitution M(code_numeral M(sf_encode source_def_extension021))lb lc ln(code_numeral M 1)ext).
 { apply(source_parameter_transport M 3 source_def_extension021 source_def_extension_bound
    source_three_parameter_names source_three_parameter_names(fun i=>code_numeral M i)
    (EIC_ext_roles(zeroM M)(succM M new)(succM M value))lb lc ln(code_numeral M 1));try assumption.
   intros[|[|[|i]]]x y HI HX HY;try lia;cbn[source_three_parameter_names]in HX,HY.
   - change(x=zeroM M)in HX. change(y=zeroM M)in HY. subst x y.
     exact(proj2(substitution_lift_head M _ _ _ _ _ _ _ _ HL)eq_refl).
   - change(x=code_numeral M 1)in HX. change(y=succM M new)in HY. subst x y.
     apply(proj2(substitution_lift_tail M _ _ _ _ _ _ _ _ _ HL)).
     exact(source_dn_assignment_zero M _ _ _ _ _ _ _ HA).
   - change(x=code_numeral M 2)in HX. change(y=succM M value)in HY. subst x y.
     apply(proj2(substitution_lift_tail M _ _ _ _ _ _ _ _ _ HL)).
     exact(source_dn_assignment_one M _ _ _ _ _ _ _ HA). }
 assert(EC:closedext=ext)by(eapply numerical_substitution_functional;eassumption). subst closedext.
 assert(HExtClose:numerical_renaming M extension rb rc(succM M old)(code_numeral M 1)ext).
 { apply(source_three_parameter_renaming_commutation M source_def_extension021
    (EIC_ext_roles old new value)(EIC_ext_roles(zeroM M)(succM M new)(succM M value))
    extension ext rb rc(succM M old)(code_numeral M 1));try assumption;[exact source_def_extension_bound|].
   intros[|[|[|i]]]HI;try lia;cbn[EIC_ext_roles];apply(proj2(HRaw _ _)).
   - left;auto.
   - right. split;[intro E;exact(HON(eq_sym E))|reflexivity].
   - right;auto. }
 exists rb,rc,closedbody. split;[exact HRaw|]. split;[|exact HEx].
 apply(proj2(numerical_renaming_binary M SFAnd previous extension pair rb rc(succM M old)(code_numeral M 1)closedbody
  (or_introl eq_refl)HPair)). exists closedprev,ext. auto.
Qed.
Print Assumptions source_env_assignment_named_constructor.
