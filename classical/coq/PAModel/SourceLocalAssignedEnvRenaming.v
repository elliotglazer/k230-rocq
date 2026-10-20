(** Arbitrary assigned parameters in the exact EnvF witness map.
    All indices, tables and source codes may be nonstandard. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 NumericalEnvironments NumericalSubstitutionMaps NumericalSubstitution NumericalRenamingMaps NumericalRenaming
 SourceRenamingSquare RenamingSubstitution SourceEnvFScopedHole SourceNamedQuantifierRules SourceNumeralLift.
From FOL.Tennenbaum Require Peano.
Unset Implicit Arguments.
Theorem source_local_assigned_env_witness_renaming M count environment shifted previous pb pc old ob oc container rb rc rn
 member body ex originalbody originalex:
 source_bounded M environment(succM M count) ->source_low_parameter_shift M 3 environment shifted ->
 environment_cons M pb pc count old ob oc(succM M count) ->
 numerical_substitution M environment ob oc(succM M count)(zeroM M)previous ->old<>container ->
 (forall i v,coding_lt M i count ->beta M pb pc i v ->v<>old) ->
 (forall i v,coding_lt M i count ->beta M pb pc i v ->
  renaming_lookup M rb rc rn(zeroM M)(succM M(succM M(succM M i)))v) ->
 renaming_lookup M rb rc rn(zeroM M)(code_numeral M 2)container ->
 sf_relation M SFMember old container member ->sf_relation M SFAnd previous member body ->
 source_named_quantifier M false old body ex ->
 sf_relation M SFAnd shifted(code_numeral M(sf_make SFMember 0 3))originalbody ->
 sf_relation M SFEx originalbody(zeroM M)originalex ->
 numerical_renaming M originalex rb rc rn(zeroM M)ex.
Proof.
 intros BE HL HCons HPrevious OC HFresh HParams HContainer HMember HBody
  (cb&cc&closed&HClose&HClosed&HEx)HOriginal HOriginalEx.
 destruct(proj1(numerical_renaming_binary M SFAnd previous member body cb cc(succM M old)(code_numeral M 1)
  closed(or_introl eq_refl)HBody)HClosed)as(cp&cm&HCP&HCM&HClosedBody).
 destruct(renaming_lift_total M rb rc rn(zeroM M))as(lb&lc&ln&HLift).
 assert(HPreviousRen:numerical_renaming M shifted lb lc ln(zeroM M)cp).
 { apply(proj2(numerical_renaming_substitution M shifted lb lc ln(zeroM M)cp)).
   apply(numerical_source_renaming_square M environment(succM M count)
    ob oc(succM M count)(zeroM M)
    (zeroM M)(zeroM M)(code_numeral M 1)(code_numeral M 3)
    cb cc(succM M old)(code_numeral M 1)
    lb lc ln(addM M ln(zeroM M))previous shifted cp BE HPrevious HL HCP).
   intros i j q m HI HJ HJM HQ.
   apply(proj1(renaming_substitution_lookup M lb lc ln(zeroM M)q m)).
   destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)as[->|[v ->]].
   - assert(HJO:substitution_lookup M ob oc(succM M count)(zeroM M)(zeroM M)old).
     { apply(proj2(substitution_lookup_inside M ob oc(succM M count)(zeroM M)(zeroM M)old(coding_zero_lt_succ M count))).
       apply(proj1(environment_lookup_inside M ob oc(succM M count)(zeroM M)old(coding_zero_lt_succ M count))).
       exact(proj2(environment_cons_head M pb pc count old ob oc(succM M count)old HCons)eq_refl). }
     rewrite(substitution_lookup_functional M _ _ _ _ _ j old HJ HJO)in HJM.
     apply(proj1(HClose old m))in HJM. destruct HJM as[[_ ->]|[H _]];[|contradiction].
     rewrite(renaming_lookup_functional M _ _ _ _ _ q(zeroM M)HQ(low_parameter_lookup_zero M 3)).
     exact(proj2(renaming_lift_head M rb rc rn(zeroM M)lb lc ln(zeroM M)HLift)eq_refl).
   - pose proof(proj1(coding_lt_succ_cancel M v count)HI)as HV.
     apply(proj1(substitution_lookup_inside M ob oc(succM M count)(zeroM M)(succM M v)j HI))in HJ.
     apply(proj2(environment_lookup_inside M ob oc(succM M count)(succM M v)j HI))in HJ.
     apply(proj1(environment_cons_tail M pb pc count old ob oc(succM M count)v j HCons))in HJ.
     apply(proj1(environment_lookup_inside M pb pc count v j HV))in HJ.
     apply(proj1(HClose j m))in HJM. destruct HJM as[[E _]|[_ ->]];[exfalso;exact(HFresh v j HV HJ E)|].
     assert(HNZ:succM M v<>zeroM M)by(exact(fun E=>Model.zero_ne_succ M v(eq_sym E))).
     rewrite(renaming_lookup_functional M _ _ _ _ _ q _ HQ(low_parameter_lookup_nonzero M 3(succM M v)HNZ)).
     replace(addM M(succM M v)(code_numeral M 3))with(succM M(succM M(succM M(succM M v)))).
     2:{ rewrite Arithmetic.add_comm. cbn[code_numeral]. now rewrite!Arithmetic.add_succ,Arithmetic.add_zero. }
     exact(proj2(renaming_lift_tail M rb rc rn(zeroM M)lb lc ln(succM M(succM M(succM M v)))j HLift)(HParams v j HV HJ)). }
 assert(HMem:numerical_renaming M(code_numeral M(sf_make SFMember 0 3))lb lc ln(zeroM M)cm).
 { destruct(proj1(numerical_renaming_member M old container member cb cc(succM M old)(code_numeral M 1)cm HMember)HCM)
    as(x&y&HX&HY&HM).
   apply(proj1(HClose old x))in HX. destruct HX as[[_ ->]|[H _]];[|contradiction].
   apply(proj1(HClose container y))in HY. destruct HY as[[E _]|[_ ->]];[exfalso;exact(OC(eq_sym E))|].
   apply(proj2(numerical_renaming_member M(zeroM M)(code_numeral M 3)
    (code_numeral M(sf_make SFMember 0 3))lb lc ln(zeroM M)cm(sf_make_numeral M SFMember 0 3))).
   exists(zeroM M),(succM M container). split.
   - exact(proj2(renaming_lift_head M rb rc rn(zeroM M)lb lc ln(zeroM M)HLift)eq_refl).
   - split;[|exact HM]. exact(proj2(renaming_lift_tail M rb rc rn(zeroM M)lb lc ln(code_numeral M 2)container HLift)HContainer). }
 apply(proj2(numerical_renaming_quantifier M false originalbody originalex rb rc rn(zeroM M)ex HOriginalEx)).
 exists lb,lc,ln,closed. split;[exact HLift|]. split;[|exact HEx].
 apply(proj2(numerical_renaming_binary M SFAnd shifted(code_numeral M(sf_make SFMember 0 3))originalbody
  lb lc ln(zeroM M)closed(or_introl eq_refl)HOriginal)). exists cp,cm. auto.
Qed.
Print Assumptions source_local_assigned_env_witness_renaming.
