(** Actual open-point extension: the finite cofinal extension law supplies
    one new K-level and a raw subset. The internally finite old member table
    is transported by the checked table theorem, not by an external induction. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension CodeExpressions SetFormulaCodes
 SourceBounded SourceBoundMonotone SourceSequents NumericalContexts NumericalEnvironments NumericalContextRenaming
 NumericalRenaming NumericalInstantiation NumericalSourceFull SourceQuantifierRules SourceProofShiftCons
 SourceContextProofHelpers SourceTraceBounds SourceRelativizationBounds SourceLeastOrdinalWitness
 SourceImplicationAllShift SourceDerivedRules SourceConjunctionRules SourceHierarchySyntax SourceCommonLevelPoint SourceCommonLevelWitness
 SourceCofinalCommonPoint SourceCofinalCommonRecipe SourceCofinalCommonWitness SourceCofinalCommonShift
 SourceCofinalPointShift SourceCofinalCommonExtend SourceCofinalExtensionShell.
Unset Implicit Arguments.
Theorem source_full_cofinal_common_above M b c n k start count Ks Lb d y old target
 ordinals cover oldmember oldlevel newmember exD bodyD bodyY kmem ordinal level pair left subset member right
 tail4 tail3 tail2 tail1 law:
 context_bounded M b c n k ->
 (forall i,coding_lt M i(succM M count) ->coding_lt M(addM M i start)k) ->
 coding_lt M Ks k ->coding_lt M y k ->
 source_cofinal_common_point M start count Ks d y old ->
 source_cofinal_common_recipe M start(succM M count)Ks target ->
 source_cofinal_extension_shell M Ks Lb d y(addM M count start)
 ordinals cover oldmember oldlevel newmember exD bodyD bodyY kmem ordinal level pair left subset member right
 tail4 tail3 tail2 tail1 law ->
 source_full_prv M b c n law ->source_full_prv M b c n ordinals ->source_full_prv M b c n cover ->
 source_full_prv M b c n old ->source_full_prv M b c n newmember ->source_full_prv M b c n target.
Proof.
 intros HC HNames HKs HY HOld HTarget HShell PLaw POrdinals PCover POld PNewMember.
 destruct HShell as(HOrdinals&HCover&HOldMember&HOldLevel&HNewMember&HKMem&HOrdinal&HLevel&HPair&HLeft&
 HSubset&HMember&HRight&HBody&HEx2&HEx1&HImp5&HImp4&HImp3&HImp2&HImp1).
 pose proof HOld as(oldcommon&oldmem&HOldCommon&HOldMem&HOldAnd).
 pose proof(source_full_conjunction_left M b c n oldmem oldcommon old HOldAnd POld)as POldMem.
 pose proof(source_full_conjunction_right M b c n oldmem oldcommon old HOldAnd POld)as POldCommon.
 pose proof(sf_relation_functional M SFMember d Ks oldmem oldmember HOldMem HOldMember)as E. subst oldmem.
 pose proof HOldCommon as(ms&od&ld&pr&HMs&HOd&HLd&HPr&HOC).
 pose proof(source_full_conjunction_left M b c n pr ms oldcommon HOC POldCommon)as PPr.
 pose proof(source_full_conjunction_right M b c n od ld pr HPr PPr)as PLd.
 pose proof(source_LL_instance_functional M d y ld oldlevel HLd HOldLevel)as E. subst ld.
 pose proof(source_full_modus_ponens M b c n ordinals tail1 law HImp1 PLaw POrdinals)as P1.
 pose proof(source_full_modus_ponens M b c n cover tail2 tail1 HImp2 P1 PCover)as P2.
 pose proof(source_full_modus_ponens M b c n oldmember tail3 tail2 HImp3 P2 POldMem)as P3.
 pose proof(source_full_modus_ponens M b c n oldlevel tail4 tail3 HImp4 P3 PLd)as P4.
 pose proof(source_full_modus_ponens M b c n newmember exD tail4 HImp5 P4 PNewMember)as PExD.
 destruct(source_full_prv_wellformed M b c n exD PExD)as(q&HExBound&HQCtx).
 set(t:=addM M k q).
 assert(HKT:coding_lt M k(succM M t))by(unfold t;apply coding_le_add).
 assert(HQT:coding_lt M q(succM M t)).
 { unfold t. rewrite Arithmetic.add_comm. apply coding_le_add. }
 pose proof(context_bounded_monotone M b c n k t HC HKT)as HCT.
 pose proof(source_bounded_monotone M exD q t HExBound HQT)as HExT.
 pose proof(proj1(source_bounded_accept_unary M SFEx bodyD exD t(or_intror eq_refl)HEx1)HExT)as HDBound.
 pose proof(proj1(source_bounded_accept_unary M SFEx bodyY bodyD(succM M t)(or_intror eq_refl)HEx2)HDBound)as HYBound.
 destruct(context_shift_total M b c n)as(sb&sc&HS).
 pose proof(context_shift_preserves_bound M b c n sb sc t HS HCT)as HSC.
 destruct(environment_cons_total M sb sc n bodyD)as(cb&cc&cn&HConsD).
 pose proof(proj2(context_bounded_cons M sb sc n bodyD cb cc cn(succM M t)HConsD)(conj HDBound HSC))as HCC.
 destruct(context_shift_total M cb cc cn)as(tb&tc&HT).
 pose proof(context_shift_preserves_bound M cb cc cn tb tc(succM M t)HT HCC)as HTC.
 destruct(environment_cons_total M tb tc cn bodyY)as(ub&uc&un&HConsY).
 pose proof(proj2(context_bounded_cons M tb tc cn bodyY ub uc un(succM M(succM M t))HConsY)(conj HYBound HTC))as HUC.
 destruct(source_cofinal_common_point_total M(succM M start)count(succM M Ks)(succM M d)(succM M y))as(old1&HOld1).
 destruct(source_cofinal_common_point_total M(succM M(succM M start))count(succM M(succM M Ks))
 (succM M(succM M d))(succM M(succM M y)))as(old2&HOld2).
 pose proof(source_cofinal_common_point_shift M start count Ks d y old old1 HOld HOld1)as HOldShift1.
 pose proof(source_cofinal_common_point_shift M(succM M start)count(succM M Ks)(succM M d)(succM M y)old1 old2 HOld1 HOld2)as HOldShift2.
 pose proof(source_full_prv_shift_cons M b c n sb sc cb cc cn bodyD old old1(succM M t)
 HS HConsD HCC HOldShift1 POld)as POld1.
 pose proof(source_full_prv_shift_cons M cb cc cn tb tc ub uc un bodyY old1 old2(succM M(succM M t))
 HT HConsY HUC HOldShift2 POld1)as POld2.
 pose proof(source_full_cons_head M tb tc cn bodyY ub uc un(succM M(succM M t))HConsY HYBound HUC)as PBodyY.
 pose proof(source_full_conjunction_left M ub uc un left right bodyY HBody PBodyY)as PLeft.
 pose proof(source_full_conjunction_right M ub uc un left right bodyY HBody PBodyY)as PRight.
 pose proof(source_full_conjunction_left M ub uc un pair level left HLeft PLeft)as PPair.
 pose proof(source_full_conjunction_right M ub uc un pair level left HLeft PLeft)as PLevel.
 pose proof(source_full_conjunction_left M ub uc un kmem ordinal pair HPair PPair)as PKMem.
 pose proof(source_full_conjunction_right M ub uc un kmem ordinal pair HPair PPair)as POrdinal.
 pose proof(source_full_conjunction_left M ub uc un subset member right HRight PRight)as PSubset.
 pose proof(source_full_conjunction_right M ub uc un subset member right HRight PRight)as PMember.
 destruct(source_cofinal_common_recipe_total M(succM M start)(succM M count)(succM M Ks))as(target1&HTarget1).
 destruct(source_cofinal_common_recipe_total M(succM M(succM M start))(succM M count)(succM M(succM M Ks)))as(target2&HTarget2).
 pose proof(source_cofinal_common_shift M start(succM M count)Ks target target1 HTarget HTarget1)as HTargetShift1.
 pose proof(source_cofinal_common_shift M(succM M start)(succM M count)(succM M Ks)target1 target2 HTarget1 HTarget2)as HTargetShift2.
 assert(HNamesT:forall i,coding_lt M i(succM M count) ->coding_lt M(addM M i start)t).
 { intros i HI. exact(source_bound_lt_le M(addM M i start)k t(HNames i HI)HKT). }
 assert(HNamesT2:forall i,coding_lt M i(succM M count) ->coding_lt M(addM M i(succM M(succM M start)))(succM M(succM M t))).
 { intros i HI. rewrite !source_common_add_successor. apply(proj2(coding_lt_succ_cancel M(succM M(addM M i start))(succM M t))).
   exact(proj2(coding_lt_succ_cancel M(addM M i start)t)(HNamesT i HI)). }
 assert(HKsT:coding_lt M Ks t)by exact(source_bound_lt_le M Ks k t HKs HKT).
 assert(HKs2:coding_lt M(succM M(succM M Ks))(succM M(succM M t))).
 { apply(proj2(coding_lt_succ_cancel M(succM M Ks)(succM M t))). exact(proj2(coding_lt_succ_cancel M Ks t)HKsT). }
 assert(HY2:coding_lt M(succM M(succM M y))(succM M(succM M t))).
 { apply(proj2(coding_lt_succ_cancel M(succM M y)(succM M t))). apply(proj2(coding_lt_succ_cancel M y t)).
   exact(source_bound_lt_le M y k t HY HKT). }
 assert(HMemberTarget:sf_relation M SFMember(addM M count(succM M(succM M start)))(zeroM M)member).
 { rewrite !source_common_add_successor. exact HMember. }
 pose proof(source_full_cofinal_common_extend_witness M ub uc un(succM M(succM M start))count
 (succM M(succM M Ks))(succM M(succM M d))(succM M(succM M y))old2(code_numeral M 1)(zeroM M)target2
 ordinal level subset member kmem(succM M(succM M t))HNamesT2 HKs2 HY2(coding_zero_lt_succ M(succM M t))HUC
 HOld2 HTarget2 HOrdinal HLevel HSubset HMemberTarget HKMem POld2 POrdinal PLevel PSubset PMember PKMem)as PTarget2.
 pose proof(source_cofinal_common_recipe_bounded M start(succM M count)Ks target t HNamesT HKsT HTarget)as BTarget.
 pose proof(source_shift_bound M target target1 t BTarget HTargetShift1)as BTarget1.
 pose proof(source_full_cons_head M sb sc n bodyD cb cc cn(succM M t)HConsD HDBound HCC)as PBodyD.
 pose proof(full_source_ExE M cb cc cn bodyY bodyD target1 target2 tb tc ub uc un
 (ex_intro _(succM M t)(conj BTarget1 HCC))PBodyD PTarget2 HEx2 HT HConsY HTargetShift2)as PTarget1.
 exact(full_source_ExE M b c n bodyD exD target target1 sb sc cb cc cn
 (ex_intro _ t(conj BTarget HCT))PExD PTarget1 HEx1 HS HConsD HTargetShift1).
Qed.
Print Assumptions source_full_cofinal_common_above.
