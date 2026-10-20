(** Complete four-witness cofinal common-level successor in the ordinary
    numerical source calculus. The sole finite law is the actual proved one. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
 SourceBounded SourceSequents NumericalContexts NumericalEnvironments NumericalContextRenaming NumericalRenaming
 NumericalInstantiation NumericalSourceFull SourceQuantifierRules SourceProofWeakening SourceProofShiftCons
 SourceContextTransport SourceContextProofHelpers SourceClosedContextShift SourceLeastOrdinalWitness SourceImplicationAllShift
 SourceCommonLevelWitness SourceCofinalGeometry SourceCofinalCommonPoint SourceCofinalCommonRecipe
 SourceCofinalCommonWitness SourceCofinalCommonShift SourceCofinalExtensionShell SourceCofinalSuccessorLaws SourceCofinalCommonAbove
 SourceRecursionAtomicShift.
Unset Implicit Arguments.
Theorem source_full_cofinal_common_successor M b c n ab ac an k start count Ks Lb old newmember target ordinals cover law:
 context_bounded M b c n k ->context_bounded M ab ac an(zeroM M) ->context_included M ab ac an b c n ->
 (forall i,coding_lt M i(succM M count) ->coding_lt M(addM M i start)k) ->coding_lt M Ks k ->
 source_cofinal_common_recipe M start count Ks old ->sf_relation M SFMember(addM M count start)Lb newmember ->
 source_cofinal_common_recipe M start(succM M count)Ks target ->
 source_cofinal_ordinals M Ks ordinals ->source_cofinal_cover M Ks Lb cover ->source_cofinal_successor_law M start count Ks Lb law ->
 source_full_prv M ab ac an law ->source_full_prv M b c n ordinals ->source_full_prv M b c n cover ->
 source_full_prv M b c n old ->source_full_prv M b c n newmember ->source_full_prv M b c n target.
Proof.
 intros HC HAC HIncl HNames HKs HOld HNew HTarget HOrd HCover HLaws PLaw POrd PCover POld PNew.
 destruct HLaws as(ord2&cover2&oldmember&oldlevel&new2&exD&bodyD&bodyY&kmem&ordinal&level&pair&left&subset&member&right&tail4&tail3&tail2&tail1&HShell).
 pose proof HShell as(HOrd2&HCover2&HOldMem&HOldLevel&HNew2&_).
 destruct HOld as(matrix&exY&HM&HY&HTop).
 assert(HOld:source_cofinal_common_recipe M start count Ks old)by(exists matrix,exY;auto).
 assert(HNamesPrefix:forall i,coding_lt M i count ->coding_lt M(addM M i start)k).
 { intros i HI. exact(HNames i(coding_lt_trans M i count(succM M count)HI(coding_lt_succ M count))). }
 pose proof(source_cofinal_common_recipe_bounded M start count Ks old k HNamesPrefix HKs HOld)as BOld.
 pose proof(proj1(source_bounded_accept_unary M SFEx exY old k(or_intror eq_refl)HTop)BOld)as BExY.
 pose proof(proj1(source_bounded_accept_unary M SFEx matrix exY(succM M k)(or_intror eq_refl)HY)BExY)as BMatrix.
 destruct(context_shift_total M b c n)as(sb&sc&HS).
 pose proof(context_shift_preserves_bound M b c n sb sc k HS HC)as HSC.
 destruct(environment_cons_total M sb sc n exY)as(cb&cc&cn&HConsD).
 pose proof(proj2(context_bounded_cons M sb sc n exY cb cc cn(succM M k)HConsD)(conj BExY HSC))as HCC.
 destruct(context_shift_total M cb cc cn)as(tb&tc&HT).
 pose proof(context_shift_preserves_bound M cb cc cn tb tc(succM M k)HT HCC)as HTC.
 destruct(environment_cons_total M tb tc cn matrix)as(ub&uc&un&HConsY).
 pose proof(proj2(context_bounded_cons M tb tc cn matrix ub uc un(succM M(succM M k))HConsY)(conj BMatrix HTC))as HUC.
 pose proof(source_closed_context_shift_self M ab ac an HAC)as HAxShift.
 pose proof(source_context_included_shift M ab ac an b c n ab ac sb sc HIncl HAxShift HS)as HInclS.
 assert(HInclC:context_included M ab ac an cb cc cn).
 { intros f HF. exact(source_cons_tail_inclusion M sb sc n exY cb cc cn HConsD f(HInclS f HF)). }
 pose proof(source_context_included_shift M ab ac an cb cc cn ab ac tb tc HInclC HAxShift HT)as HInclT.
 assert(HInclU:context_included M ab ac an ub uc un).
 { intros f HF. exact(source_cons_tail_inclusion M tb tc cn matrix ub uc un HConsY f(HInclT f HF)). }
 pose proof(source_full_prv_weaken_bounded M ab ac an ub uc un law(succM M(succM M k))PLaw HInclU HUC)as PLawU.
 destruct(source_cofinal_ordinals_total M(succM M Ks))as(ord1&HOrd1).
 destruct(source_cofinal_cover_total M(succM M Ks)(succM M Lb))as(cover1&HCover1).
 pose proof(source_cofinal_ordinals_shift M Ks ordinals ord1 HOrd HOrd1)as HOrdS1.
 pose proof(source_cofinal_ordinals_shift M(succM M Ks)ord1 ord2 HOrd1 HOrd2)as HOrdS2.
 pose proof(source_cofinal_cover_shift M Ks Lb cover cover1 HCover HCover1)as HCoverS1.
 pose proof(source_cofinal_cover_shift M(succM M Ks)(succM M Lb)cover1 cover2 HCover1 HCover2)as HCoverS2.
 pose proof(source_full_prv_shift_cons M b c n sb sc cb cc cn exY ordinals ord1(succM M k)HS HConsD HCC HOrdS1 POrd)as POrd1.
 pose proof(source_full_prv_shift_cons M cb cc cn tb tc ub uc un matrix ord1 ord2(succM M(succM M k))HT HConsY HUC HOrdS2 POrd1)as POrd2.
 pose proof(source_full_prv_shift_cons M b c n sb sc cb cc cn exY cover cover1(succM M k)HS HConsD HCC HCoverS1 PCover)as PCover1.
 pose proof(source_full_prv_shift_cons M cb cc cn tb tc ub uc un matrix cover1 cover2(succM M(succM M k))HT HConsY HUC HCoverS2 PCover1)as PCover2.
 destruct(sf_relation_total M SFMember(succM M(addM M count start))(succM M Lb))as(new1&HNew1).
 assert(HNew2':sf_relation M SFMember(succM M(succM M(addM M count start)))(succM M(succM M Lb))new2).
 { rewrite <- !source_common_add_successor. exact HNew2. }
 pose proof(source_rec_member_shift M(addM M count start)Lb newmember new1 HNew HNew1)as HNewS1.
 pose proof(source_rec_member_shift M(succM M(addM M count start))(succM M Lb)new1 new2 HNew1 HNew2')as HNewS2.
 pose proof(source_full_prv_shift_cons M b c n sb sc cb cc cn exY newmember new1(succM M k)HS HConsD HCC HNewS1 PNew)as PNew1.
 pose proof(source_full_prv_shift_cons M cb cc cn tb tc ub uc un matrix new1 new2(succM M(succM M k))HT HConsY HUC HNewS2 PNew1)as PNew2.
 pose proof(source_full_cons_head M tb tc cn matrix ub uc un(succM M(succM M k))HConsY BMatrix HUC)as PMatrix.
 destruct(source_cofinal_common_recipe_total M(succM M start)(succM M count)(succM M Ks))as(target1&HTarget1).
 destruct(source_cofinal_common_recipe_total M(succM M(succM M start))(succM M count)(succM M(succM M Ks)))as(target2&HTarget2).
 pose proof(source_cofinal_common_shift M start(succM M count)Ks target target1 HTarget HTarget1)as HTargetS1.
 pose proof(source_cofinal_common_shift M(succM M start)(succM M count)(succM M Ks)target1 target2 HTarget1 HTarget2)as HTargetS2.
 assert(HNames2:forall i,coding_lt M i(succM M count) ->coding_lt M(addM M i(succM M(succM M start)))(succM M(succM M k))).
 { intros i HI. rewrite !source_common_add_successor. apply(proj2(coding_lt_succ_cancel M(succM M(addM M i start))(succM M k))).
   exact(proj2(coding_lt_succ_cancel M(addM M i start)k)(HNames i HI)). }
 assert(HKs2:coding_lt M(succM M(succM M Ks))(succM M(succM M k))).
 { apply(proj2(coding_lt_succ_cancel M(succM M Ks)(succM M k))). exact(proj2(coding_lt_succ_cancel M Ks k)HKs). }
 pose proof(source_full_cofinal_common_above M ub uc un(succM M(succM M k))(succM M(succM M start))count
 (succM M(succM M Ks))(succM M(succM M Lb))(code_numeral M 1)(zeroM M)matrix target2
 ord2 cover2 oldmember oldlevel new2 exD bodyD bodyY kmem ordinal level pair left subset member right tail4 tail3 tail2 tail1 law
 HUC HNames2 HKs2(coding_zero_lt_succ M(succM M k))HM HTarget2 HShell PLawU POrd2 PCover2 PMatrix PNew2)as PTarget2.
 pose proof(source_cofinal_common_recipe_bounded M start(succM M count)Ks target k HNames HKs HTarget)as BTarget.
 pose proof(source_shift_bound M target target1 k BTarget HTargetS1)as BTarget1.
 pose proof(source_full_cons_head M sb sc n exY cb cc cn(succM M k)HConsD BExY HCC)as PExY.
 pose proof(full_source_ExE M cb cc cn matrix exY target1 target2 tb tc ub uc un
 (ex_intro _(succM M k)(conj BTarget1 HCC))PExY PTarget2 HY HT HConsY HTargetS2)as PTarget1.
 exact(full_source_ExE M b c n exY old target target1 sb sc cb cc cn
 (ex_intro _ k(conj BTarget HC))POld PTarget1 HTop HS HConsD HTargetS1).
Qed.
Print Assumptions source_full_cofinal_common_successor.
