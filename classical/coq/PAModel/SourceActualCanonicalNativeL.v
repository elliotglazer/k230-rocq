(** Actual uniform canonical native K-prime images in L. Every common
 carrier, shared reflection geometry, positive selector, trace and finite
 proof certificate is generated, with all five auxiliary witnesses removed
 by genuine fresh source ExE. The only mathematical inputs are the explicit
 existing L Separation and Replacement image obligations. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone
 SourceNativeKRecipes SourceNativeSharedGeometryTotal SourceNativeGeometryElimination SourceNativeFreshWitnessExtrusion
 SourceCommonLevelPoint SourceCommonLevelRecipe SourceCommonLevelDomainContext SourceDomainContexts SourceLFixed
 SourceRelativization SourceRelativizationBounds SourceKZFCForwardSchemas SourceNativeContextExtension
 SourceFiniteCutoffShift SourcePCSTables SourcePieceConjunctionBounds SourceWitnessThetaRecipe SourceHierarchySyntax
 CanonicalKPrimeLFlexibleClosure NativeCanonicalLConsumer NumericalContexts NumericalEnvironments NumericalSourceFull
 SourceZFRProvability ContextCombination SourceTraceBounds SourceClosedContextShift SourceProofWeakening
 SourceContextProofHelpers SourceLeastOrdinalWitness.
Unset Implicit Arguments.
Theorem source_actual_native_upper_L_from_schemas M:
 L_separation_image_obligation M->L_replacement_image_obligation M->canonical_upper_L_any_domain_proofs M.
Proof.
 intros LS LR phi n upper relative BP HUpper HR.
 set(live:=succM M(succM M n)).
 destruct(source_zfr_native_shared_geometry_total M phi n live BP)
  as(theta&level&pb&pc&pn&qb&qc&qn&sb&sc&pieces&unusedOrd&unusedGeometry&unusedLaw&
   HTheta&BTheta&HLevel&BLevel&HPT&HQT&HUnionTable&HValid&HPIn&HQIn&HUnusedOrd&HUnusedGeometry&HUnusedImpl&PUnusedLaw).
 destruct(source_domain_context_total M(source_L_domain_code M)live)as(db&dc&HDC).
 destruct(source_common_level_recipe_total M(zeroM M)live)as(target&HTarget).
 assert(HNames:forall i,coding_lt M i live->coding_lt M(addM M i(zeroM M))live).
 { intros i HI. rewrite coding_add_zero_r. exact HI. }
 destruct(source_zfr_common_level_domain_context M(zeroM M)live live db dc target HDC HNames HTarget)
  as(ab&ac&an&gb&gc&gn&HAC&HG&PTarget).
 pose proof(source_zfr_context_closed M ab ac an HAC)as BA0.
 pose proof(context_bounded_monotone M ab ac an(zeroM M)live BA0(coding_zero_lt_succ M live))as BA.
 pose proof(source_domain_context_bounded M(source_L_domain_code M)live db dc(numerical_L_domain_bounded M)HDC)as BD.
 pose proof(source_context_union_bounded M ab ac an db dc live gb gc gn live HG BA BD)as BG.
 pose proof(source_upper_conclusion_recipe_bound M phi upper n BP HUpper)as BUpper.
 pose proof(source_relativization_preserves_bound M upper(source_L_domain_code M)live relative
  (numerical_L_domain_bounded M)BUpper HR)as BRelative.
 destruct(source_common_level_point_total M(zeroM M)live live(succM M live))as(point&HPoint).
 assert(LSS:coding_lt M live(succM M(succM M live)))by exact(coding_lt_trans M live(succM M live)(succM M(succM M live))(coding_lt_succ M live)(coding_lt_succ M _)).
 assert(LSSS:coding_lt M live(succM M(succM M(succM M live))))by exact(coding_lt_trans M live(succM M(succM M live))(succM M(succM M(succM M live)))LSS(coding_lt_succ M _)).
 assert(PointNames:forall i,coding_lt M i live->coding_lt M(addM M i(zeroM M))(succM M(succM M live))).
 { intros i HI. rewrite coding_add_zero_r. exact(coding_lt_trans M i live(succM M(succM M live))HI LSS). }
 pose proof(source_common_level_point_bounded M(zeroM M)live live(succM M live)point(succM M(succM M live))
  PointNames LSS(coding_lt_succ M(succM M live))HPoint)as BPoint.
 pose proof(context_bounded_monotone M gb gc gn live(succM M(succM M live))BG LSSS)as BGUp.
 destruct(environment_cons_total M gb gc gn point)as(bb&bc&bn&HCons).
 pose proof(proj2(context_bounded_cons M gb gc gn point bb bc bn(succM M(succM M live))HCons)(conj BPoint BGUp))as BBranch.
 pose proof(source_full_cons_head M gb gc gn point bb bc bn(succM M(succM M live))HCons BPoint BBranch)as PPoint.
 assert(HDB:context_included M db dc live bb bc bn).
 { intros f HH. apply(source_cons_tail_inclusion M gb gc gn point bb bc bn HCons).
   exact(context_union_right M ab ac an db dc live gb gc gn HG f HH). }
 pose proof(source_bounded_monotone M relative live(succM M(succM M live))BRelative LSSS)as BRelativeUp.
 destruct(source_full_native_common_point_to_upper M phi theta n upper relative level pb pc pn qb qc qn sb sc pieces
  live(succM M live)point bb bc bn(succM M(succM M live))db dc
  LS LR BP HTheta HUpper HR BLevel HLevel HPT HQT HValid HPIn HQIn LSSS LSS(coding_lt_succ M(succM M live))
  (fun i HI=>coding_lt_trans M i live(succM M(succM M live))HI LSS)BBranch BRelativeUp HDC HDB HPoint PPoint)
  as(eb&ec&en&ub&uc&un&HEC&HU&PGoal).
 destruct(source_full_closed_zfr_common_level_fresh M gb gc gn(zeroM M)live live(succM M live)point target relative live(succM M live)
  bb bc bn eb ec en ub uc un BG BRelative HNames(coding_lt_succ M live)(coding_lt_succ M live)(coding_lt_succ M(succM M live))
  HPoint HTarget HCons HEC HU PGoal PTarget)as(vb&vc&vn&HV&PRelative).
 destruct(context_union_total M ab ac an eb ec en)as(cb&cc&cn&HC).
 assert(HCC:source_zfr_context M cb cc cn).
 { intros f HF. apply(proj1(proj2 HC f))in HF. destruct HF as[HF|HF];[exact(HAC f HF)|exact(HEC f HF)]. }
 destruct(context_union_total M cb cc cn db dc live)as(wb&wc&wn&HW).
 pose proof(context_bounded_monotone M cb cc cn(zeroM M)live(source_zfr_context_closed M cb cc cn HCC)(coding_zero_lt_succ M live))as BC.
 pose proof(source_context_union_bounded M cb cc cn db dc live wb wc wn live HW BC BD)as BW.
 assert(HIn:context_included M vb vc vn wb wc wn).
 { intros f HF. apply(proj1(proj2 HV f))in HF. apply(proj2(proj2 HW f)). destruct HF as[HF|HF].
   - apply(proj1(proj2 HG f))in HF. destruct HF as[HF|HF];[left;apply(proj2(proj2 HC f));now left|now right].
   - left. apply(proj2(proj2 HC f)). now right. }
 exists live,cb,cc,cn,db,dc,wb,wc,wn. split;[exact HCC|]. split;[exact HDC|]. split;[exact HW|].
 exact(source_full_prv_weaken_bounded M vb vc vn wb wc wn relative live PRelative HIn BW).
Qed.
Theorem source_actual_canonical_kprime_L_images M:
 L_separation_image_obligation M->L_replacement_image_obligation M->canonical_kprime_L_images M.
Proof.
 intros LS LR. exact(canonical_kprime_L_images_from_any_domain M(source_actual_native_upper_L_from_schemas M LS LR)).
Qed.
Print Assumptions source_actual_native_upper_L_from_schemas.
Print Assumptions source_actual_canonical_kprime_L_images.
