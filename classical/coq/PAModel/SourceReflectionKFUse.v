(** Actual outer universal elimination of the literal reflection KF law. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 NumericalSubstitutionMaps NumericalSubstitution SubstitutionSource NumericalInstantiation NumericalSourceFull
 SourceInstantiationConstructors SourceDerivedRules SourceTracePointRules SourcePieceConjunctionBounds
 SourceReflectionKF SourceReflectionKFWitness SourceReflectionKFNext.
Unset Implicit Arguments.
Theorem source_full_reflection_KF_use M domain level sb sc count K k whole member next gb gc gn:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->source_piece_table_valid M sb sc count ->
 source_reflection_KF M domain level sb sc count K whole ->sf_relation M SFMember k K member ->
 source_reflection_KF_next M domain level sb sc count K k next ->
 source_full_prv M gb gc gn whole ->source_full_prv M gb gc gn member ->source_full_prv M gb gc gn next.
Proof.
 intros HD HL HV(g&lev&pc&point&all&mk&kw&inner&body&ex&tail&HG&HLev&HPC&HPoint&HAll&HMK&HKW&HInner&HBody&HEx&HTail&HWhole)
  HMember HNext PWhole PMember.
 assert(HRaw:source_reflection_KF_next M domain level sb sc count(succM M K)(zeroM M)ex).
 { exists body. split;[|exact HEx]. exists mk,kw,lev,pc,point,all,inner. auto 15. }
 destruct(substitution_singleton_total M k)as(ib&ic&HHead&_).
 assert(HIN:numerical_instantiation M ex k next).
 { exists ib,ic. split;[exact HHead|].
   exact(source_reflection_KF_next_substitution M domain level sb sc count(succM M K)(zeroM M)ex K k next
    ib ic(code_numeral M 1)(zeroM M)HD HL HV HRaw HNext(substitution_singleton_tail M ib ic K)HHead). }
 pose proof(source_instantiation_head_member M K g k member HG HMember)as HIG.
 destruct(sf_relation_total M SFImpl member next)as(instance&HInstance).
 pose proof(source_instantiation_binary M SFImpl g ex tail k member next instance
  (or_intror(or_intror eq_refl))HTail HIG HIN HInstance)as HI.
 pose proof(full_source_AllE M gb gc gn tail whole k instance
  (source_wf_quantifier_instance M gb gc gn SFAll tail whole k instance(or_introl eq_refl)HWhole
   (source_full_prv_wellformed M gb gc gn whole PWhole)HI)PWhole HWhole HI)as PInstance.
 exact(source_full_modus_ponens M gb gc gn member next instance HInstance PInstance PMember).
Qed.
Print Assumptions source_full_reflection_KF_use.
