(** A fixed ordinary geometry list. The internally finite piece table
    is a syntax parameter, not a family of assumed source proofs. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SourceBounded NumericalInstantiation NumericalRenaming SourceQuantifierRules
 SourceOrdinalPredicate SourceDomainInstances SourceCofinalGeometry SourceHierarchySyntax SourceHierarchyShifts
 SourceReflectionGeometryPredicates SourceRecursionPrimitiveRelations SourcePieceConjunctionBounds SourceReflectionKF
 SourcePHGeometryShifts SourcePHKFShift.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate_code.
Definition source_PH_geometry_frame M domain level sb sc count K beta Lb frame:=exists ordinals ob subsets lb whole,
 source_cofinal_ordinals M K ordinals /\numerical_instantiation M(source_ordinal_predicate_code M)beta ob /\
 source_reflection_geometry_instance M ReflectionSubsets(source_rec_env2 K beta)subsets /\
 source_LL_instance M beta Lb lb /\source_reflection_KF M domain level sb sc count K whole /\
 frame=[ordinals;ob;subsets;lb;whole].
Theorem source_PH_geometry_frame_total M domain level sb sc count K beta Lb:
 exists frame,source_PH_geometry_frame M domain level sb sc count K beta Lb frame.
Proof.
 destruct(source_cofinal_ordinals_total M K)as(o&HO).
 destruct(numerical_instantiation_total M(source_ordinal_predicate_code M)beta)as(ob&HOB).
 destruct(source_reflection_geometry_instance_total M ReflectionSubsets(source_rec_env2 K beta))as(subsets&HS).
 destruct(source_LL_instance_total M beta Lb)as(lb&HL).
 destruct(source_reflection_KF_total M domain level sb sc count K)as(whole&HW).
 exists[o;ob;subsets;lb;whole],o,ob,subsets,lb,whole. auto 10.
Qed.
Theorem source_PH_geometry_frame_bounded M domain level sb sc count K beta Lb frame bound:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->source_piece_table_valid M sb sc count ->
 coding_lt M K bound ->coding_lt M beta bound ->coding_lt M Lb bound ->
 source_PH_geometry_frame M domain level sb sc count K beta Lb frame ->forall f,In f frame ->source_bounded M f bound.
Proof.
 intros HD HL HV BK BB BL(o&ob&subsets&lb&whole&HO&HOB&HS&HLb&HW&->).
 pose proof(source_cofinal_ordinals_bounded M K o bound BK HO)as BO.
 pose proof(source_domain_instance_bound M(source_ordinal_predicate_code M)beta ob bound(source_ordinal_predicate_bounded M)BB HOB)as BOB.
 assert(BS:source_bounded M subsets bound).
 { apply(source_reflection_geometry_instance_bounded M ReflectionSubsets(source_rec_env2 K beta)subsets bound);[|exact HS].
   intros[|[|i]]HI;cbn in HI;try lia;assumption. }
 pose proof(source_LL_instance_bounded M beta Lb lb bound BB BL HLb)as BLB.
 pose proof(source_reflection_KF_bounded M domain level sb sc count K whole bound HD HL HV BK HW)as BW.
 intros f[<-|[<-|[<-|[<-|[<-|[]]]]]];assumption.
Qed.
Theorem source_PH_geometry_frame_shift M domain level sb sc count K beta Lb frame shifted:
 source_bounded M domain(code_numeral M 1) ->source_bounded M level(code_numeral M 2) ->source_piece_table_valid M sb sc count ->
 source_PH_geometry_frame M domain level sb sc count K beta Lb frame ->
 source_PH_geometry_frame M domain level sb sc count(succM M K)(succM M beta)(succM M Lb)shifted ->
 Forall2(source_formula_shift M)frame shifted.
Proof.
 intros HD HL HV(o&ob&subsets&lb&whole&HO&HOB&HS&HLb&HW&->)
  (o'&ob'&subsets'&lb'&whole'&HO'&HOB'&HS'&HLb'&HW'&->).
 constructor;[exact(source_cofinal_ordinals_shift M K o o' HO HO')|].
 constructor;[exact(source_domain_shift_to M(source_ordinal_predicate_code M)beta ob ob'(source_ordinal_predicate_bounded M)HOB HOB')|].
 constructor;[exact(source_PH_subsets_shift M K beta subsets subsets' HS HS')|].
 constructor;[exact(source_LL_shift_to M beta Lb lb lb' HLb HLb')|].
 constructor;[exact(source_PH_KF_shift M domain level sb sc count K whole whole' HD HL HV HW HW')|constructor].
Qed.
Print Assumptions source_PH_geometry_frame_total.
Print Assumptions source_PH_geometry_frame_bounded.
Print Assumptions source_PH_geometry_frame_shift.
