(** Literal Power Set selector shell. Its output is exactly the L-relative
 subset closure used by the native K carrier inference. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceNumeralLift
 SourceNativePowerCarrierOld SourceNativePowerCarrierFixed SourceOrdinaryReflectionParameters SourceOrdinaryReflectionSyntax
 SourceFiniteNamedRelativization SourceRelativization SourceRelativizationCalibration OldRelativizationBridge
 SourceFiniteParameters SourceFiniteParameterProofs SourceFiniteNameParameters SourceFiniteParameterComposition SourceUnaryParameters SourceParameterGraphs
 SourceHierarchySyntax SourceHierarchyCalibration SourceOrdinalPredicate SourceOrdinalParameterCalibration
 SourceLFixed SourceZFRProvability SourceSubsetClosedPoint SourceSubsetClosedShift SourceUpperTraceFrame
 SourcePropositionalRebase SourceFiniteTelescope NumericalInstantiation OldNamedSyntaxBridge OldFullNDSourceBridge.
From OldK230S Require KUpperCore.
From OldZFC Require Z_base Z_L Z_refl Z_rel.
From Undecidability.FOL Require Import Syntax.Bounded Syntax.BinSig Sets.Signatures Sets.minZF.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZFSignature.ZF_pred_sig | 0.
Local Opaque code_numeral source_L_domain source_L_domain_code source_ordinal_predicate source_LL_predicate.
Lemma source_native_cp_theta_bound:bounded 4 source_native_cp_theta.
Proof. apply(@isolated_bounded OC.falsity_on 4 old_native_cp_theta).
 exact(OldZFC.Z_rel.fb_bounded _ 4 old_native_cp_theta_bound). Qed.
Lemma isolated_native_subset_at i:
 isolated_formula(OldK230S.KUpperCore.subset_closed(@OC.var OB.sig_empty i))=
 C.subst_form(C.scons(C.var i)C.var)(source_point_subset_closed $0).
Proof. reflexivity. Qed.
Theorem source_parameter_native_subset_closed M names rho i Y raw:
 code_relation M rho(names i)Y->
 code_relation M rho(source_parameter_expression names
  (isolated_formula(OldK230S.KUpperCore.subset_closed(@OC.var OB.sig_empty i))))raw->
 source_subset_closed_graph M Y raw.
Proof.
 intros HName HRaw. rewrite isolated_native_subset_at,source_parameter_substitution in HRaw.
 pose proof(source_unary_parameter_instantiation M(source_point_subset_closed $0)
  (fun j=>names(sf_index((C.scons(C.var i)C.var)j)))rho Y raw
  source_point_subset_closed_bound HName HRaw)as HInst.
 destruct(code_relation_total M(source_parameter_expression source_three_parameter_names(source_point_subset_closed $0))
  (fun _=>Y))as(raw'&HRaw').
 pose proof(source_unary_parameter_instantiation M(source_point_subset_closed $0)
  source_three_parameter_names(fun _=>Y)Y raw' source_point_subset_closed_bound eq_refl HRaw')as HInst'.
 pose proof(numerical_instantiation_functional M _ Y raw raw' HInst HInst')as E. subst raw'. exact HRaw'.
Qed.
Theorem source_zfr_native_cp_subset_shell M beta Y s t:
 exists refl ordinal level st sY tY raw relative law,
 source_ordinary_reflection M(source_L_domain_code M)(code_numeral M 4)
  (code_numeral M(sf_encode source_native_cp_theta))beta refl /\
 numerical_instantiation M(source_ordinal_predicate_code M)beta ordinal /\
 source_LL_instance M beta Y level /\sf_relation M SFMember s t st /\
 sf_relation M SFMember s Y sY /\sf_relation M SFMember t Y tY /\
 source_subset_closed_graph M Y raw /\source_relativization M(source_L_domain_code M)raw relative /\
 source_finite_telescope M (refl::ordinal::level::st::sY::tY::nil) relative law /\source_zfr_provable M law.
Proof.
 set(rho:=fun i:nat=>match i with 0=>beta|1=>Y|2=>s|_=>t end).
 set(names:=source_finite_parameter_names 4).
 destruct(code_relation_total M source_native_cp_subset_expression rho)as(law&HLaw).
 pose proof(source_zfr_native_cp_subset_named M rho law HLaw)as PLaw.
 change(code_relation M rho(E_sf SFImpl
  (source_parameter_expression names(isolated_formula(OldZFC.Z_refl.Refl 4 old_native_cp_theta(@OC.var OB.sig_empty 0))))
  (E_sf SFImpl(source_parameter_expression names(isolated_formula(OldZFC.Z_base.Ord0(@OC.var OB.sig_empty 0))))
   (E_sf SFImpl(source_parameter_expression names(isolated_formula(OldZFC.Z_L.LL(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1))))
    (E_sf SFImpl(E_sf SFMember(names 2)(names 3))
     (E_sf SFImpl(E_sf SFMember(names 2)(names 1))
      (E_sf SFImpl(E_sf SFMember(names 3)(names 1))
       (source_parameter_expression names(isolated_formula(OldRegCon.Rel.rel OldZFC.Z_L.Lform
        (OldK230S.KUpperCore.subset_closed(@OC.var OB.sig_empty 1)))))))))))law)in HLaw.
 destruct(schema_expression_split M rho SFImpl _ _ law HLaw)as(refl&i1&HRefl&HI1&H0).
 destruct(schema_expression_split M rho SFImpl _ _ i1 HI1)as(ordinal&i2&HOrdinal&HI2&H1).
 destruct(schema_expression_split M rho SFImpl _ _ i2 HI2)as(level&i3&HLevel&HI3&H2).
 destruct(schema_expression_split M rho SFImpl _ _ i3 HI3)as(st&i4&HST&HI4&H3).
 destruct(schema_expression_split M rho SFImpl _ _ i4 HI4)as(sY&i5&HSY&HI5&H4).
 destruct(schema_expression_split M rho SFImpl _ _ i5 HI5)as(tY&relative&HTY&HRelative&H5).
 destruct(code_relation_total M(source_parameter_expression names
  (isolated_formula(OldK230S.KUpperCore.subset_closed(@OC.var OB.sig_empty 1))))rho)as(raw&HRaw).
 exists refl,ordinal,level,st,sY,tY,raw,relative,law. split.
 - exact(source_parameter_ordinary_reflection M 4 old_native_cp_theta names rho beta refl source_native_cp_theta_bound eq_refl HRefl).
 - split;[exact(source_parameter_ordinal_instance M names rho 0 beta ordinal eq_refl HOrdinal)|].
   split;[exact(source_parameter_LL_instance M names rho 0 1 beta Y level eq_refl eq_refl HLevel)|].
   split;[exact HST|]. split;[exact HSY|]. split;[exact HTY|]. split.
   + exact(source_parameter_native_subset_closed M names rho 1 Y raw eq_refl HRaw).
   + split.
     * rewrite isolated_relativization in HRelative.
       exact(source_finite_named_relativization M source_L_domain
        (isolated_formula(OldK230S.KUpperCore.subset_closed(@OC.var OB.sig_empty 1)))4 rho raw relative
        source_L_domain_bounded HRaw HRelative).
     * split;[|exact PLaw]. exists i1. split;[|exact H0]. exists i2. split;[|exact H1].
       exists i3. split;[|exact H2]. exists i4. split;[|exact H3]. exists i5. split;[|exact H4].
       exists relative. split;[reflexivity|exact H5].
Qed.
Print Assumptions source_native_cp_theta_bound.
Print Assumptions source_parameter_native_subset_closed.
Print Assumptions source_zfr_native_cp_subset_shell.
