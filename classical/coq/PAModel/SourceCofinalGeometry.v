(** Exact ordinary ordinal-collection and cofinal-cover syntax, independent
    of source proof existence. These are the retained PH_from antecedents. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceQuantifierRules
 SourceReflectionUnionOld SourceReflectionLevelCoverOld SourceLFixed OldNamedSyntaxBridge OldFullNDSourceBridge
 SourceFiniteParameters SourceFiniteNameParameters SourceParameterGraphs SourceParameterRenamingTransport NumericalRenamingMaps NumericalRenaming NumericalContextRenaming.
From OldZFC Require Z_base Z_L Z_refl Z_rel.
From Undecidability.FOL Require Import Syntax.Bounded.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Definition source_cofinal_ordinals_predicate:=isolated_formula(old_reflection_ordinals(@OC.var OB.sig_empty 0)).
Definition source_cofinal_cover_predicate:=isolated_formula(old_reflection_level_cover(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)).
Lemma source_cofinal_ordinals_finite_bound:bounded 1 source_cofinal_ordinals_predicate.
Proof.
 apply(@isolated_bounded OC.falsity_on 1(old_reflection_ordinals(@OC.var OB.sig_empty 0))).
 apply(OldZFC.Z_rel.fb_bounded _ 1).
 change ((0<2 /\1<2) /\OldZF.Std_tr.fb 2(OldZFC.Z_base.Ord0(@OC.var OB.sig_empty 0))).
 split;[lia|]. exact(OldZFC.Z_refl.fb_Ord0(@OC.var OB.sig_empty 0)2 ltac:(cbn;lia)).
Qed.
Lemma source_cofinal_cover_finite_bound:bounded 2 source_cofinal_cover_predicate.
Proof.
 apply(@isolated_bounded OC.falsity_on 2(old_reflection_level_cover(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1))).
 apply(OldZFC.Z_rel.fb_bounded _ 2).
 change ((0<3 /\2<3) /\((0<4 /\2<4) /\
  (OldZF.Std_tr.fb 5(OldZFC.Z_L.LL(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 0)) /\(2<5 /\0<5)))).
 split;[lia|]. split;[lia|]. split;[exact(OldZFC.Z_refl.fb_LL(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 0)5 ltac:(cbn;lia)ltac:(cbn;lia))|lia].
Qed.
Definition source_cofinal_ordinals M K out:=code_relation M(fun _=>K)
 (source_parameter_expression(source_finite_parameter_names 1)source_cofinal_ordinals_predicate)out.
Definition source_cofinal_cover M K Lb out:=code_relation M(fun i=>match i with 0=>K|_=>Lb end)
 (source_parameter_expression(source_finite_parameter_names 2)source_cofinal_cover_predicate)out.
Theorem source_cofinal_ordinals_total M K:exists out,source_cofinal_ordinals M K out.
Proof. apply code_relation_total. Qed.
Theorem source_cofinal_cover_total M K Lb:exists out,source_cofinal_cover M K Lb out.
Proof. apply code_relation_total. Qed.
Theorem source_cofinal_ordinals_bounded M K out k:coding_lt M K k ->source_cofinal_ordinals M K out ->source_bounded M out k.
Proof.
 intros HK HO. apply(source_parameter_graph_bounded M 1 source_cofinal_ordinals_predicate source_cofinal_ordinals_finite_bound
 (source_finite_parameter_names 1)(fun _=>K)k);[|exact HO].
 intros[|i]x HI HX;try lia. change(x=K)in HX. now subst x.
Qed.
Theorem source_cofinal_cover_bounded M K Lb out k:coding_lt M K k ->coding_lt M Lb k ->source_cofinal_cover M K Lb out ->source_bounded M out k.
Proof.
 intros HK HL HO. apply(source_parameter_graph_bounded M 2 source_cofinal_cover_predicate source_cofinal_cover_finite_bound
 (source_finite_parameter_names 2)(fun i=>match i with 0=>K|_=>Lb end)k);[|exact HO].
 intros[|[|i]]x HI HX;try lia;[change(x=K)in HX|change(x=Lb)in HX];subst x;assumption.
Qed.
Theorem source_cofinal_ordinals_shift M K f g:source_cofinal_ordinals M K f ->source_cofinal_ordinals M(succM M K)g ->source_formula_shift M f g.
Proof.
 intros HF HG. apply(source_parameter_renaming_transport M 1 source_cofinal_ordinals_predicate source_cofinal_ordinals_finite_bound
 (source_finite_parameter_names 1)(source_finite_parameter_names 1)(fun _=>K)(fun _=>succM M K)
 (zeroM M)(zeroM M)(zeroM M)(succM M(zeroM M))f g);[|exact HF|exact HG].
 intros[|i]x y HI HX HY;try lia. change(x=K)in HX. change(y=succM M K)in HY. subst x y.
 apply context_shift_lookup. reflexivity.
Qed.
Theorem source_cofinal_cover_shift M K Lb f g:source_cofinal_cover M K Lb f ->source_cofinal_cover M(succM M K)(succM M Lb)g ->source_formula_shift M f g.
Proof.
 intros HF HG. apply(source_parameter_renaming_transport M 2 source_cofinal_cover_predicate source_cofinal_cover_finite_bound
 (source_finite_parameter_names 2)(source_finite_parameter_names 2)(fun i=>match i with 0=>K|_=>Lb end)
 (fun i=>match i with 0=>succM M K|_=>succM M Lb end)(zeroM M)(zeroM M)(zeroM M)(succM M(zeroM M))f g);[|exact HF|exact HG].
 intros[|[|i]]x y HI HX HY;try lia.
 - change(x=K)in HX. change(y=succM M K)in HY. subst x y. apply context_shift_lookup. reflexivity.
 - change(x=Lb)in HX. change(y=succM M Lb)in HY. subst x y. apply context_shift_lookup. reflexivity.
Qed.
Print Assumptions source_cofinal_ordinals_finite_bound.
Print Assumptions source_cofinal_cover_finite_bound.
Print Assumptions source_cofinal_cover_shift.
