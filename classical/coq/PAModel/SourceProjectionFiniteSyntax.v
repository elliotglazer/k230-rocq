(** Literal finite PJ/Op4 subformulas. These syntax identities keep the
    fresh named binders separate from their eventual de Bruijn positions. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceProjectionOperationFixed SourceProjectionOperationOld
 SourceFiniteParameters SourceFiniteNameParameters SourceParameterGraphs SourceFiniteParameterComposition
 SourceDefinabilityPrimitives OldNamedSyntaxBridge OldFullNDSourceBridge.
From OldZFC Require Z_cl Z_rel.
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF.
#[local] Existing Instance sig_empty |0.
#[local] Existing Instance ZF_pred_sig |0.
From Undecidability.FOL Require Import Syntax.Bounded.
Unset Implicit Arguments.
Definition projection_operation4:sf_form:=isolated_formula(OldZFC.Z_cl.Op 4
 (@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2)(@OC.var OB.sig_empty 3)).
Definition projection_PJ3:sf_form:=isolated_formula(OldZFC.Z_cl.PJ
 (@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 2)).
Definition old_projection_inner_body4:OldUndecidability.FOL.Syntax.Core.form:=
 (OC.bin OC.FullSyntax.Conj((@OC.var OB.sig_empty 0) ∈' (@OC.var OB.sig_empty 2))
  (OldZFC.Z_cl.Ext0(@OC.var OB.sig_empty 3)(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 0))).
Definition projection_inner_body4:sf_form:=isolated_formula old_projection_inner_body4.
Definition projection_inner3:sf_form:=isolated_formula(OC.quant OC.FullSyntax.Ex old_projection_inner_body4).
Definition projection_outer_body4:sf_form:=isolated_formula
 (OC.bin OC.FullSyntax.Conj(((@OC.var OB.sig_empty 0) ∈' (@OC.var OB.sig_empty 2)))
 (OC.quant OC.FullSyntax.Ex(OC.bin OC.FullSyntax.Conj(((@OC.var OB.sig_empty 0) ∈' (@OC.var OB.sig_empty 2)))
 (OldZFC.Z_cl.Ext0(@OC.var OB.sig_empty 4)(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 0))))).
Lemma projection_operation_bound:CBound.bounded 4 projection_operation4.
Proof. unfold projection_operation4. apply(@isolated_bounded OC.falsity_on 4),OldZFC.Z_rel.fb_bounded,OldZFC.Z_rel.fbb_fb. reflexivity. Qed.
Lemma projection_PJ_bound:CBound.bounded 3 projection_PJ3.
Proof. unfold projection_PJ3. apply(@isolated_bounded OC.falsity_on 3),OldZFC.Z_rel.fb_bounded,OldZFC.Z_rel.fbb_fb. reflexivity. Qed.
Lemma projection_inner_body_bound:CBound.bounded 4 projection_inner_body4.
Proof. unfold projection_inner_body4. apply(@isolated_bounded OC.falsity_on 4),OldZFC.Z_rel.fb_bounded,OldZFC.Z_rel.fbb_fb. reflexivity. Qed.
Lemma projection_inner_bound:CBound.bounded 3 projection_inner3.
Proof. unfold projection_inner3. apply(@isolated_bounded OC.falsity_on 3),OldZFC.Z_rel.fb_bounded,OldZFC.Z_rel.fbb_fb. reflexivity. Qed.
Lemma projection_outer_body_bound:CBound.bounded 4 projection_outer_body4.
Proof. unfold projection_outer_body4. apply(@isolated_bounded OC.falsity_on 4),OldZFC.Z_rel.fb_bounded,OldZFC.Z_rel.fbb_fb. reflexivity. Qed.
Lemma projection_PJ_literal:sf_encode projection_PJ3=sf_make SFEx(sf_encode projection_outer_body4)0.
Proof. reflexivity. Qed.
Print Assumptions projection_operation_bound.
Print Assumptions projection_PJ_bound.
Print Assumptions projection_inner_body_bound.
Print Assumptions projection_outer_body_bound.
