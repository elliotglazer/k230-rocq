(** Literal fixed primitives used by the arbitrary-code definability recursion.
    These are syntax calibrations, not the uniform definability theorem. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceBounded
 SourceBoundedCalibration SourceNumeralLift OldNamedSyntaxBridge OldFullNDSourceBridge.
From OldZFC Require Z_base Z_cl Z_rel.
From Undecidability.FOL Require Import Syntax.Bounded.
Unset Implicit Arguments.
Definition source_def_empty :sf_form := isolated_formula
 (OldZFC.Z_base.Emp0 (@OC.var OB.sig_empty 0)).
Definition source_def_successor01 :sf_form := isolated_formula
 (OldZFC.Z_base.Succ0 (@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)).
Definition source_def_extension021 :sf_form := isolated_formula
 (OldZFC.Z_cl.Ext0 (@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 2)(@OC.var OB.sig_empty 1)).

Lemma source_def_empty_bound :CBound.bounded 1 source_def_empty.
Proof. unfold source_def_empty. apply (@isolated_bounded OC.falsity_on 1),OldZFC.Z_rel.fb_bounded,OldZFC.Z_rel.fbb_fb. reflexivity. Qed.
Lemma source_def_successor_bound :CBound.bounded 2 source_def_successor01.
Proof. unfold source_def_successor01. apply (@isolated_bounded OC.falsity_on 2),OldZFC.Z_rel.fb_bounded,OldZFC.Z_rel.fbb_fb. reflexivity. Qed.
Lemma source_def_extension_bound :CBound.bounded 3 source_def_extension021.
Proof. unfold source_def_extension021. apply (@isolated_bounded OC.falsity_on 3),OldZFC.Z_rel.fb_bounded,OldZFC.Z_rel.fbb_fb. reflexivity. Qed.
Theorem numerical_def_empty_bound M :source_bounded M
 (code_numeral M(sf_encode source_def_empty))(code_numeral M 1).
Proof. apply source_formula_numeral_bounded,source_def_empty_bound. Qed.
Theorem numerical_def_successor_bound M :source_bounded M
 (code_numeral M(sf_encode source_def_successor01))(code_numeral M 2).
Proof. apply source_formula_numeral_bounded,source_def_successor_bound. Qed.
Theorem numerical_def_extension_bound M :source_bounded M
 (code_numeral M(sf_encode source_def_extension021))(code_numeral M 3).
Proof. apply source_formula_numeral_bounded,source_def_extension_bound. Qed.
Print Assumptions numerical_def_empty_bound.
Print Assumptions numerical_def_successor_bound.
Print Assumptions numerical_def_extension_bound.


