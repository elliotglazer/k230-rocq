(** Literal finite calibration against the pinned Z_refl.ballS syntax. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceNumeralLift
  SourceBallSRules SourceBallS OldNamedSyntaxBridge.
From Undecidability.FOL Require Import Syntax.Core Syntax.BinSig Sets.Signatures Sets.minZF.
From OldZFC Require Z_refl.
Unset Implicit Arguments.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZFSignature.ZF_pred_sig | 0.
Fixpoint source_balls_finite(n y:nat)(body:sf_form):sf_form:=match n with
  |0=>body|S k=>∀($0 ∈' $(S y) →source_balls_finite k(S y)body)end.
Theorem source_ballS_finite_lift M n y body:
  source_ballS M(code_numeral M n)(code_numeral M y)(code_numeral M(sf_encode body))
    (code_numeral M(sf_encode(source_balls_finite n y body))).
Proof.
  revert y. induction n as[|n IH];intro y.
  - apply source_ballS_zero. reflexivity.
  - apply source_ballS_succ. exists(code_numeral M(sf_encode(source_balls_finite n(S y)body))).
    split;[exact(IH(S y))|].
    exists(code_numeral M(sf_make SFMember 0(S y))),
      (code_numeral M(sf_make SFImpl(sf_make SFMember 0(S y))(sf_encode(source_balls_finite n(S y)body)))).
    split;[exact(sf_make_numeral M SFMember 0(S y))|].
    split;[exact(sf_make_numeral M SFImpl(sf_make SFMember 0(S y))(sf_encode(source_balls_finite n(S y)body)))|].
    exact(sf_make_numeral M SFAll(sf_make SFImpl(sf_make SFMember 0(S y))(sf_encode(source_balls_finite n(S y)body)))0).
Qed.
Theorem isolated_ballS_exact n y(body:isolated_old_form OC.falsity_on):
  isolated_formula(OldZFC.Z_refl.ballS n(@OC.var OB.sig_empty y)body)=
  source_balls_finite n y(isolated_formula body).
Proof. revert y. induction n as[|n IH];intro y;[reflexivity|].
  change ((∀($0 ∈' $(S y) →isolated_formula(OldZFC.Z_refl.ballS n(@OC.var OB.sig_empty(S y))body)))=
    (∀($0 ∈' $(S y) →source_balls_finite n(S y)(isolated_formula body)))).
  rewrite IH. reflexivity.
Qed.
Theorem source_ballS_old_finite_lift M n y(body:isolated_old_form OC.falsity_on):
  source_ballS M(code_numeral M n)(code_numeral M y)(code_numeral M(sf_encode(isolated_formula body)))
    (code_numeral M(sf_encode(isolated_formula(OldZFC.Z_refl.ballS n(@OC.var OB.sig_empty y)body)))).
Proof. rewrite isolated_ballS_exact. apply source_ballS_finite_lift. Qed.
Print Assumptions source_ballS_finite_lift.
Print Assumptions isolated_ballS_exact.
Print Assumptions source_ballS_old_finite_lift.

