(** The finite literal formula computed by the canonical definability graph. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceNumeralLift
 SourceLDefinableProfile SourceFiniteCutoffShift SourceSetRelativizationCalibration
 SourceSetRelativization SchemaConstructorBounds SetSchemaConstructors.
From Undecidability.FOL Require Import Syntax.Core Syntax.Facts Syntax.BinSig Sets.Signatures Sets.minZF.
From FOL Require Import FullSyntax.
Unset Implicit Arguments.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZFSignature.ZF_pred_sig | 0.
Definition finite_definable_profile(domain phi:sf_form):sf_form :=
 ∃(domain ∧∀($0 ∈' $1 ↔($0 ∈' $2 ∧sf_relativize_set 2
    phi[source_shift_sigma 1][source_shift_sigma 1]))).
Lemma source_definable_profile_shell M d r selected carrier conjunction lr rl iff all body result :
 sf_relation M SFMember(zeroM M)(code_numeral M 1) selected ->
 sf_relation M SFMember(zeroM M)(code_numeral M 2) carrier ->
 sf_relation M SFAnd carrier r conjunction ->sf_relation M SFImpl selected conjunction lr ->
 sf_relation M SFImpl conjunction selected rl ->sf_relation M SFAnd lr rl iff ->
 sf_relation M SFAll iff(zeroM M) all ->sf_relation M SFAnd d all body ->
 sf_relation M SFEx body(zeroM M) result ->
 code_relation M(L_definable_profile_environment r d)(E_L_definable_profile(CEvar 0)(CEvar 1)) result.
Proof.
 intros HSelected HCarrier HConj HLR HRL HIff HAll HBody HResult.
 set(env:=L_definable_profile_environment r d).
 set(atomX:=E_sf SFMember(CEconst 0)(CEconst 1)).
 set(atomY:=E_sf SFMember(CEconst 0)(CEconst 2)).
 assert(HX:code_relation M env atomX selected).
 { exact(proj2(schema_expression_graph M env SFMember(CEconst 0)(CEconst 1)
     (zeroM M)(code_numeral M 1) selected eq_refl eq_refl) HSelected). }
 assert(HY:code_relation M env atomY carrier).
 { exact(proj2(schema_expression_graph M env SFMember(CEconst 0)(CEconst 2)
     (zeroM M)(code_numeral M 2) carrier eq_refl eq_refl) HCarrier). }
 assert(HC:code_relation M env(E_sf SFAnd atomY(CEvar 0)) conjunction).
 { exact(proj2(schema_expression_graph M env SFAnd atomY(CEvar 0) carrier r conjunction HY eq_refl) HConj). }
 assert(HL:code_relation M env(E_sf SFImpl atomX(E_sf SFAnd atomY(CEvar 0))) lr).
 { exact(proj2(schema_expression_graph M env SFImpl atomX _ selected conjunction lr HX HC) HLR). }
 assert(HR:code_relation M env(E_sf SFImpl(E_sf SFAnd atomY(CEvar 0)) atomX) rl).
 { exact(proj2(schema_expression_graph M env SFImpl _ atomX conjunction selected rl HC HX) HRL). }
 assert(HI:code_relation M env(E_sf_iff atomX(E_sf SFAnd atomY(CEvar 0))) iff).
 { exact(proj2(schema_expression_graph M env SFAnd _ _ lr rl iff HL HR) HIff). }
 assert(HA:code_relation M env(E_sf SFAll(E_sf_iff atomX(E_sf SFAnd atomY(CEvar 0)))(CEconst 0)) all).
 { exact(proj2(schema_expression_graph M env SFAll _ (CEconst 0) iff(zeroM M) all HI eq_refl) HAll). }
 assert(HB:code_relation M env(E_sf SFAnd(CEvar 1)
   (E_sf SFAll(E_sf_iff atomX(E_sf SFAnd atomY(CEvar 0)))(CEconst 0))) body).
 { exact(proj2(schema_expression_graph M env SFAnd(CEvar 1) _ d all body eq_refl HA) HBody). }
 exact(proj2(schema_expression_graph M env SFEx _ (CEconst 0) body(zeroM M) result HB eq_refl) HResult).
Qed.
Theorem source_definable_profile_finite_lift M domain phi :
 source_definable_profile M(code_numeral M(sf_encode domain))(code_numeral M(sf_encode phi))
  (code_numeral M(sf_encode(finite_definable_profile domain phi))).
Proof.
 set(first:=phi[source_shift_sigma 1]). set(matrix:=first[source_shift_sigma 1]).
 set(r:=sf_relativize_set 2 matrix).
 exists(code_numeral M(sf_encode first)),(code_numeral M(sf_encode matrix)),(code_numeral M(sf_encode r)).
 split;[apply(source_cutoff_shift_fixed_source M 1(fun _=>zeroM M) phi);apply source_formula_numeral_graph|].
 split;[apply(source_cutoff_shift_fixed_source M 1(fun _=>zeroM M) first);apply source_formula_numeral_graph|].
 split;[apply source_set_relativization_finite_lift|].
 eapply source_definable_profile_shell with
  (selected:=code_numeral M(sf_encode($0 ∈' $1)))
  (carrier:=code_numeral M(sf_encode($0 ∈' $2)))
  (conjunction:=code_numeral M(sf_encode($0 ∈' $2 ∧r)))
  (lr:=code_numeral M(sf_encode($0 ∈' $1 →($0 ∈' $2 ∧r))))
  (rl:=code_numeral M(sf_encode(($0 ∈' $2 ∧r)→$0 ∈' $1)))
  (iff:=code_numeral M(sf_encode($0 ∈' $1 ↔($0 ∈' $2 ∧r))))
  (all:=code_numeral M(sf_encode(∀($0 ∈' $1 ↔($0 ∈' $2 ∧r)))))
  (body:=code_numeral M(sf_encode(domain ∧∀($0 ∈' $1 ↔($0 ∈' $2 ∧r))))).
 - exact(sf_make_numeral M SFMember 0 1).
 - exact(sf_make_numeral M SFMember 0 2).
 - exact(sf_make_numeral M SFAnd(sf_encode($0 ∈' $2))(sf_encode r)).
 - exact(sf_make_numeral M SFImpl(sf_encode($0 ∈' $1))(sf_encode($0 ∈' $2 ∧r))).
 - exact(sf_make_numeral M SFImpl(sf_encode($0 ∈' $2 ∧r))(sf_encode($0 ∈' $1))).
 - exact(sf_make_numeral M SFAnd(sf_encode($0 ∈' $1 →($0 ∈' $2 ∧r)))(sf_encode(($0 ∈' $2 ∧r)→$0 ∈' $1))).
 - exact(sf_make_numeral M SFAll(sf_encode($0 ∈' $1 ↔($0 ∈' $2 ∧r))) 0).
 - exact(sf_make_numeral M SFAnd(sf_encode domain)(sf_encode(∀($0 ∈' $1 ↔($0 ∈' $2 ∧r))))).
 - exact(sf_make_numeral M SFEx(sf_encode(domain ∧∀($0 ∈' $1 ↔($0 ∈' $2 ∧r)))) 0).
Qed.
Print Assumptions source_definable_profile_shell.
Print Assumptions source_definable_profile_finite_lift.
