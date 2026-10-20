(** The literal five-premise native carrier theorem is fixed by an
 actual projection onto the original parameters and its selected carrier. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 SourceZeroTransposition SourceNativeSupportProjection SourceNativeProjectionInvariance SourceFiniteTelescope
 SourceFiniteTelescopeTransport NumericalRenaming NumericalRenamingMaps.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_native_five_premise_projection_fixed M live fresh tb tc
 exprofile witness subsetclosed ie iw iset ix ip target law count rb rc:
 source_bounded M exprofile live->source_bounded M witness live->source_bounded M subsetclosed live->
 source_bounded M target live->coding_lt M(code_numeral M 1)live->coding_lt M live fresh->
 source_zero_transposition M fresh tb tc->
 numerical_renaming M exprofile tb tc(succM M fresh)(zeroM M)ie->
 numerical_renaming M witness tb tc(succM M fresh)(zeroM M)iw->
 numerical_renaming M subsetclosed tb tc(succM M fresh)(zeroM M)iset->
 sf_relation M SFMember(zeroM M)fresh ix->sf_relation M SFMember(code_numeral M 1)fresh ip->
 source_finite_telescope M[ie;iw;iset;ix;ip]target law->
 source_native_support_projection M live fresh count rb rc->numerical_renaming M law rb rc count(zeroM M)law.
Proof.
 intros BE BW BS BT B1 LF HTrans RE RW RS HIX HIP HT HP.
 assert(B0:coding_lt M(zeroM M)live).
 { exact(coding_lt_trans M(zeroM M)(code_numeral M 1)live(coding_zero_lt_succ M(zeroM M))B1). }
 assert(RIX:numerical_renaming M ix rb rc count(zeroM M)ix).
 { apply(proj2(numerical_renaming_member M(zeroM M)fresh ix rb rc count(zeroM M)ix HIX)).
   exists(zeroM M),fresh. split;[exact(proj1 HP _ B0)|]. split;[exact(proj1(proj2 HP))|exact HIX]. }
 assert(RIP:numerical_renaming M ip rb rc count(zeroM M)ip).
 { apply(proj2(numerical_renaming_member M(code_numeral M 1)fresh ip rb rc count(zeroM M)ip HIP)).
   exists(code_numeral M 1),fresh. split;[exact(proj1 HP _ B1)|]. split;[exact(proj1(proj2 HP))|exact HIP]. }
 apply(source_finite_telescope_renaming M[ie;iw;iset;ix;ip][ie;iw;iset;ix;ip]target target law law rb rc count(zeroM M));
  [|exact(source_bounded_projection_fixed M target live fresh count rb rc BT HP)|exact HT|exact HT].
 constructor;[exact(source_transposed_bounded_projection_fixed M exprofile live fresh tb tc ie count rb rc BE LF HTrans RE HP)|].
 constructor;[exact(source_transposed_bounded_projection_fixed M witness live fresh tb tc iw count rb rc BW LF HTrans RW HP)|].
 constructor;[exact(source_transposed_bounded_projection_fixed M subsetclosed live fresh tb tc iset count rb rc BS LF HTrans RS HP)|].
 constructor;[exact RIX|]. constructor;[exact RIP|]. constructor.
Qed.
Print Assumptions source_native_five_premise_projection_fixed.
