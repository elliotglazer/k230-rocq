(** An actual attempt that maps the initial domain index to its initial value. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceRecursionPrimitiveRelations SourceRecursionPrimitiveTransport
 SourceRecursionAttempt SourceRecursionAttemptBounds SourceRecursionBottomAttempt SourceZFRPositiveMaps SourceZFRConjunctionLeft.
Unset Implicit Arguments.
Definition source_rec_initial_attempt M phi o a N out:=exists att app body,
 source_rec_attempt M phi(succM M o)(succM M a)(succM M N)(zeroM M)att /\source_rec_app M(zeroM M)(succM M o)(succM M a)app /\
 sf_relation M SFAnd att app body /\sf_relation M SFEx body(zeroM M)out.
Theorem source_rec_initial_attempt_total M phi o a N:exists out,source_rec_initial_attempt M phi o a N out.
Proof.
 destruct(source_rec_attempt_total M phi(succM M o)(succM M a)(succM M N)(zeroM M))as(att&HT).
 destruct(source_rec_app_total M(zeroM M)(succM M o)(succM M a))as(app&HA).
 destruct(sf_relation_total M SFAnd att app)as(body&HB).
 destruct(sf_relation_total M SFEx body(zeroM M))as(out&HO). exists out,att,app,body. auto.
Qed.
Theorem source_rec_initial_attempt_bounded M phi o a N out k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->source_rec_initial_attempt M phi o a N out ->source_bounded M out k.
Proof.
 intros BP BO BA BN(att&app&body&HT&HA&HB&HO).
 pose proof(source_rec_attempt_bounded M phi(succM M o)(succM M a)(succM M N)(zeroM M)att(succM M k)BP
  (proj2(coding_lt_succ_cancel M o k)BO)(proj2(coding_lt_succ_cancel M a k)BA)(proj2(coding_lt_succ_cancel M N k)BN)(coding_zero_lt_succ M k)HT)as BT.
 pose proof(source_rec_app_bounded M(zeroM M)(succM M o)(succM M a)app(succM M k)(coding_zero_lt_succ M k)
  (proj2(coding_lt_succ_cancel M o k)BO)(proj2(coding_lt_succ_cancel M a k)BA)HA)as BApp.
 exact(proj2(source_bounded_accept_unary M SFEx body out k(or_intror eq_refl)HO)
  (proj2(source_bounded_accept_binary M SFAnd att app body(succM M k)(or_introl eq_refl)HB)(conj BT BApp))).
Qed.
Theorem source_zfr_rec_initial_attempt_from_bottom M phi o a N old new k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->
 source_rec_initial_attempt M(zeroM M)o a N old ->source_rec_initial_attempt M phi o a N new ->source_zfr_map M old new.
Proof.
 intros BP BO BA BN HOld HNew.
 pose proof(source_rec_initial_attempt_bounded M(zeroM M)o a N old k(source_bounded_accept_falsity M(code_numeral M 2))BO BA BN HOld)as BOld.
 pose proof(source_rec_initial_attempt_bounded M phi o a N new k BP BO BA BN HNew)as BNew.
 destruct HOld as(att0&app0&body0&HT0&HA0&HB0&HO0). destruct HNew as(att&app&body&HT&HA&HB&HO).
 pose proof(source_rec_app_functional M _ _ _ app0 app HA0 HA)as E. subst app0.
 rec_all_bounds.
 apply(source_zfr_map_quantifier M SFEx body0 body old new k(or_intror eq_refl));try assumption.
 apply(source_zfr_map_and_left M att0 att app body0 body(succM M k));try assumption.
 exact(source_zfr_rec_bottom_attempt_map M phi(succM M o)(succM M a)(succM M N)(zeroM M)att0 att(succM M k)BP
  (proj2(coding_lt_succ_cancel M o k)BO)(proj2(coding_lt_succ_cancel M a k)BA)(proj2(coding_lt_succ_cancel M N k)BN)(coding_zero_lt_succ M k)HT0 HT).
Qed.
Print Assumptions source_rec_initial_attempt_total.
Print Assumptions source_rec_initial_attempt_bounded.
Print Assumptions source_zfr_rec_initial_attempt_from_bottom.
