(** Uniform closure_om: the genuine recursion kernel specialized to the
    fixed omega structure, with both existential witnesses eliminated. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone FixedSourceBounds
 SourceClosedShift SourceFiniteTelescope SourceFiniteTelescopeExists SourceFiniteTelescopeRemoveTheorem
 SourceRecursionFunctionality SourceRecursionFunctionalityClosed SourceRecursionTotalRelation
 SourceRecursionClosureExists SourceOmegaRecursionFixed SourceOmegaRecursionBounds SourceOmegaRecursionBranch SourceZFRProvability.
From Stdlib Require Import Lists.List Lia.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque code_numeral source_omega_recursion_body_code source_omega_recursion_inner_code source_omega_recursion_code.
Theorem source_zfr_rec_omega_closure M phi funlaw totalG target law:
 source_bounded M phi(code_numeral M 2) ->source_rec_functionality M phi funlaw ->source_rec_total_relation M phi totalG ->
 source_rec_closure_exists M phi(code_numeral M 0)target ->
 source_finite_telescope M[funlaw;totalG]target law ->source_zfr_provable M law.
Proof.
 intros BP HFun HG HT HL.
 pose proof(source_rec_functionality_closed M phi funlaw BP HFun)as BFun.
 pose proof(source_rec_total_relation_closed M phi totalG BP HG)as BG.
 assert(BA:forall k x,In x[funlaw;totalG]->source_bounded M x k).
 { intros k x[<-|[<-|[]]];eapply source_bounded_monotone;try eassumption;apply coding_zero_lt_succ. }
 assert(HS:Forall2(SourceQuantifierRules.source_formula_shift M)[funlaw;totalG][funlaw;totalG]).
 { constructor;[exact(source_closed_shift_self M funlaw BFun)|]. constructor;[exact(source_closed_shift_self M totalG BG)|constructor]. }
 destruct(source_rec_closure_exists_total M phi(code_numeral M 1))as(target1&HT1).
 destruct(source_rec_closure_exists_total M phi(code_numeral M 2))as(target2&HT2).
 pose proof(source_rec_closure_exists_shift M phi(code_numeral M 0)target target1 BP HT HT1)as S0.
 pose proof(source_rec_closure_exists_shift M phi(code_numeral M 1)target1 target2 BP HT1 HT2)as S1.
 destruct(source_finite_telescope_total M([funlaw;totalG]++[source_omega_recursion_body_code M])target2)as(branch2&HBranch2).
 pose proof(source_zfr_rec_omega_branch M phi funlaw totalG target2 branch2 BP HFun HG HT2 HBranch2)as PBranch2.
 destruct(source_finite_telescope_total M([funlaw;totalG]++[source_omega_recursion_inner_code M])target1)as(branch1&HBranch1).
 assert(BInner:source_bounded M(source_omega_recursion_inner_code M)(code_numeral M 2)).
 { exact(source_bounded_monotone M _ (code_numeral M 1)(code_numeral M 2)(source_omega_recursion_inner_bounded M)(proj2(fixed_source_numeral_lt_iff M 1 3)ltac:(lia))). }
 pose proof(source_rec_closure_exists_bounded M phi(code_numeral M 1)target1(code_numeral M 2)BP(proj2(fixed_source_numeral_lt_iff M 1 2)ltac:(lia))HT1)as BT1.
 pose proof(source_zfr_finite_telescope_exists M[funlaw;totalG][funlaw;totalG]
  (source_omega_recursion_body_code M)(source_omega_recursion_inner_code M)target1 target2 branch2 branch1(code_numeral M 2)
  (BA(code_numeral M 2))BInner BT1 HS(source_omega_recursion_inner_graph M)S1 HBranch2 HBranch1 PBranch2)as PBranch1.
 destruct(source_finite_telescope_total M([funlaw;totalG]++[source_omega_recursion_code M])target)as(branch0&HBranch0).
 assert(BOmega:source_bounded M(source_omega_recursion_code M)(code_numeral M 1)).
 { exact(source_bounded_monotone M _ (zeroM M)(code_numeral M 1)(source_omega_recursion_closed M)(coding_zero_lt_succ M(code_numeral M 1))). }
 pose proof(source_rec_closure_exists_bounded M phi(code_numeral M 0)target(code_numeral M 1)BP(proj2(fixed_source_numeral_lt_iff M 0 1)ltac:(lia))HT)as BT.
 pose proof(source_zfr_finite_telescope_exists M[funlaw;totalG][funlaw;totalG]
  (source_omega_recursion_inner_code M)(source_omega_recursion_code M)target target1 branch1 branch0(code_numeral M 1)
  (BA(code_numeral M 1))BOmega BT HS(source_omega_recursion_outer_graph M)S0 HBranch1 HBranch0 PBranch1)as PBranch0.
 exact(source_zfr_finite_telescope_remove_theorem M[funlaw;totalG](source_omega_recursion_code M)target branch0 law(code_numeral M 1)
  (BA(code_numeral M 1))BT HBranch0 HL(source_zfr_omega_recursion_structure M)PBranch0).
Qed.
Print Assumptions source_zfr_rec_omega_closure.
