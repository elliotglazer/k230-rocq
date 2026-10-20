(** Split off the first entry of an arbitrary internally finite beta
    environment. The original codes themselves are the resulting cons. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions NumericalProofs
 NumericalEnvironments SourceBoundedMapComposition.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature|0.
#[local] Existing Instance PA_preds_signature|0.
Theorem source_dn_environment_uncons M b c count:exists head tb tc,
 environment_cons M tb tc count head b c(succM M count).
Proof.
 set(rho:=b .:c .:fun _=>zeroM M).
 set(F:=beta_formula $2 $3(σ $1)$0).
 assert(HF:forall i v,holds M(v .:i .:rho)F <->beta M b c(succM M i)v).
 { intros i v. unfold F. apply beta_formula_correct. }
 assert(HT:forall i,coding_lt M i count ->exists v,holds M(v .:i .:rho)F).
 { intros i _. destruct(beta_total M b c(succM M i))as(v&HV).
   exists v. exact(proj2(HF i v)HV). }
 assert(HU:forall i v w,coding_lt M i count ->holds M(v .:i .:rho)F ->holds M(w .:i .:rho)F ->v=w).
 { intros i v w _ HV HW. exact(beta_unique M b c(succM M i)v w(proj1(HF i v)HV)(proj1(HF i w)HW)). }
 destruct(beta_pack_total_function M rho F count HT HU)as(tb&tc&HTable).
 destruct(beta_total M b c(zeroM M))as(head&HHead).
 exists head,tb,tc. split;[reflexivity|]. split.
 - apply(proj2(environment_lookup_inside M b c(succM M count)(zeroM M)head(coding_zero_lt_succ M count))). exact HHead.
 - intros i v HE. destruct(environment_lt_cases M i count)as[HI|HI].
   + apply(proj1(environment_lookup_inside M tb tc count i v HI))in HE.
     pose proof(proj1(HF i v)(proj1(HTable i v HI)HE))as HOld.
     apply(proj2(environment_lookup_inside M b c(succM M count)(succM M i)v
      (proj2(coding_lt_succ_cancel M i count)HI))). exact HOld.
   + apply(proj1(environment_lookup_outside M tb tc count i v HI))in HE.
     apply(proj2(environment_lookup_outside M b c(succM M count)(succM M i)v
      ltac:(intro H;apply HI;exact(proj1(coding_lt_succ_cancel M i count)H)))). exact HE.
Qed.
Print Assumptions source_dn_environment_uncons.
