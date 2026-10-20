(** An actual internally finite projection onto the original parameter
 names and one selected carrier. Every unused proof-domain name goes to zero. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT FiniteCRTFormula NumericalProofs BetaPacking CodeExpressions
 NumericalRenamingMaps NumericalEnvironments.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
Definition source_support_projection_index M live fresh i j:=
 (coding_lt M i live /\ j = i) \/
 (~ coding_lt M i live /\ i = fresh /\ j = fresh) \/
 (~ coding_lt M i live /\ i <> fresh /\ j = zeroM M).
Definition source_support_projection_index_formula(live fresh i j:term):form:=
 (Peano.sless i live ∧ (j == i)) ∨
 (((Peano.sless i live → ⊥) ∧ (i == fresh) ∧ (j == fresh)) ∨
  ((Peano.sless i live → ⊥) ∧ (i == fresh → ⊥) ∧ (j == zero))).
Local Opaque holds.
Lemma source_support_projection_index_correct M rho live fresh i j:
 holds M rho(source_support_projection_index_formula live fresh i j)<->
 source_support_projection_index M(evalM M rho live)(evalM M rho fresh)(evalM M rho i)(evalM M rho j).
Proof.
 unfold source_support_projection_index_formula,source_support_projection_index.
 repeat setoid_rewrite holds_or. repeat setoid_rewrite holds_and. repeat setoid_rewrite holds_imp.
 repeat setoid_rewrite holds_sless. Local Transparent holds. cbn[holds evalM]. tauto.
Qed.
Definition source_native_support_projection M live fresh count b c:=
 (forall i,coding_lt M i live->renaming_lookup M b c count(zeroM M)i i) /\
 renaming_lookup M b c count(zeroM M)fresh fresh /\
 (forall i j,coding_lt M i count->renaming_lookup M b c count(zeroM M)i j->
  coding_lt M j live \/j = fresh \/j = zeroM M).
Theorem source_native_support_projection_total M live fresh count:
 exists b c,source_native_support_projection M live fresh count b c.
Proof.
 set(rho:=live .:fresh .:fun _=>zeroM M).
 set(F:=source_support_projection_index_formula $2 $3 $1 $0).
 assert(HT:forall i,coding_lt M i count->exists j,holds M(j .:i .:rho)F).
 { intros i _. destruct(environment_lt_cases M i live)as[HI|HI].
   - exists i. apply source_support_projection_index_correct. left. auto.
   - destruct(@Peano.D_eq_dec(carrier M)(raw_interpretation M)(fun ax H r=>axioms M ax r H)i fresh)as[->|HIF].
     + exists fresh. apply source_support_projection_index_correct. right;left. auto.
     + exists(zeroM M). apply source_support_projection_index_correct. right;right. auto. }
 assert(HB:forall i j,coding_lt M i count->holds M(j .:i .:rho)F->coding_lt M j(succM M count)).
 { intros i j HI H. apply source_support_projection_index_correct in H. change(source_support_projection_index M live fresh i j)in H.
   destruct H as[[_ ->]|[[_[<- ->]]|[_[_ ->]]]].
   - exact(coding_lt_trans M i count(succM M count)HI(coding_lt_succ M count)).
   - exact(coding_lt_trans M i count(succM M count)HI(coding_lt_succ M count)).
   - apply coding_zero_lt_succ. }
 assert(HU:forall i j v,coding_lt M i count->holds M(j .:i .:rho)F->holds M(v .:i .:rho)F->j=v).
 { intros i j v _ HJ HV. apply source_support_projection_index_correct in HJ,HV. change(source_support_projection_index M live fresh i j)in HJ. change(source_support_projection_index M live fresh i v)in HV.
   unfold source_support_projection_index in HJ,HV. intuition congruence. }
 destruct(beta_pack_function M rho F count count HT HB HU)as(b&c&HBC).
 exists b,c. split.
 - intros i HI. destruct(environment_lt_cases M i count)as[HIC|HIC].
   + left. split;[exact HIC|]. apply(proj2(HBC i i HIC)). apply source_support_projection_index_correct. left. auto.
   + right. split;[exact HIC|]. symmetry. apply coding_add_zero_r.
 - split.
   + destruct(environment_lt_cases M fresh count)as[HF|HF].
     * left. split;[exact HF|]. apply(proj2(HBC fresh fresh HF)). apply source_support_projection_index_correct.
       destruct(environment_lt_cases M fresh live)as[HL|HL];[left|right;left];auto.
     * right. split;[exact HF|]. symmetry. apply coding_add_zero_r.
   + intros i j HI HJ. apply(proj1(renaming_lookup_inside M b c count(zeroM M)i j HI))in HJ.
     pose proof(proj1(HBC i j HI)HJ)as H. apply source_support_projection_index_correct in H. change(source_support_projection_index M live fresh i j)in H.
     destruct H as[[HL ->]|[[_[_ ->]]|[_[_ ->]]]];auto.
Qed.
Print Assumptions source_native_support_projection_total.
