(** An actual unpair site accepts finite zero padding of its entry PC. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs NumericalEnvironments Pairing
 Program230PathCode Program230Configurations Program230Histories Program230TransferProgram
 Program230InstructionFormula Program230RootHistory Program230TransferEntry Program230UnpairSites.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Theorem p230_unpair_padded_entry M P Q a n start count:
 In(P,a,n)p230_unpair_sites->program230_pc start=program230_path_value M Q->ipeq Q P->
 program230_register start a=count->program230_register start 6=zeroM M->program230_register start 7=zeroM M->
 exists b c time final,program230_program_history M p230 b c time start /\
 program230_state_at M b c time final /\coding_lt M(zeroM M)time /\
 program230_pc final=program230_path_value M(inc_path P) /\program230_register final a=zeroM M /\
 pair_graph M(program230_register final 6)(program230_register final 7)count /\
 (forall i,(i<9)%nat->i<>a->i<>6->i<>7->program230_register final i=program230_register start i).
Proof.
 intros HI HP HE HA H6 H7.
 set(canonical:=program230_with_pc start(program230_path_value M P)).
 assert(CA:program230_register canonical a=count)by(unfold canonical;now rewrite program230_with_pc_register).
 assert(C6:program230_register canonical 6=zeroM M)by(unfold canonical;now rewrite program230_with_pc_register).
 assert(C7:program230_register canonical 7=zeroM M)by(unfold canonical;now rewrite program230_with_pc_register).
 destruct(p230_unpair_site_history M P a n canonical count HI eq_refl CA C6 C7)
 as[b[c[time[final[HR[HT[Hpositive[Hpc[HZ[Hpair Hframe]]]]]]]]]].
 assert(Hnz:time<>zeroM M).
 {intro E;rewrite E in Hpositive;destruct Hpositive as[d Hd];rewrite coding_add_zero in Hd;exact(zero_ne_succ M d Hd). }
 apply(proj2(p230_instruction_history_correct M b c time canonical))in HR.
 destruct(p230_history_ipeq_endpoint M b c time canonical P Q final eq_refl(ipeq_sym Q P HE)HR Hnz HT)
 as[d[e[HD[HT' _]]]].
 assert(EC:program230_with_pc canonical(program230_path_value M Q)=start).
 {unfold canonical;rewrite program230_with_pc_twice;now apply program230_with_pc_restore. }
 exists d,e,time,final;split;[apply p230_instruction_history_correct;now rewrite <-EC|].
 split;[exact HT'|]. split;[exact Hpositive|]. split;[exact Hpc|]. split;[exact HZ|]. split;[exact Hpair|].
 intros i Hi Hia Hi6 Hi7;rewrite(Hframe i Hi Hia Hi6 Hi7);unfold canonical;apply program230_with_pc_register.
Qed.
Print Assumptions p230_unpair_padded_entry.
