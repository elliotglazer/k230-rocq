(** The concrete finite-control invariant for the unchanged public program. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 TM230BinaryStep Program230PathCode Program230Edges Program230LeafFormula
 TM230CleanControl TM230LogicalSites.
From FOL Require Import FullSyntax Arithmetics.
From K230 Require RM RMEquiv Prog230 Interpreter230Leaves Interpreter230Check.
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Definition machine230_p230_control M depth pc:=
 machine230_clean_control M K230.Interpreter230Check.leaves230 depth pc.
Definition machine230_p230_control_formula depth pc:=
 machine230_clean_control_formula K230.Interpreter230Check.leaves230 depth pc.
Theorem machine230_p230_control_formula_correct M rho depth pc:
 holds M rho(machine230_p230_control_formula depth pc)<->
 machine230_p230_control M(evalM M rho depth)(evalM M rho pc).
Proof. apply machine230_clean_control_formula_correct. Qed.
Lemma machine230_p230_leaf_checked Q e:
 In(Q,e)K230.Interpreter230Check.leaves230 ->
 K230.Interpreter230Check.check_edge Q e=true /\(length Q<=40)%nat.
Proof.
 intro HI. pose proof K230.Interpreter230Check.all_leaves_check as HC.
 rewrite forallb_forall in HC. specialize(HC(Q,e)HI);cbn[fst snd]in HC.
 split;[exact HC|]. unfold K230.Interpreter230Check.check_edge in HC.
 destruct(Nat.leb(length Q)40)eqn:HE;[now apply Nat.leb_le|discriminate].
Qed.
Theorem machine230_p230_control_decode M depth pc:
 machine230_p230_control M depth pc ->exists P,
 depth=code_numeral M(length P) /\pc=program230_path_value M P /\
 (length P<=40)%nat /\K230.RMEquiv.clean K230.Prog230.p230 P.
Proof.
 intros[P[HP[HD HC]]]. exists P;split;[exact HD|]. split;[exact HC|]. split.
 -apply(machine230_control_candidates_bound K230.Interpreter230Check.leaves230 40);[|exact HP].
  intros Q e HI;exact(proj2(machine230_p230_leaf_checked Q e HI)).
 -apply(machine230_control_candidates_clean K230.Prog230.p230 K230.Interpreter230Check.leaves230);[|exact HP].
  intros Q e HI;exact(program230_leaves_sound K230.Prog230.p230
   (K230.RM.nnodes K230.Prog230.p230+1)(K230.RM.root K230.Prog230.p230)Q e HI).
Qed.
Theorem machine230_p230_control_initial M:
 machine230_p230_control M(zeroM M)(code_numeral M 1).
Proof. apply machine230_clean_control_initial. Qed.
Theorem machine230_p230_control_step M Q e R T pc z:
 In(Q,e)K230.Interpreter230Check.leaves230 ->program230_edge_step M Q e R T pc ->
 pc=program230_path_value M(machine230_edge_path Q e z) ->
 machine230_p230_control M(code_numeral M(length(machine230_edge_path Q e z)))pc.
Proof.
 intros HI HE EPC. exists(machine230_edge_path Q e z);split.
 -exact(machine230_edge_candidate M K230.Interpreter230Check.leaves230 Q e R T pc z HI HE).
 -split;[reflexivity|exact EPC].
Qed.
Lemma machine230_clean_false_suffix p P e d:
 K230.RMEquiv.clean p P ->
 K230.RM.walk p(K230.RM.nnodes p+1)(K230.RM.root p)P 0=Some(e,d)->
 Forall(eq false)(skipn d P).
Proof.
 intros HC HW. apply Forall_forall. intros b Hb.
 apply In_nth with(d:=false)in Hb. destruct Hb as[i[Hi He]].
 pose proof(HC e d HW(d+i)ltac:(lia))as Hz. unfold K230.RM.bit in Hz.
 rewrite nth_skipn in He. congruence.
Qed.
Print Assumptions machine230_p230_control_formula_correct.
Print Assumptions machine230_p230_control_decode.
Print Assumptions machine230_p230_control_step.
Print Assumptions machine230_clean_false_suffix.
