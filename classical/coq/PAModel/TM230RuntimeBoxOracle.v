(** All literal runtime box-oracle promises discharged by actual register paths. *)
From PAModel Require Import Model Arithmetic CodeExpressions TM230BitArithmetic TM230LeftView TM230Paths
 TM230SkipBlock TM230RuntimeBox TM230RuntimeBoxProperties TM230RuntimeBoxSimplePaths TM230RuntimeBoxIncrement
 TM230RuntimeWords TM230RuntimeStep TM230RuntimeExec TM230MacroProgress.
From Stdlib Require Import Lists.List Arith.Arith Bool.Bool Lia.
Unset Implicit Arguments.
Lemma machine230_runtime_skip_target q r:
 Runtime230.skip_target q=Some r->(r<9)%nat /\machine230_skip_label r=q.
Proof.
 intro H. repeat(destruct q;cbn[Runtime230.skip_target]in H;try discriminate;
 try solve[injection H as <-;split;[lia|reflexivity]]).
Qed.
Theorem machine230_concrete_runtime_oracle M values E br:
 machine230_runtime_branch_valid M values br->
 machine230_runtime_oracle_paths M(machine230_runtime_box M values E)br.
Proof.
 intros HB q x q' x' extra left word s HE HX HV.
 destruct x as[eff|r].
 -destruct eff;cbn[Runtime230.oracle]in HE;try discriminate.
  destruct(Runtime230.skip_target q)as[r|]eqn:HT;[|discriminate].
  injection HE as <- <- <-. destruct(machine230_runtime_skip_target q r HT)as[HR EQ].
  rewrite <-EQ in HV. exact(machine230_runtime_mark_path M values E r left word s HR HX HV).
 -cbn[Runtime230.oracle]in HE.
  destruct(Nat.ltb r 9)eqn:HR;[apply Nat.ltb_lt in HR|discriminate].
  destruct(Nat.eqb q 64)eqn:HQ.
  +apply Nat.eqb_eq in HQ;subst q. injection HE as <- <- <-.
   exact(machine230_runtime_increment_path M values E r left word s HR HX HV).
  +destruct(Nat.eqb q 0)eqn:HQ0;[apply Nat.eqb_eq in HQ0;subst q|discriminate].
   destruct br as[[r' z]|];[|discriminate].
   destruct(Nat.eqb r r')eqn:HRR;[apply Nat.eqb_eq in HRR;subst r'|discriminate].
   destruct z;injection HE as <- <- <-.
   *exact(machine230_runtime_decrement_zero_path M values E r left word s HR HB HX HV).
   *exact(machine230_runtime_decrement_positive_path M values E r left word s HR HB HX HV).
Qed.
Theorem machine230_concrete_runtime_exec M values E br gap fuel target:
 machine230_runtime_branch_valid M values br->
 forall conf moved conf' s,Runtime230.exec fuel br target conf moved=Some conf' ->
 machine230_runtime_view M gap(machine230_runtime_box M values E)conf s ->
 target conf'=true /\exists t,machine230_runtime_view M gap(machine230_runtime_box M values E)conf' t /\
 machine230_reaches M s t /\(moved=false->machine230_progresses M s t).
Proof.
 intro HB. exact(machine230_runtime_exec_sound M gap(machine230_runtime_box M values E)br
 (machine230_runtime_box_head M values E)(machine230_concrete_runtime_oracle M values E br HB)fuel target).
Qed.
Print Assumptions machine230_concrete_runtime_oracle.
Print Assumptions machine230_concrete_runtime_exec.