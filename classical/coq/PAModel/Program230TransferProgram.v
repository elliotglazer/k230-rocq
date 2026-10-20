(** Embedding the checked internal loop into an actual program occurrence.
    Premises describe finite tree syntax only; no iteration or run is assumed. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 Program230PathCode Program230PathPop Program230Read Program230Walk Program230Edges Program230Transition
 Program230Configurations Program230Histories Program230TransferCycle Program230TransferStates Program230TransferLoop.
From FOL Require Import FullSyntax Arithmetics.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Bool.Bool Lia.
Import ListNotations.
Unset Implicit Arguments.
Definition program230_program_history M p b c N start:=
 program230_state_at M b c(zeroM M)start /\
 forall i s t,coding_lt M i N->program230_state_at M b c i s->
 program230_state_at M b c(succM M i)t->
 Program230Transition.program230_step M p(program230_pc s)(program230_register s)
 (program230_register t)(program230_pc t).
Lemma program230_read_exact_path M P:
 program230_read M(program230_path_value M P)P(succM M(zeroM M)).
Proof.
 pose proof(program230_read_path M(length P)P)as H.
 rewrite program230_take_zeros_firstn in H by lia.
 now rewrite firstn_all,skipn_all in H.
Qed.
Lemma program230_read_path_zero M P:
 program230_read M(program230_path_value M P)(P++[false])(succM M(zeroM M)).
Proof.
 apply program230_read_app. exists(succM M(zeroM M));split;[apply program230_read_exact_path|].
 cbn[program230_read]. exists(succM M(zeroM M));split;[|reflexivity].
 left;repeat split;reflexivity.
Qed.
Definition program230_transfer_occurrence p P a b n m:=
 fol p(ENode(root p))P = Some(ENode n) /\
 nodes p n = (EDecnz a,ENode m) /\nodes p m = (EInc b,EContinue 2).
Lemma program230_transfer_occurrence_leaves p P a b n m:
 program230_transfer_occurrence p P a b n m->
 fol p(ENode(root p))(P++[false]) = Some(EDecnz a) /\
 fol p(ENode(root p))(P++[true;false]) = Some(EInc b) /\
 fol p(ENode(root p))(P++[true;true]) = Some(EContinue 2).
Proof.
 intros[HP[HN HM]]. rewrite !fol_app,HP.
 cbn[fol child]. rewrite HN. cbn[fst snd fol child]. rewrite HM;repeat split;reflexivity.
Qed.
Lemma program230_transfer_cycle_in_program M p P a b n m s t:
 program230_transfer_occurrence p P a b n m->
 program230_transfer_cycle M P a b s t->
 Program230Transition.program230_step M p(program230_pc s)(program230_register s)
 (program230_register t)(program230_pc t).
Proof.
 intros HO HC. destruct(program230_transfer_occurrence_leaves p P a b n m HO)as[HD[HI HK]].
 destruct HC as[[HP HE]|[[HP HE]|[HP HE]]].
 -exists(EDecnz a),(P++[false]),(succM M(zeroM M));split;[|exact HE].
  split;[rewrite HP;apply program230_read_path_zero|]. split;[exact HD|reflexivity].
 -exists(EInc b),(P++[true;false]),(succM M(zeroM M));split;[|exact HE].
  split;[|split;[exact HI|reflexivity]]. rewrite HP.
  replace(P++[true;false])with((P++[true])++[false])by(symmetry;exact(@List.app_assoc bool P (true::nil) (false::nil))).
  apply program230_read_path_zero.
 -exists(EContinue 2),(P++[true;true]),(succM M(zeroM M));split;[|exact HE].
  split;[rewrite HP;apply program230_read_exact_path|]. split;[exact HK|reflexivity].
Qed.
Theorem program230_transfer_history_in_program M p P a b n m u v N start:
 program230_transfer_occurrence p P a b n m->
 program230_history M(program230_transfer_formula P a b)u v N start->
 program230_program_history M p u v N start.
Proof.
 intros HO[H0 HS]. split;[exact H0|]. intros i s t Hi Hs Ht.
 apply(program230_transfer_cycle_in_program M p P a b n m s t HO).
 apply program230_transfer_formula_correct. exact(HS i s t Hi Hs Ht).
Qed.
Theorem program230_transfer_program_history M p P a b n m start count:
 (a<9)%nat->(b<9)%nat->a<>b->program230_transfer_occurrence p P a b n m->
 program230_pc start = program230_path_value M P->program230_register start a = count->
 exists u v final,program230_program_history M p u v(program230_transfer_time M count)start /\
 program230_state_at M u v(program230_transfer_time M count)final /\
 program230_pc final = program230_path_value M(inc_path P) /\
 program230_register final a = zeroM M /\
 program230_register final b = addM M(program230_register start b)count /\
 (forall i,(i<9)%nat->i<>a->i<>b->program230_register final i = program230_register start i).
Proof.
 intros Ha Hb Hab HO HP HA.
 destruct(program230_transfer_loop M P a b Ha Hb Hab start count HP HA)
 as[u[v[final[HR HF]]]]. exists u,v,final. split;[|exact HF].
 exact(program230_transfer_history_in_program M p P a b n m u v(program230_transfer_time M count)start HO HR).
Qed.
Print Assumptions program230_transfer_history_in_program.
Print Assumptions program230_transfer_program_history.
