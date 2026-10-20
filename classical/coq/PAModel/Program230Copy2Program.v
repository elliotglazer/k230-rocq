(** Exact public-program interpretation of the two-target copying loop. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions NumericalProofs
 Program230PathCode Program230PathPop Program230Read Program230Walk Program230Edges Program230Transition
 Program230Configurations Program230Histories Program230TransferProgram Program230Copy2States Program230Copy2Loop.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.
Lemma program230_read_concat_path M P Q:
 program230_read M(program230_path_value M(P++Q))P(program230_path_value M Q).
Proof.
 induction P as[|b P IH];[reflexivity|]. cbn[app program230_read].
 exists(program230_path_value M(P++Q));split;[|exact IH].
 exact(program230_path_pop_list M(b::P++Q)).
Qed.
Lemma program230_read_path_two_zeros M P:
 program230_read M(program230_path_value M P)(P++[false;false])(succM M(zeroM M)).
Proof.
 apply program230_read_app;exists(succM M(zeroM M));split;[apply program230_read_exact_path|].
 cbn[program230_read]. exists(succM M(zeroM M));split;[left;repeat split;reflexivity|].
 exists(succM M(zeroM M));split;[left;repeat split;reflexivity|reflexivity].
Qed.
Definition program230_copy2_occurrence p P a b c n m k:=
 fol p(ENode(root p))P = Some(ENode n) /\nodes p n = (EDecnz a,ENode m) /\
 nodes p m = (EInc b,ENode k) /\nodes p k = (EInc c,EContinue 3).
Lemma program230_copy2_occurrence_leaves p P a b c n m k:
 program230_copy2_occurrence p P a b c n m k->
 fol p(ENode(root p))(P++[false]) = Some(EDecnz a) /\
 fol p(ENode(root p))(P++[true;false]) = Some(EInc b) /\
 fol p(ENode(root p))(P++[true;true;false]) = Some(EInc c) /\
 fol p(ENode(root p))(P++[true;true;true]) = Some(EContinue 3).
Proof.
 intros[HP[HN[HM HK]]]. rewrite !fol_app,HP. cbn[fol child]. rewrite HN.
 cbn[fst snd fol child]. rewrite HM. cbn[fst snd fol child]. rewrite HK.
 repeat split;reflexivity.
Qed.
Lemma program230_copy2_cycle_in_program M p P a b c n m k s t:
 program230_copy2_occurrence p P a b c n m k->program230_copy2_cycle M P a b c s t->
 Program230Transition.program230_step M p(program230_pc s)(program230_register s)(program230_register t)(program230_pc t).
Proof.
 intros HO HC;destruct(program230_copy2_occurrence_leaves p P a b c n m k HO)as[HD[HB[HC' HK]]].
 destruct HC as[[HP HE]|[[HP HE]|[[HP HE]|[HP HE]]]].
 -exists(EDecnz a),(P++[false]),(succM M(zeroM M));split;[|exact HE].
  split;[rewrite HP;apply program230_read_path_zero|]. split;[exact HD|reflexivity].
 -exists(EInc b),(P++[true;false]),(succM M(zeroM M));split;[|exact HE].
  split;[|split;[exact HB|reflexivity]]. rewrite HP.
  replace(P++[true;false])with((P++[true])++[false])
   by(symmetry;exact(@List.app_assoc bool P (true::nil)(false::nil))).
  apply program230_read_path_zero.
 -exists(EInc c),(P++[true;true;false]),(succM M(zeroM M));split;[|exact HE].
  split;[|split;[exact HC'|reflexivity]]. rewrite HP.
  replace(P++[true;true;false])with((P++[true;true])++[false])
   by(symmetry;exact(@List.app_assoc bool P (true::true::nil)(false::nil))).
  apply program230_read_path_zero.
 -exists(EContinue 3),(P++[true;true;true]),(succM M(zeroM M));split;[|exact HE].
  split;[rewrite HP;apply program230_read_exact_path|]. split;[exact HK|reflexivity].
Qed.
Theorem program230_copy2_program_history M p P a b c n m k start count:
 (a<9)%nat->(b<9)%nat->(c<9)%nat->a<>b->a<>c->b<>c->
 program230_copy2_occurrence p P a b c n m k->
 program230_pc start = program230_path_value M P->program230_register start a = count->
 exists u v final,program230_program_history M p u v(program230_copy2_time M count)start /\
 program230_state_at M u v(program230_copy2_time M count)final /\
 program230_pc final = program230_path_value M(inc_path P) /\
 program230_register final a = zeroM M /\
 program230_register final b = addM M(program230_register start b)count /\
 program230_register final c = addM M(program230_register start c)count /\
 (forall i,(i<9)%nat->i<>a->i<>b->i<>c->program230_register final i = program230_register start i).
Proof.
 intros Ha Hb Hc Hab Hac Hbc HO HP HA.
 destruct(program230_copy2_loop M P a b c Ha Hb Hc Hab Hac Hbc start count HP HA)as[u[v[final[HR HF]]]].
 exists u,v,final;split;[|exact HF]. destruct HR as[H0 HS];split;[exact H0|].
 intros i s t Hi Hs Ht;apply(program230_copy2_cycle_in_program M p P a b c n m k s t HO).
 apply program230_copy2_formula_correct;exact(HS i s t Hi Hs Ht).
Qed.
Print Assumptions program230_copy2_program_history.
