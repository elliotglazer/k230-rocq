(** A finite arithmetic disjunction records exactly the initial PC and
    the possible post-leaf PCs. No external path is quantified inside the PA
    formula used later by induction. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs TM230BinaryStep Program230PathCode
 Program230Edges TM230LogicalSites TM230DispatchEdge.
From FOL Require Import FullSyntax Arithmetics.
From K230 Require RM RMEquiv.
From Stdlib Require Import Lists.List Lia Bool.Bool.
Import ListNotations.
Unset Implicit Arguments.
Definition machine230_post_paths Q(e:K230.RM.edge):list(list bool):=
 match e with
 |K230.RM.EInc _=>[K230.RM.inc_path Q]
 |K230.RM.EDecnz _=>[K230.RM.brk 1 Q;K230.RM.inc_path Q]
 |K230.RM.EBreak k=>[K230.RM.brk k Q]
 |K230.RM.EContinue k=>[K230.RM.cont k Q]
 |_=>[] end.
Definition machine230_control_candidates(leaves:list(list bool*K230.RM.edge)):=
 []::flat_map(fun qe=>machine230_post_paths(fst qe)(snd qe))leaves.
Definition machine230_clean_control M leaves depth pc:=exists P,
 In P(machine230_control_candidates leaves) /\depth=code_numeral M(length P) /\pc=program230_path_value M P.
Fixpoint machine230_control_list_formula(paths:list(list bool))(depth pc:term):form:=
 match paths with
 |[]=>⊥
 |P::paths=>(depth==num(length P) ∧pc==program230_path_term P) ∨machine230_control_list_formula paths depth pc
 end.
Definition machine230_clean_control_formula leaves depth pc:=
 machine230_control_list_formula(machine230_control_candidates leaves)depth pc.
Lemma machine230_control_holds_bot M rho:holds M rho ⊥<->False.
Proof. reflexivity. Qed.
Local Opaque holds.
Lemma machine230_control_list_formula_correct M rho paths depth pc:
 holds M rho(machine230_control_list_formula paths depth pc)<->
 exists P,In P paths /\evalM M rho depth=code_numeral M(length P) /\evalM M rho pc=program230_path_value M P.
Proof.
 induction paths as[|P paths IH].
 -cbn[machine230_control_list_formula]. rewrite machine230_control_holds_bot.
  split;[tauto|intros[Q[H _]];contradiction].
 -cbn[machine230_control_list_formula]. rewrite holds_or,holds_and.
  rewrite !machine230_holds_equal,code_eval_num,program230_path_term_correct,IH.
  split.
  +intros[[HD HP]|[Q[HQ[HD HP]]]].
   *exists P;split;[now left|auto].
   *exists Q;split;[now right|auto].
  +intros[Q[[HQ|HQ][HD HP]]];[subst Q;left;auto|right;exists Q;auto].
Qed.
Theorem machine230_clean_control_formula_correct M rho leaves depth pc:
 holds M rho(machine230_clean_control_formula leaves depth pc)<->
 machine230_clean_control M leaves(evalM M rho depth)(evalM M rho pc).
Proof. apply machine230_control_list_formula_correct. Qed.
Theorem machine230_clean_control_initial M leaves:
 machine230_clean_control M leaves(zeroM M)(code_numeral M 1).
Proof. exists[];split;[now left|split;reflexivity]. Qed.
Lemma machine230_post_path_clean p Q e P:
 K230.RMEquiv.fol p(K230.RM.ENode(K230.RM.root p))Q=Some e ->K230.RMEquiv.is_node e=false ->
 In P(machine230_post_paths Q e)->K230.RMEquiv.clean p P.
Proof.
 intros HF Hleaf HI. destruct e;cbn[machine230_post_paths]in HI;try contradiction.
 -destruct HI as[<-|[]]. apply(K230.RMEquiv.clean_inc p Q(K230.RM.EInc r)Q (@nil bool) HF Hleaf);now rewrite app_nil_r.
 -destruct HI as[<-|[<-|[]]].
  +unfold K230.RM.brk. destruct(K230.RMEquiv.strip_path_prefix false 1 Q)as[T ET].
   exact(K230.RMEquiv.clean_inc p Q(K230.RM.EDecnz r)(K230.RM.strip_path false 1 Q)T HF Hleaf ET).
  +apply(K230.RMEquiv.clean_inc p Q(K230.RM.EDecnz r)Q (@nil bool) HF Hleaf);now rewrite app_nil_r.
 -destruct HI as[<-|[]]. unfold K230.RM.brk.
  destruct(K230.RMEquiv.strip_path_prefix false k Q)as[T ET].
  exact(K230.RMEquiv.clean_inc p Q(K230.RM.EBreak k)(K230.RM.strip_path false k Q)T HF Hleaf ET).
 -destruct HI as[<-|[]]. unfold K230.RM.cont.
  destruct(K230.RMEquiv.strip_path_prefix true k Q)as[T ET].
  exact(K230.RMEquiv.clean_prefix p Q(K230.RM.EContinue k)(K230.RM.strip_path true k Q)T HF ET).
Qed.
Theorem machine230_control_candidates_clean p leaves:
 (forall Q e,In(Q,e)leaves->K230.RMEquiv.fol p(K230.RM.ENode(K230.RM.root p))Q=Some e /\K230.RMEquiv.is_node e=false)->
 forall P,In P(machine230_control_candidates leaves)->K230.RMEquiv.clean p P.
Proof.
 intros HL P[HP|HP].
 -subst P;intros e d HW i Hi;unfold K230.RM.bit;destruct i;reflexivity.
 -apply in_flat_map in HP. destruct HP as[[Q e][HQ HP]].
  destruct(HL Q e HQ)as[HF HE];exact(machine230_post_path_clean p Q e P HF HE HP).
Qed.
Theorem machine230_control_candidates_bound leaves bound:
 (forall Q e,In(Q,e)leaves->(length Q<=bound)%nat)->
 forall P,In P(machine230_control_candidates leaves)->(length P<=bound)%nat.
Proof.
 intros HL P[HP|HP];[subst P;cbn;lia|].
 apply in_flat_map in HP. destruct HP as[[Q e][HQ HP]]. specialize(HL Q e HQ). change(length Q<=bound)%nat in HL.
 destruct e;cbn[machine230_post_paths]in HP;try contradiction.
 -destruct HP as[<-|[]]. pose proof(machine230_edge_path_length Q(K230.RM.EInc r)false);cbn[machine230_edge_path]in H;cbn[fst snd];lia.
 -destruct HP as[<-|[<-|[]]].
  +pose proof(machine230_edge_path_length Q(K230.RM.EDecnz r)true);cbn[machine230_edge_path]in H;cbn[fst snd];lia.
  +pose proof(machine230_edge_path_length Q(K230.RM.EDecnz r)false);cbn[machine230_edge_path]in H;cbn[fst snd];lia.
 -destruct HP as[<-|[]]. pose proof(machine230_edge_path_length Q(K230.RM.EBreak k)false);cbn[machine230_edge_path]in H;cbn[fst snd];lia.
 -destruct HP as[<-|[]]. pose proof(machine230_edge_path_length Q(K230.RM.EContinue k)false);cbn[machine230_edge_path]in H;cbn[fst snd];lia.
Qed.
Theorem machine230_edge_candidate M leaves Q e R T pc z:
 In(Q,e)leaves->program230_edge_step M Q e R T pc ->
 In(machine230_edge_path Q e z)(machine230_control_candidates leaves).
Proof.
 intros HQ HE. right;apply in_flat_map;exists(Q,e);split;[exact HQ|]. cbn[fst snd].
 destruct e;cbn[program230_edge_step]in HE;try contradiction;
 cbn[machine230_post_paths machine230_edge_path];auto;destruct z;auto.
 all:cbn;tauto.
Qed.
Print Assumptions machine230_clean_control_formula_correct.
Print Assumptions machine230_control_candidates_clean.
Print Assumptions machine230_control_candidates_bound.
Print Assumptions machine230_edge_candidate.
