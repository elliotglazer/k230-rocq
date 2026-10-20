(** Compositional free-variable bounds; the complete finite leaf list is
    never expanded in these proofs. *)
From PAModel Require Import SentenceBounds TM230LiteralActions Program230PathCode
 Program230PathPop Program230Read Program230Edges Program230LeafFormula Program230HaltingFormula.
From FOL Require Import FullSyntax Arithmetics.
From Undecidability.FOL.Syntax Require Import Bounded.
From K230 Require Import RM RMEquiv Prog230.
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
Import ListNotations.
Unset Implicit Arguments.

Lemma program230_term_boundb_complete k t : bounded_t k t ->term_boundb k t=true.
Proof.
 intro H;induction H as[x Hx|f v Hv IH].
 -cbn[term_boundb];apply Nat.ltb_lt;exact Hx.
 -change(vector_allb(term_boundb k)v=true). apply vector_allb_true;exact IH.
Qed.
Lemma program230_term_boundb_shift k t : term_boundb k t=true ->term_boundb(S k)t`[↑]=true.
Proof.
 intro H. apply program230_term_boundb_complete.
 eapply (subst_bounded_max_t (ff:=falsity_on) (n:=k)).
 -intros i Hi;change (bounded_t (S k) ($(S i)));constructor;lia.
 -apply term_boundb_sound;exact H.
Qed.
Lemma program230_num_boundb k n : term_boundb k(num n)=true.
Proof. induction n;[reflexivity|]. change (term_boundb k (num n) && true=true);now rewrite IHn. Qed.
Lemma program230_path_term_boundb k Q : term_boundb k(program230_path_term Q)=true.
Proof. induction Q as[|b Q IH];cbn[program230_path_term term_boundb];[reflexivity|].
 destruct b;cbn[machine230_bit];rewrite !program230_num_boundb,IH;reflexivity.
Qed.
Lemma program230_equal_boundb k t u : term_boundb k t=true ->term_boundb k u=true ->
 formula_boundb k(t==u)=true.
Proof. intros HT HU;cbn[formula_boundb vector_allb];now rewrite HT,HU. Qed.
Lemma program230_and_boundb k a b : formula_boundb k a=true ->formula_boundb k b=true ->
 formula_boundb k(a ∧b)=true.
Proof. intros HA HB;change(formula_boundb k a &&formula_boundb k b=true);now rewrite HA,HB. Qed.
Lemma program230_or_boundb k a b : formula_boundb k a=true ->formula_boundb k b=true ->
 formula_boundb k(a ∨b)=true.
Proof. intros HA HB;change(formula_boundb k a &&formula_boundb k b=true);now rewrite HA,HB. Qed.

Lemma program230_pop_boundb k code head rest :
 term_boundb k code=true ->term_boundb k head=true ->term_boundb k rest=true ->
 formula_boundb k(program230_path_pop_formula code head rest)=true.
Proof.
 intros HC HH HR.
 pose proof(program230_term_boundb_shift k code HC)as HC'.
 pose proof(program230_term_boundb_shift k head HH)as HH'.
 pose proof(program230_term_boundb_shift k rest HR)as HR'.
 unfold program230_path_pop_formula.
 cbn[formula_boundb vector_allb term_boundb];now rewrite HC,HH,HR,HC',HH',HR'.
Qed.
Lemma program230_read_boundb k code Q rest :
 term_boundb k code=true ->term_boundb k rest=true ->
 formula_boundb k(program230_read_formula code Q rest)=true.
Proof.
 induction Q as[|b Q IH]in k,code,rest|-*;intros HC HR.
 -apply program230_equal_boundb;assumption.
 -change(formula_boundb(S k)(program230_path_pop_formula code`[↑](num(machine230_bit b))$0 ∧
    program230_read_formula $0 Q rest`[↑])=true).
  apply program230_and_boundb.
  +apply program230_pop_boundb;[apply program230_term_boundb_shift;exact HC|apply program230_num_boundb|reflexivity].
  +apply IH;[reflexivity|apply program230_term_boundb_shift;exact HR].
Qed.
Lemma program230_reached_boundb k Q pc : term_boundb k pc=true ->
 formula_boundb k(program230_path_reached_formula Q pc)=true.
Proof. intro H;apply program230_read_boundb;[apply program230_term_boundb_shift;exact H|reflexivity]. Qed.
Lemma program230_all_boundb k n F :
 (forall i,(i<n)%nat->formula_boundb k(F i)=true) ->
 formula_boundb k(program230_all_formula n F)=true.
Proof.
 induction n as[|n IH];intro H;[reflexivity|].
 apply program230_and_boundb;[apply H;lia|apply IH;intros i Hi;apply H;lia].
Qed.
Lemma program230_same_boundb k before after :
 (forall i,(i<9)%nat->term_boundb k(before i)=true) ->
 (forall i,(i<9)%nat->term_boundb k(after i)=true) ->
 formula_boundb k(program230_same_formula before after)=true.
Proof. intros HB HA;apply program230_all_boundb;intros i Hi;apply program230_equal_boundb;auto. Qed.
Lemma program230_update_boundb k before after r value :
 (forall i,(i<9)%nat->term_boundb k(before i)=true) ->
 (forall i,(i<9)%nat->term_boundb k(after i)=true) ->term_boundb k value=true ->
 formula_boundb k(program230_update_formula before after r value)=true.
Proof.
 intros HB HA HV;apply program230_all_boundb;intros i Hi;apply program230_equal_boundb;[auto|].
 destruct(Nat.eqb i r);auto.
Qed.
Lemma program230_positive_boundb k Q before after r pc' :
 (r<9)%nat ->
 (forall i,(i<9)%nat->term_boundb k(before i)=true) ->
 (forall i,(i<9)%nat->term_boundb k(after i)=true) ->term_boundb k pc'=true ->
 formula_boundb k(program230_positive_formula Q before after r pc')=true.
Proof.
 intros Hr HB HA HP;unfold program230_positive_formula.
 change (formula_boundb (S k) ((before r)`[↑]==σ $0 ∧
   (pc'`[↑]==(program230_path_term(inc_path Q))`[↑] ∧
    program230_update_formula (fun i => (before i)`[↑]) (fun i => (after i)`[↑]) r $0))=true).
 apply program230_and_boundb.
 -apply program230_equal_boundb;[apply program230_term_boundb_shift;auto|reflexivity].
 -apply program230_and_boundb.
  +apply program230_equal_boundb;apply program230_term_boundb_shift;[exact HP|apply program230_path_term_boundb].
  +apply program230_update_boundb;[intros i Hi;apply program230_term_boundb_shift;auto|
    intros i Hi;apply program230_term_boundb_shift;auto|reflexivity].
Qed.
Lemma program230_edge_boundb k Q e before after pc' :
 (forall i,(i<9)%nat->term_boundb k(before i)=true) ->
 (forall i,(i<9)%nat->term_boundb k(after i)=true) ->term_boundb k pc'=true ->
 formula_boundb k(program230_edge_formula Q e before after pc')=true.
Proof.
 intros HB HA HP;destruct e as[n|r|r|j|j|];cbn[program230_edge_formula];try reflexivity.
 -destruct(Nat.ltb r 9)eqn:Hr;[apply Nat.ltb_lt in Hr|reflexivity].
  apply program230_and_boundb.
  +apply program230_equal_boundb;[exact HP|apply program230_path_term_boundb].
  +apply program230_update_boundb;[exact HB|exact HA|].
   cbn[term_boundb];rewrite(HB r Hr);reflexivity.
 -destruct(Nat.ltb r 9)eqn:Hr;[apply Nat.ltb_lt in Hr|reflexivity].
  apply program230_or_boundb.
  +apply program230_and_boundb.
   *apply program230_equal_boundb;[auto|reflexivity].
   *apply program230_and_boundb.
    --apply program230_equal_boundb;[exact HP|apply program230_path_term_boundb].
    --apply program230_same_boundb;assumption.
  +apply program230_positive_boundb;assumption.
 -apply program230_and_boundb;[apply program230_equal_boundb;[exact HP|apply program230_path_term_boundb]|apply program230_same_boundb;assumption].
 -apply program230_and_boundb;[apply program230_equal_boundb;[exact HP|apply program230_path_term_boundb]|apply program230_same_boundb;assumption].
Qed.
Lemma program230_leaf_step_boundb k Q e pc before after pc' :
 term_boundb k pc=true ->
 (forall i,(i<9)%nat->term_boundb k(before i)=true) ->
 (forall i,(i<9)%nat->term_boundb k(after i)=true) ->term_boundb k pc'=true ->
 formula_boundb k(program230_leaf_step_formula Q e pc before after pc')=true.
Proof. intros HC HB HA HP;apply program230_and_boundb;[apply program230_reached_boundb;exact HC|apply program230_edge_boundb;assumption]. Qed.
Lemma program230_leaves_step_boundb k L pc before after pc' :
 term_boundb k pc=true ->
 (forall i,(i<9)%nat->term_boundb k(before i)=true) ->
 (forall i,(i<9)%nat->term_boundb k(after i)=true) ->term_boundb k pc'=true ->
 formula_boundb k(program230_leaves_step_formula L pc before after pc')=true.
Proof.
 intros HC HB HA HP;induction L as[|[Q e]L IH];[reflexivity|].
 apply program230_or_boundb;[apply program230_leaf_step_boundb;assumption|exact IH].
Qed.
Theorem program230_program_step_boundb k p pc before after pc' :
 term_boundb k pc=true ->
 (forall i,(i<9)%nat->term_boundb k(before i)=true) ->
 (forall i,(i<9)%nat->term_boundb k(after i)=true) ->term_boundb k pc'=true ->
 formula_boundb k(program230_program_step_formula p pc before after pc')=true.
Proof. apply program230_leaves_step_boundb. Qed.
Lemma program230_leaf_halt_boundb k Q e pc :term_boundb k pc=true ->
 formula_boundb k(program230_leaf_halt_formula Q e pc)=true.
Proof. intro H;destruct e;try reflexivity;apply program230_reached_boundb;exact H. Qed.
Lemma program230_leaves_halt_boundb k L pc :term_boundb k pc=true ->
 formula_boundb k(program230_leaves_halt_formula L pc)=true.
Proof. intro H;induction L as[|[Q e]L IH];[reflexivity|];apply program230_or_boundb;[apply program230_leaf_halt_boundb;exact H|exact IH]. Qed.
Theorem program230_program_halt_boundb k p pc :term_boundb k pc=true ->
 formula_boundb k(program230_program_halt_formula p pc)=true.
Proof. apply program230_leaves_halt_boundb. Qed.

Corollary p230_instruction_boundb :
 formula_boundb 20(p230_program_step_formula $0 (fun i => $ (S i)) (fun i => $ (11+i)) $10)=true.
Proof.
 apply program230_program_step_boundb;try reflexivity;
 intros i Hi;cbn[term_boundb];apply Nat.ltb_lt;lia.
Qed.
Corollary p230_instruction_bounded :
 bounded 20(p230_program_step_formula $0 (fun i => $ (S i)) (fun i => $ (11+i)) $10).
Proof. apply formula_boundb_sound;exact p230_instruction_boundb. Qed.
Corollary p230_halt_boundb :formula_boundb 1(p230_program_halt_formula $0)=true.
Proof. apply program230_program_halt_boundb;reflexivity. Qed.
Corollary p230_halt_bounded :bounded 1(p230_program_halt_formula $0).
Proof. apply formula_boundb_sound;exact p230_halt_boundb. Qed.
Print Assumptions program230_program_step_boundb.
Print Assumptions program230_program_halt_boundb.
Print Assumptions p230_instruction_bounded.
Print Assumptions p230_halt_bounded.
