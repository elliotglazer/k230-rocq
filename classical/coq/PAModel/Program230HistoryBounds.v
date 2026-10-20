(** Compositional bounds for actual ten-field histories, followed by
    closedness of the exact seeded halting and nonhalting formulas. *)
From PAModel Require Import Model FiniteCoding SentenceBounds Program230FormulaBounds
 Program230Configurations Program230Histories Program230InstructionFormula Program230HaltingFormula Program230HaltingSentence.
From FOL Require Import FullSyntax Arithmetics.
From Undecidability.FOL.Syntax Require Import Bounded.
From Stdlib Require Import Lists.List Bool.Bool Arith.Arith Lia.
Unset Implicit Arguments.

Lemma program230_formula_boundb_complete {ff} k(phi:form ff):
 bounded k phi ->formula_boundb k phi = true.
Proof.
 intro H;induction H as [ff n P v Hv|op ff n a b Ha IHa Hb IHb|op ff n a Ha IHa|n].
 -change(vector_allb(term_boundb n)v = true);apply vector_allb_true.
  intros t Ht;apply program230_term_boundb_complete;auto.
 -change(formula_boundb n a &&formula_boundb n b = true);now rewrite IHa,IHb.
 -exact IHa.
 -reflexivity.
Qed.
Lemma program230_imp_boundb k a b:formula_boundb k a = true ->formula_boundb k b = true ->
 formula_boundb k(a→b) = true.
Proof. intros HA HB;change(formula_boundb k a &&formula_boundb k b = true);now rewrite HA,HB. Qed.
Lemma program230_sless_boundb k x y:term_boundb k x = true ->term_boundb k y = true ->
 formula_boundb k(Peano.sless x y) = true.
Proof.
 intros HX HY;pose proof(program230_term_boundb_shift k x HX)as HX'.
 pose proof(program230_term_boundb_shift k y HY)as HY'.
 unfold Peano.sless;cbn[formula_boundb vector_allb term_boundb];now rewrite HX',HY'.
Qed.
Lemma program230_remainder_boundb k b q r:
 term_boundb k b = true ->term_boundb k q = true ->term_boundb k r = true ->
 formula_boundb k(remainder_formula b q r) = true.
Proof.
 intros HB HQ HR;unfold remainder_formula;apply program230_and_boundb.
 -apply program230_sless_boundb;assumption.
 -pose proof(program230_term_boundb_shift k b HB)as HB'.
  pose proof(program230_term_boundb_shift k q HQ)as HQ'.
  pose proof(program230_term_boundb_shift k r HR)as HR'.
  cbn[formula_boundb vector_allb term_boundb];now rewrite HB',HQ',HR'.
Qed.
Lemma program230_beta_boundb k b c i r:
 term_boundb k b = true ->term_boundb k c = true ->term_boundb k i = true ->term_boundb k r = true ->
 formula_boundb k(beta_formula b c i r) = true.
Proof.
 intros HB HC HI HR;apply program230_remainder_boundb;[exact HB| |exact HR].
 cbn[term_boundb];now rewrite HI,HC.
Qed.
Lemma program230_field_index_boundb k i j:term_boundb k i = true ->
 term_boundb k(program230_field_index_term i j) = true.
Proof. intro HI;unfold program230_field_index_term;cbn[term_boundb];now rewrite !program230_num_boundb,HI. Qed.
Lemma program230_fields_boundb k n F:
 (forall j,(j<n)%nat->formula_boundb k(F j) = true)->
 formula_boundb k(program230_fields_formula n F) = true.
Proof.
 induction n as[|n IH];intro H;[reflexivity|].
 apply program230_and_boundb;[apply H;lia|apply IH;intros j Hj;apply H;lia].
Qed.
Definition program230_config_boundb k(s:program230_configuration term):Prop:=
 forall j,(j<10)%nat->term_boundb k(program230_field s j) = true.
Lemma program230_state_at_boundb k b c i s:
 term_boundb k b = true ->term_boundb k c = true ->term_boundb k i = true ->program230_config_boundb k s ->
 formula_boundb k(program230_state_at_formula b c i s) = true.
Proof.
 intros HB HC HI HS;apply program230_fields_boundb;intros j Hj.
 apply program230_beta_boundb;[exact HB|exact HC|apply program230_field_index_boundb;exact HI|apply HS;exact Hj].
Qed.
Lemma program230_lift_boundb n k t:term_boundb k t = true ->term_boundb(n+k)(program230_lift n t) = true.
Proof. intro H;induction n as[|n IH];[exact H|]. apply program230_term_boundb_shift;exact IH. Qed.
Lemma program230_step_boundb k step s t:
 formula_boundb 20 step = true ->program230_config_boundb k s ->program230_config_boundb k t ->
 formula_boundb k(program230_step_formula step s t) = true.
Proof.
 intros Hstep HS HT;apply program230_formula_boundb_complete.
 unfold program230_step_formula;eapply (subst_bounded_max (n:=20)).
 -intros j Hj;apply term_boundb_sound;unfold program230_transition_env.
  destruct(Nat.ltb j 10)eqn:E10;[apply Nat.ltb_lt in E10;apply HS;exact E10|].
  destruct(Nat.ltb j 20)eqn:E20.
  +apply Nat.ltb_ge in E10;apply HT;lia.
  +apply Nat.ltb_ge in E20;lia.
 -apply formula_boundb_sound;exact Hstep.
Qed.
Local Opaque program230_state_at_formula program230_step_formula.
Theorem program230_history_boundb k step b c N start:
 formula_boundb 20 step = true ->term_boundb k b = true ->term_boundb k c = true ->term_boundb k N = true ->
 program230_config_boundb k start ->formula_boundb k(program230_history_formula step b c N start) = true.
Proof.
 intros Hstep HB HC HN HS.
 assert(HBefore:program230_config_boundb(21+k)program230_history_before).
 {intros j Hj;unfold program230_history_before;rewrite program230_config_of_fields by exact Hj.
  cbn[term_boundb];apply Nat.ltb_lt;lia. }
 assert(HAfter:program230_config_boundb(21+k)program230_history_after).
 {intros j Hj;unfold program230_history_after;rewrite program230_config_of_fields by exact Hj.
  cbn[term_boundb];apply Nat.ltb_lt;lia. }
 unfold program230_history_formula;apply program230_and_boundb.
 -apply program230_state_at_boundb;try assumption;reflexivity.
 -change(formula_boundb(21+k)
  (Peano.sless $20(program230_lift 21 N)→
   program230_state_at_formula(program230_lift 21 b)(program230_lift 21 c)$20 program230_history_before→
   program230_state_at_formula(program230_lift 21 b)(program230_lift 21 c)(σ $20)program230_history_after→
   program230_step_formula step program230_history_before program230_history_after) = true).
  apply program230_imp_boundb.
  +apply program230_sless_boundb;[reflexivity|apply program230_lift_boundb;exact HN].
  +apply program230_imp_boundb.
   *apply program230_state_at_boundb;[apply program230_lift_boundb;exact HB|
     apply program230_lift_boundb;exact HC|reflexivity|exact HBefore].
   *apply program230_imp_boundb.
    --apply program230_state_at_boundb;[apply program230_lift_boundb;exact HB|
      apply program230_lift_boundb;exact HC|reflexivity|exact HAfter].
    --apply program230_step_boundb;assumption.
Qed.

Lemma p230_initial_terms_boundb k:program230_config_boundb k p230_initial_terms.
Proof. intros j Hj;do 10(destruct j;[reflexivity|]);lia. Qed.
Lemma p230_counter_halt_at_boundb k b c N:
 term_boundb k b = true ->term_boundb k c = true ->term_boundb k N = true ->
 formula_boundb k(p230_counter_halt_at_formula b c N) = true.
Proof.
 intros HB HC HN;unfold p230_counter_halt_at_formula.
 change(formula_boundb(S k)(beta_formula b`[↑] c`[↑](program230_field_index_term N`[↑] 0)$0 ∧p230_program_halt_formula $0) = true).
 apply program230_and_boundb.
 -apply program230_beta_boundb;[apply program230_term_boundb_shift;exact HB|
   apply program230_term_boundb_shift;exact HC|apply program230_field_index_boundb;apply program230_term_boundb_shift;exact HN|reflexivity].
 -apply program230_program_halt_boundb;reflexivity.
Qed.
Theorem p230_counter_halting_formula_boundb:formula_boundb 0 p230_counter_halting_formula = true.
Proof.
 unfold p230_counter_halting_formula.
 change(formula_boundb 3(program230_history_formula p230_instruction_formula $2 $1 $0 p230_initial_terms ∧
  p230_counter_halt_at_formula $2 $1 $0) = true).
 apply program230_and_boundb.
 -apply program230_history_boundb.
  +unfold p230_instruction_formula;exact p230_instruction_boundb.
  +reflexivity.
  +reflexivity.
  +reflexivity.
  +apply p230_initial_terms_boundb.
 -apply p230_counter_halt_at_boundb;reflexivity.
Qed.
Theorem p230_counter_halting_formula_closed:closed p230_counter_halting_formula.
Proof. apply formula_boundb_sound;exact p230_counter_halting_formula_boundb. Qed.
Theorem p230_counter_nonhalting_formula_boundb:formula_boundb 0 p230_counter_nonhalting_formula = true.
Proof.
 change(formula_boundb 0 p230_counter_halting_formula &&true = true).
 now rewrite p230_counter_halting_formula_boundb.
Qed.
Theorem p230_counter_nonhalting_formula_closed:closed p230_counter_nonhalting_formula.
Proof. apply formula_boundb_sound;exact p230_counter_nonhalting_formula_boundb. Qed.
Print Assumptions program230_history_boundb.
Print Assumptions p230_counter_halting_formula_closed.
Print Assumptions p230_counter_nonhalting_formula_closed.
