(** Agreement of actual counterprogram histories at arbitrary internal indices.
    The induction predicate is a literal PA formula. No standardness of the
    history length or of the configurations is assumed. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
 CodeExpressions NumericalProofs Program230PathPop Program230Configurations
 Program230Histories Program230InstructionFormula Program230HaltingSentence
 Program230Transition Program230LongPrefixes.
From FOL Require Import FullSyntax Arithmetics.
From K230 Require Import Prog230.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Definition program230_histories_agree_at M b c d e i :=
 forall j, (j<10)%nat -> exists value,
 beta M b c (program230_field_index M i j) value /\
 beta M d e (program230_field_index M i j) value.

Definition program230_histories_agree_formula (b c d e i:term):form :=
 program230_fields_formula 10 (fun j =>
  ∃(beta_formula b`[↑] c`[↑] (program230_field_index_term i j)`[↑] $0 ∧
    beta_formula d`[↑] e`[↑] (program230_field_index_term i j)`[↑] $0)).

Local Opaque holds beta_formula.

Lemma program230_histories_agree_formula_correct M rho b c d e i:
 holds M rho (program230_histories_agree_formula b c d e i) <->
 program230_histories_agree_at M (evalM M rho b) (evalM M rho c)
  (evalM M rho d) (evalM M rho e) (evalM M rho i).
Proof.
 unfold program230_histories_agree_formula,program230_histories_agree_at.
 rewrite program230_fields_formula_correct.
 assert (Hj:forall j,
  holds M rho (∃(beta_formula b`[↑] c`[↑] (program230_field_index_term i j)`[↑] $0 ∧
    beta_formula d`[↑] e`[↑] (program230_field_index_term i j)`[↑] $0)) <->
  exists value,
   beta M (evalM M rho b) (evalM M rho c)
    (program230_field_index M (evalM M rho i) j) value /\
   beta M (evalM M rho d) (evalM M rho e)
    (program230_field_index M (evalM M rho i) j) value).
 { intro j. rewrite holds_ex.
   assert (Hbody:forall value,
    holds M (value.:rho)
      (beta_formula b`[↑] c`[↑] (program230_field_index_term i j)`[↑] $0 ∧
       beta_formula d`[↑] e`[↑] (program230_field_index_term i j)`[↑] $0) <->
    beta M (evalM M rho b) (evalM M rho c)
      (program230_field_index M (evalM M rho i) j) value /\
    beta M (evalM M rho d) (evalM M rho e)
      (program230_field_index M (evalM M rho i) j) value).
   { intro value. rewrite holds_and,!beta_formula_correct,!pathpop_eval_up,
       program230_field_index_correct. reflexivity. }
   setoid_rewrite Hbody. reflexivity. }
 split;intros H j Hj10;apply (Hj j);apply H;exact Hj10.
Qed.

Lemma program230_histories_agree_states M b c d e i:
 program230_histories_agree_at M b c d e i <->
 forall s t, program230_state_at M b c i s ->
 program230_state_at M d e i t -> s=t.
Proof.
 split.
 -intros H s t HS HT. apply p230_configuration_ext;intros j Hj.
  destruct (H j Hj) as [value [HB HD]].
  transitivity value.
  +exact (beta_unique M b c (program230_field_index M i j) _ _ (HS j Hj) HB).
  +exact (beta_unique M d e (program230_field_index M i j) _ _ HD (HT j Hj)).
 -intro H. destruct (program230_state_at_total M b c i) as [s HS].
  destruct (program230_state_at_total M d e i) as [t HT].
  specialize (H s t HS HT);subst t.
  intros j Hj;exists (program230_field s j);split;[apply HS|apply HT];exact Hj.
Qed.

Definition program230_bounded_history_agreement M b c d e N L i :=
 coding_lt M i (succM M N) -> coding_lt M i (succM M L) ->
 program230_histories_agree_at M b c d e i.

Lemma program230_bounded_history_agreement_definable M b c d e N L:
 Definable1 M (program230_bounded_history_agreement M b c d e N L).
Proof.
 exists (Peano.sless $0 (σ $5) → Peano.sless $0 (σ $6) →
   program230_histories_agree_formula $1 $2 $3 $4 $0),
   (b.:c.:d.:e.:N.:L.:(fun _ => zeroM M)).
 intro i;unfold program230_bounded_history_agreement.
 rewrite !holds_imp,!less_formula_correct,program230_histories_agree_formula_correct.
 reflexivity.
Qed.

Theorem p230_histories_agree M b c d e N L start:
 program230_history M p230_instruction_formula b c N start ->
 program230_history M p230_instruction_formula d e L start ->
 forall i, coding_lt M i (succM M N) -> coding_lt M i (succM M L) ->
 program230_histories_agree_at M b c d e i.
Proof.
 intros [HB0 HB] [HD0 HD].
 apply (definable_induction M
   (program230_bounded_history_agreement M b c d e N L)
   (program230_bounded_history_agreement_definable M b c d e N L)).
 -intros _ _. apply program230_histories_agree_states;intros s t HS HT.
  transitivity start.
  +exact (program230_state_at_functional M b c (zeroM M) s start HS HB0).
  +exact (program230_state_at_functional M d e (zeroM M) start t HD0 HT).
 -intros i IH HN HL.
  apply (proj1 (coding_lt_succ_cancel M i N)) in HN.
  apply (proj1 (coding_lt_succ_cancel M i L)) in HL.
  apply program230_histories_agree_states;intros s t HS HT.
  destruct (program230_state_at_total M b c i) as [before HBbefore].
  destruct (program230_state_at_total M d e i) as [other HDother].
  assert (E:before=other).
  { apply (proj1 (program230_histories_agree_states M b c d e i)).
    -apply IH.
     +exact (coding_lt_trans M i N (succM M N) HN (coding_lt_succ M N)).
     +exact (coding_lt_trans M i L (succM M L) HL (coding_lt_succ M L)).
    -exact HBbefore.
    -exact HDother. }
  subst other. eapply p230_instruction_deterministic.
  +exact (HB i before s HN HBbefore HS).
  +exact (HD i before t HL HDother HT).
Qed.

Theorem p230_histories_states_equal M b c d e N L start i s t:
 program230_history M p230_instruction_formula b c N start ->
 program230_history M p230_instruction_formula d e L start ->
 coding_lt M i (succM M N) -> coding_lt M i (succM M L) ->
 program230_state_at M b c i s -> program230_state_at M d e i t -> s=t.
Proof.
 intros HB HD HN HL HS HT.
 exact (proj1 (program230_histories_agree_states M b c d e i)
   (p230_histories_agree M b c d e N L start HB HD i HN HL) s t HS HT).
Qed.

Theorem p230_history_halt_is_maximal M b c d e N L start:
 program230_history M p230_instruction_formula b c N start ->
 p230_counter_halt_at M b c N ->
 program230_history M p230_instruction_formula d e L start ->
 ~coding_lt M N L.
Proof.
 intros HB [last [Hlast Hhalt]] HD HNL.
 destruct (program230_state_at_total M d e N) as [atN HN].
 destruct (program230_state_at_total M d e (succM M N)) as [after Hafter].
 assert (E:last=atN).
 { exact (p230_histories_states_equal M b c d e N L start N last atN
    HB HD (coding_lt_succ M N)
    (coding_lt_trans M N L (succM M L) HNL (coding_lt_succ M L)) Hlast HN). }
 destruct HD as [_ Hstep].
 pose proof (Hstep N atN after HNL HN Hafter) as HS.
 rewrite <-E in HS. apply p230_instruction_formula_correct in HS.
 exact (program230_halt_excludes_step M p230 (program230_pc last)
   (program230_register last) (program230_register after) (program230_pc after) Hhalt HS).
Qed.

Definition p230_has_arbitrary_histories M :=
 forall N, exists b c,
 program230_history M p230_instruction_formula b c N (p230_initial_configuration M).

Theorem p230_nonhalting_iff_arbitrary_histories M:
 p230_counter_nonhalting M <-> p230_has_arbitrary_histories M.
Proof.
 split.
 -intros Hno N.
  destruct (p230_counter_nonhalting_long_prefixes M Hno N) as [b [c [HR _]]].
  exists b,c;exact HR.
 -intros Hall [b [c [N [HR Hhalt]]]].
  destruct (Hall (succM M N)) as [d [e HD]].
  exact (p230_history_halt_is_maximal M b c d e N (succM M N)
    (p230_initial_configuration M) HR Hhalt HD (coding_lt_succ M N)).
Qed.

Print Assumptions program230_histories_agree_formula_correct.
Print Assumptions program230_bounded_history_agreement_definable.
Print Assumptions p230_histories_agree.
Print Assumptions p230_histories_states_equal.
Print Assumptions p230_history_halt_is_maximal.
Print Assumptions p230_nonhalting_iff_arbitrary_histories.
