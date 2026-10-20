(** The literal public machine and the exact seeded counterprogram halt
    equivalently in every PA model, including at nonstandard coded lengths. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
 TM230BinaryStep TM230RunArithmetic TM230RunComposition TM230StandardRun TM230StandardPacking
 TM230ExactPaths TM230TerminalPaths TM230SeededSimulation
 Program230Configurations Program230Histories Program230HaltingSentence Program230LongPrefixes.
From Stdlib Require Import Logic.Classical_Prop PArith setoid_ring.Ring.
Unset Implicit Arguments.
Section Equivalence.
Variable M:Model.
Local Notation Z:=(zeroM M).
Local Notation S:=(succM M).
Local Notation N:=(code_numeral M).
Local Infix "+":=(addM M).
Add Ring counter_equivalence_ring:(model_semiring M).
Theorem machine230_halting_implies_p230_counter:
 machine230_arithmetical_halts M ->p230_counter_halting M.
Proof.
 intros[b[c[n[HR HH]]]]. apply NNPP;intro Hno.
 destruct(machine230_state_at_total M b c n)as[halted HT].
 assert(Hq:machine230_state halted=N 230).
 {exact(beta_unique M b c(machine230_state_index M n 0)(machine230_state halted)(N 230)(proj1 HT)HH). }
 destruct(p230_counter_nonhalting_long_prefixes M Hno(S n))as[pb[pc[HP Hpositive]]].
 destruct(machine230_seeded_instruction_history M pb pc(S n)HP)
  as[final[ending[time[slack[Hfinal[Hpath[Htime Hsim]]]]]]].
 assert(Hless:coding_lt M n time).
 {exists(N(Pos.to_nat 408419)+slack). rewrite Htime,
   (succ_as_add M n),(succ_as_add M(n+(N(Pos.to_nat 408419)+slack)));ring. }
 destruct Hpath as[tb[tc Hpath]].
 exact(machine230_terminal_path_maximal M b c n tb tc time(machine230_seed M)halted ending
  (conj HR HT)Hq Hpath Hless).
Qed.
Theorem machine230_counter_halting_iff:
 machine230_arithmetical_halts M <->p230_counter_halting M.
Proof. split;[apply machine230_halting_implies_p230_counter|apply p230_counter_halting_implies_machine230]. Qed.
End Equivalence.
Print Assumptions machine230_halting_implies_p230_counter.
Print Assumptions machine230_counter_halting_iff.
