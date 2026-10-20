(** The exact finite blank startup initializes the arithmetic invariant. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
 TM230BinaryStep TM230RunArithmetic TM230RunComposition TM230Paths TM230BitArithmetic PowerTwoSyntax PowerTwoRecurrence
 TM230RuntimeBox TM230PhysicalRegisters TM230RuntimeTokens TM230DispatchWords
 TM230DispatchCode TM230DispatchCalibration TM230BootEncoding.
From Stdlib Require Import Lists.List PArith setoid_ring.Ring.
Import ListNotations.
Unset Implicit Arguments.
Theorem machine230_dispatch_code_empty M gap file s:
 machine230_dispatch_view M [] gap 0 file s ->
 machine230_dispatch_code_view M(code_numeral M 1)(zeroM M)gap file s.
Proof.
 intro H. pose proof(proj1(machine230_dispatch_code_calibration M [] gap 0 file s)H)as HC.
 now rewrite coding_add_zero_r in HC.
Qed.
Theorem machine230_uniform_dispatch_boot M:
 exists b c s word,
 machine230_path M b c(code_numeral M(Pos.to_nat 408419))(machine230_seed M)s /\
 machine230_runtime_box M(machine230_physical_values M(machine230_initial_register M))
  (code_numeral M 167)(Runtime230.BPlain Runtime230.FNone)word /\
 machine230_dispatch_code_view M(code_numeral M 1)(zeroM M)(code_numeral M 181)word s /\
 addM M(zeroM M)(code_numeral M 181)=addM M(code_numeral M 117)(code_numeral M 64).
Proof.
 destruct(machine230_uniform_initial_register_view M)as[b[c[s[p[spare[word[HP[HV[Hpower[Hsp Hfile]]]]]]]]]].
 exists b,c,s,word;split;[exact HP|]. split.
 -apply(machine230_register_box_intro M(machine230_initial_register M)(code_numeral M 167)spare word).
  +change(coding_lt M(zeroM M)(succM M(code_numeral M 166)));apply coding_zero_lt_succ.
  +exact Hsp.
  +exact Hfile.
 -split.
  +apply machine230_dispatch_code_empty. exists p;split;[now rewrite coding_add_zero_r|exact HV].
  +rewrite coding_add_zero,<-machine230_runtime_numeral_add;reflexivity.
Qed.
Print Assumptions machine230_dispatch_code_empty.
Print Assumptions machine230_uniform_dispatch_boot.
