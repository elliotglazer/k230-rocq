(** The concrete arithmetic simulation state. Its finite control evidence
    is the PA-definable public candidate predicate, not an external path
    quantified by an internal induction hypothesis. *)
From PAModel Require Import Model Arithmetic CodeExpressions TM230BinaryStep TM230RunComposition
 TM230MacroProgress TM230RuntimeWords TM230RuntimeBox TM230PhysicalRegisters
 TM230RuntimeSites TM230DispatchCode TM230DispatchEdge TM230DispatchHalt
 TM230DispatchBoot TM230DispatchNormalization TM230P230Control TM230LogicalSites
 TM230BootEncoding Program230PathCode Program230Edges Program230Walk
 Program230LeafFormula Program230Transition.
From K230 Require RM RMEquiv Prog230 Interpreter230Check.
From Stdlib Require Import Lists.List Lia PArith.
Unset Implicit Arguments.
Definition machine230_simulation_state M pc R s:=exists depth gap excess E file,
 machine230_p230_control M depth pc /\
 machine230_runtime_box M(machine230_physical_values M R)E(Runtime230.BPlain Runtime230.FNone)file /\
 machine230_dispatch_code_view M pc depth gap file s /\
 addM M depth gap=addM M excess(code_numeral M Sites230.D0).
Theorem machine230_simulation_initial M:
 exists b c s,machine230_path M b c(code_numeral M(Pos.to_nat 408419))(machine230_seed M)s /\
 machine230_simulation_state M(code_numeral M 1)(machine230_initial_register M)s.
Proof.
 destruct(machine230_uniform_dispatch_boot M)as[b[c[s[word[HP[HB[HC HE]]]]]]].
 exists b,c,s;split;[exact HP|].
 exists(zeroM M),(code_numeral M 181),(code_numeral M 117),(code_numeral M 167),word.
 split;[apply machine230_p230_control_initial|]. split;[exact HB|]. split;[exact HC|exact HE].
Qed.
Theorem machine230_simulation_step M pc R T pc' s:
 machine230_simulation_state M pc R s ->
 program230_step M K230.Prog230.p230 pc R T pc' ->
 exists t,machine230_progresses M s t /\machine230_simulation_state M pc' T t.
Proof.
 intros[depth[gap[excess[E[file[HC[HB[HS Hpos]]]]]]]][e[Q[rest[HW HE]]]].
 destruct(machine230_p230_control_decode M depth pc HC)as[P[HD[HPC[HL Hclean]]]].
 pose proof(program230_walk_leaf_member M K230.Prog230.p230 pc e Q rest K230.Prog230.p230_wf HW)as Hleaf.
 destruct(machine230_p230_leaf_checked Q e Hleaf)as[Hcheck HQ].
 assert(HWP:program230_walk M K230.Prog230.p230(program230_path_value M P)e Q rest)by(now rewrite <-HPC).
 destruct(program230_walk_source_exact M K230.Prog230.p230 P e Q rest K230.Prog230.p230_wf HWP)
  as[Hsource[HQread Hrest]].
 pose proof(machine230_clean_false_suffix K230.Prog230.p230 P e(length Q)Hclean Hsource)as Hfalse.
 destruct(machine230_dispatch_code_program_edge M P Q(length Q)e R T pc pc' E depth gap excess file s
  HQ Hcheck HE HQread Hfalse HD HPC Hpos HB HS)
  as[z[output[t[Hpc[Hbound[HBox[Hcode Hpath]]]]]]].
 exists t;split;[exact Hpath|].
 exists(code_numeral M(length(machine230_edge_path Q e z))),
  (addM M(addM M excess(code_numeral M(machine230_edge_extra Q e z)))
    (code_numeral M(Sites230.D0-length(machine230_edge_path Q e z)))),
  (addM M excess(code_numeral M(machine230_edge_extra Q e z))),
  (machine230_edge_spares M e E),output.
 split;[exact(machine230_p230_control_step M Q e R T pc' z Hleaf HE Hpc)|].
 split;[exact HBox|]. split;[exact Hcode|].
 apply machine230_dispatch_header_position;unfold Sites230.D0;lia.
Qed.
Theorem machine230_simulation_halt M pc R s:
 machine230_simulation_state M pc R s ->
 program230_halt M K230.Prog230.p230 pc ->
 exists t,machine230_state t=code_numeral M 230 /\machine230_progresses M s t.
Proof.
 intros[depth[gap[excess[E[file[HC[HB[HS Hpos]]]]]]]][Q[rest HW]].
 destruct(machine230_p230_control_decode M depth pc HC)as[P[HD[HPC[HL Hclean]]]].
 pose proof(program230_walk_leaf_member M K230.Prog230.p230 pc K230.RM.EHalt Q rest K230.Prog230.p230_wf HW)as Hleaf.
 destruct(machine230_p230_leaf_checked Q K230.RM.EHalt Hleaf)as[Hcheck HQ].
 assert(HWP:program230_walk M K230.Prog230.p230(program230_path_value M P)K230.RM.EHalt Q rest)by(now rewrite <-HPC).
 destruct(program230_walk_source_exact M K230.Prog230.p230 P K230.RM.EHalt Q rest K230.Prog230.p230_wf HWP)
  as[Hsource[HQread Hrest]].
 pose proof(machine230_clean_false_suffix K230.Prog230.p230 P K230.RM.EHalt(length Q)Hclean Hsource)as Hfalse.
 assert(Hhalt:Sites230.run_halt Q=true).
 {unfold K230.Interpreter230Check.check_edge in Hcheck.
  destruct(Nat.leb(length Q)40);[exact Hcheck|discriminate]. }
 exact(machine230_dispatch_code_halt M P Q(length Q)R pc E depth gap excess file s
  HQ Hhalt HQread Hfalse HD HPC Hpos HB HS).
Qed.
Print Assumptions machine230_simulation_initial.
Print Assumptions machine230_simulation_step.
Print Assumptions machine230_simulation_halt.
