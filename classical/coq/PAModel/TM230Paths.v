(** Actual finite paths for the literal table, in every PA model. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension BetaPacking CodeExpressions
 NumericalProofs TM230BinaryStep TM230RunArithmetic TM230StandardRun TM230StandardPacking TM230RunComposition.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lia setoid_ring.Ring.
Unset Implicit Arguments.
Definition machine230_run_from_formula b c n q l h r :=
 machine230_state_at_formula b c zero q l h r ∧ machine230_transitions_formula b c n.
Lemma machine230_run_from_formula_correct M rho b c n q l h r:
 holds M rho(machine230_run_from_formula b c n q l h r) <->
 machine230_run_from M(evalM M rho b)(evalM M rho c)(evalM M rho n)
 (machine230_mk_config(carrier M)(evalM M rho q)(evalM M rho l)(evalM M rho h)(evalM M rho r)).
Proof.
 unfold machine230_run_from_formula,machine230_run_from.
 rewrite holds_and,machine230_state_at_formula_correct,machine230_transitions_formula_correct. reflexivity.
Qed.
Definition machine230_path_formula b c n q l h r q' l' h' r' :=
 machine230_run_from_formula b c n q l h r ∧ machine230_state_at_formula b c n q' l' h' r'.
Lemma machine230_path_formula_correct M rho b c n q l h r q' l' h' r':
 holds M rho(machine230_path_formula b c n q l h r q' l' h' r') <->
 machine230_path M(evalM M rho b)(evalM M rho c)(evalM M rho n)
 (machine230_mk_config(carrier M)(evalM M rho q)(evalM M rho l)(evalM M rho h)(evalM M rho r))
 (machine230_mk_config(carrier M)(evalM M rho q')(evalM M rho l')(evalM M rho h')(evalM M rho r')).
Proof.
 unfold machine230_path_formula,machine230_path.
 rewrite holds_and,machine230_run_from_formula_correct,machine230_state_at_formula_correct. reflexivity.
Qed.
Definition machine230_reaches M s t:=exists b c n,machine230_path M b c n s t.
Definition machine230_reaches_formula q l h r q' l' h' r' :=
 ∃∃∃machine230_path_formula $2 $1 $0
 (machine230_lift 3 q)(machine230_lift 3 l)(machine230_lift 3 h)(machine230_lift 3 r)
 (machine230_lift 3 q')(machine230_lift 3 l')(machine230_lift 3 h')(machine230_lift 3 r').
Lemma machine230_lift3_eval M rho a b c t:
 evalM M(c.:b.:a.:rho)(machine230_lift 3 t)=evalM M rho t.
Proof. unfold evalM;cbn[machine230_lift]. now rewrite !eval_up. Qed.
Local Opaque holds machine230_path_formula.
Lemma machine230_reaches_formula_correct M rho q l h r q' l' h' r':
 holds M rho(machine230_reaches_formula q l h r q' l' h' r') <->
 machine230_reaches M
 (machine230_mk_config(carrier M)(evalM M rho q)(evalM M rho l)(evalM M rho h)(evalM M rho r))
 (machine230_mk_config(carrier M)(evalM M rho q')(evalM M rho l')(evalM M rho h')(evalM M rho r')).
Proof.
 unfold machine230_reaches_formula,machine230_reaches. repeat setoid_rewrite holds_ex.
 setoid_rewrite machine230_path_formula_correct. setoid_rewrite machine230_lift3_eval. reflexivity.
Qed.
Section Paths.
Variable M:Model.
Local Notation D := (carrier M).
Local Notation Z := (zeroM M).
Local Notation S := (succM M).
Local Infix "+" := (addM M).
Local Infix "*" := (mulM M).
Local Notation four := (code_numeral M 4).
Add Ring machine230_path_ring : (model_semiring M).
Lemma machine230_state_singleton(s:machine230_config D):
 exists b c,machine230_state_at M b c Z s.
Proof.
 destruct s as[q l h r].
 destruct(beta_extension M q q(S Z)l)as[b1[c1[H1 HL]]].
 destruct(beta_extension M b1 c1(S(S Z))h)as[b2[c2[H2 HH]]].
 destruct(beta_extension M b2 c2(S(S(S Z)))r)as[b3[c3[H3 HR]]].
 assert(H01:coding_lt M Z(S Z))by apply coding_lt_succ.
 assert(H12:coding_lt M(S Z)(S(S Z)))by apply coding_lt_succ.
 assert(H23:coding_lt M(S(S Z))(S(S(S Z))))by apply coding_lt_succ.
 assert(H02:coding_lt M Z(S(S Z)))by(eapply coding_lt_trans;eassumption).
 assert(H13:coding_lt M(S Z)(S(S(S Z))))by(eapply coding_lt_trans;eassumption).
 assert(H03:coding_lt M Z(S(S(S Z))))by(eapply coding_lt_trans;eassumption).
 exists b3,c3. unfold machine230_state_at,machine230_state_index;cbn[machine230_state machine230_left machine230_head machine230_right].
 replace(four*Z+code_numeral M 0)with Z by (cbn[code_numeral];ring).
 replace(four*Z+code_numeral M 1)with(S Z)by (cbn[code_numeral];ring).
 replace(four*Z+code_numeral M 2)with(S(S Z))by (cbn[code_numeral];ring).
 replace(four*Z+code_numeral M 3)with(S(S(S Z)))by (cbn[code_numeral];ring).
 refine(conj _ (conj _ (conj _ HR))).
 -apply H3;[exact H03|]. apply H2;[exact H02|]. apply H1;[exact H01|apply beta_singleton].
 -apply H3;[exact H13|]. apply H2;[exact H12|exact HL].
 -apply H3;[exact H23|exact HH].
Qed.
Theorem machine230_path_zero s:
 exists b c,machine230_path M b c Z s s.
Proof.
 destruct(machine230_state_singleton s)as[b[c H]]. exists b,c. split;[split|];try exact H.
 intros i x y Hi. exfalso. exact(coding_not_lt_zero M i Hi).
Qed.
Theorem machine230_path_one s t:
 machine230_step M s t ->exists b c,machine230_path M b c(S Z)s t.
Proof.
 intro Hstep. destruct(machine230_state_singleton s)as[b[c HS]].
 destruct(machine230_state_singleton t)as[d[e HT]].
 destruct(beta_concatenate M b c four d e four)as[f[g[HL HR]]].
 assert(Hleft:forall i v,coding_lt M i(four*(S Z))->beta M b c i v->beta M f g(four*Z+i)v).
 { intros i v Hi HV. replace(four*Z+i)with i by ring.
   apply HL;[|exact HV]. replace(four*(S Z))with four in Hi by(rewrite succ_as_add;ring). exact Hi. }
 assert(Hright:forall i v,coding_lt M i(four*(S Z))->beta M d e i v->beta M f g(four*(S Z)+i)v).
 { intros i v Hi HV. replace(four*(S Z))with four in * by(rewrite succ_as_add;ring). exact(HR i v Hi HV). }
 assert(HS':machine230_state_at M f g Z s).
 { pose proof(machine230_state_at_transport M b c f g Z(S Z)Hleft Z s(coding_lt_succ M Z)HS)as P.
   now rewrite coding_add_zero in P. }
 assert(HT':machine230_state_at M f g(S Z)t).
 { pose proof(machine230_state_at_transport M d e f g(S Z)(S Z)Hright Z t(coding_lt_succ M Z)HT)as P.
   now rewrite coding_add_zero_r in P. }
 exists f,g. split;[split;[exact HS'|]|exact HT'].
 intros i x y Hi HX HY. apply coding_lt_succ_cases in Hi. destruct Hi as[Hi|E];[exfalso;exact(coding_not_lt_zero M i Hi)|]. subst i.
 assert(x=s)by(eapply machine230_state_at_unique;eassumption).
 assert(y=t)by(eapply machine230_state_at_unique;eassumption). now subst.
Qed.
Theorem machine230_path_join b c n d e k s u t:
 machine230_path M b c n s u ->machine230_path M d e k u t ->
 exists f g,machine230_path M f g(n+k)s t.
Proof.
 intros[H1 HU][H2 HT].
 destruct(machine230_run_from_join M b c n d e k s u H1 HU H2)as[f[g[Hrun[HL HR]]]].
 exists f,g. split;[exact Hrun|]. apply(HR k t(coding_lt_succ M k)). exact HT.
Qed.
Theorem machine230_reaches_refl s:machine230_reaches M s s.
Proof. destruct(machine230_path_zero s)as[b[c H]]. exists b,c,Z. exact H. Qed.
Theorem machine230_reaches_step s t:machine230_step M s t ->machine230_reaches M s t.
Proof. intro H. destruct(machine230_path_one s t H)as[b[c HP]]. exists b,c,(S Z). exact HP. Qed.
Theorem machine230_reaches_trans s u t:
 machine230_reaches M s u ->machine230_reaches M u t ->machine230_reaches M s t.
Proof.
 intros[b[c[n H]]][d[e[k H']]]. destruct(machine230_path_join b c n d e k s u t H H')as[f[g HP]].
 exists f,g,(n+k). exact HP.
Qed.
End Paths.
Print Assumptions machine230_path_one.
Print Assumptions machine230_path_join.
Print Assumptions machine230_reaches_formula_correct.
