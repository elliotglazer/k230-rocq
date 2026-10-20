(** Ten-field internally coded counterprogram configurations. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaPacking CodeExpressions NumericalProofs.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lists.List Arith.Arith Lia setoid_ring.Ring.
Import ListNotations.
Unset Implicit Arguments.
Record program230_configuration(D:Type):Type:=mkProgram230Configuration{
 program230_pc:D;
 program230_r0:D;
 program230_r1:D;
 program230_r2:D;
 program230_r3:D;
 program230_r4:D;
 program230_r5:D;
 program230_r6:D;
 program230_r7:D;
 program230_r8:D
}.
Arguments program230_pc {D} _ .
Arguments program230_r0 {D} _ .
Arguments program230_r1 {D} _ .
Arguments program230_r2 {D} _ .
Arguments program230_r3 {D} _ .
Arguments program230_r4 {D} _ .
Arguments program230_r5 {D} _ .
Arguments program230_r6 {D} _ .
Arguments program230_r7 {D} _ .
Arguments program230_r8 {D} _ .
Definition program230_field{D}(s:program230_configuration D)(j:nat):D:=
 match j with
 |0=>program230_pc s
 |1=>program230_r0 s
 |2=>program230_r1 s
 |3=>program230_r2 s
 |4=>program230_r3 s
 |5=>program230_r4 s
 |6=>program230_r5 s
 |7=>program230_r6 s
 |8=>program230_r7 s
 |9=>program230_r8 s
 |_=>program230_r8 s end.
Definition program230_register{D}(s:program230_configuration D)(j:nat):D:=program230_field s(S j).
Definition program230_config_of{D}(f:nat->D):program230_configuration D:=mkProgram230Configuration D (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) (f 8) (f 9).
Lemma program230_config_of_fields{D}(f:nat->D)j:(j<10)%nat->program230_field(program230_config_of f)j=f j.
Proof. intro H;do 10(destruct j;[reflexivity|]);lia. Qed.
Definition program230_eval_config M rho(s:program230_configuration term):program230_configuration(carrier M):=program230_config_of(fun j=>evalM M rho(program230_field s j)).
Lemma program230_eval_field M rho s j:(j<10)%nat->program230_field(program230_eval_config M rho s)j=evalM M rho(program230_field s j).
Proof. intro H. exact(@program230_config_of_fields(carrier M)(fun k=>evalM M rho(program230_field s k))j H). Qed.
Definition program230_field_index M i j:=addM M(mulM M(code_numeral M 10)i)(code_numeral M j).
Definition program230_field_index_term(i:term)j:term:=(num 10 ⊗ i) ⊕ num j.
Definition program230_state_at M b c i(s:program230_configuration(carrier M)):=forall j,(j<10)%nat->beta M b c(program230_field_index M i j)(program230_field s j).
Fixpoint program230_fields_formula n(F:nat->form):form:=match n with 0=>zero==zero|S n=>F n ∧program230_fields_formula n F end.
Lemma program230_fields_formula_correct M rho n F:holds M rho(program230_fields_formula n F)<->forall j,(j<n)%nat->holds M rho(F j).
Proof. induction n as[|n IH];cbn[program230_fields_formula];[split;[intros _ j H;lia|reflexivity]|]. rewrite holds_and,IH. split;[intros[Hn H]j Hj;destruct(Nat.eq_dec j n);[subst;exact Hn|apply H;lia]|intro H;split;[apply H;lia|intros j Hj;apply H;lia]]. Qed.
Definition program230_state_at_formula(b c i:term)(s:program230_configuration term):form:=program230_fields_formula 10(fun j=>beta_formula b c(program230_field_index_term i j)(program230_field s j)).
Lemma program230_field_index_correct M rho i j:evalM M rho(program230_field_index_term i j)=program230_field_index M(evalM M rho i)j.
Proof. unfold program230_field_index_term,program230_field_index. change(addM M(mulM M(evalM M rho(num 10))(evalM M rho i))(evalM M rho(num j))=addM M(mulM M(code_numeral M 10)(evalM M rho i))(code_numeral M j)). now rewrite !code_eval_num. Qed.
Lemma program230_state_at_formula_correct M rho b c i s:holds M rho(program230_state_at_formula b c i s)<->program230_state_at M(evalM M rho b)(evalM M rho c)(evalM M rho i)(program230_eval_config M rho s).
Proof. unfold program230_state_at_formula,program230_state_at;rewrite program230_fields_formula_correct. split;intros H j Hj;specialize(H j Hj).
 -rewrite(program230_eval_field M rho s j Hj). apply beta_formula_correct in H. now rewrite program230_field_index_correct in H.
 -apply beta_formula_correct. rewrite program230_field_index_correct. now rewrite(program230_eval_field M rho s j Hj)in H.
Qed.
Lemma program230_state_at_total M b c i:exists s,program230_state_at M b c i s.
Proof.
 destruct(beta_total M b c(program230_field_index M i 0))as[p H0].
 destruct(beta_total M b c(program230_field_index M i 1))as[a0 H1].
 destruct(beta_total M b c(program230_field_index M i 2))as[a1 H2].
 destruct(beta_total M b c(program230_field_index M i 3))as[a2 H3].
 destruct(beta_total M b c(program230_field_index M i 4))as[a3 H4].
 destruct(beta_total M b c(program230_field_index M i 5))as[a4 H5].
 destruct(beta_total M b c(program230_field_index M i 6))as[a5 H6].
 destruct(beta_total M b c(program230_field_index M i 7))as[a6 H7].
 destruct(beta_total M b c(program230_field_index M i 8))as[a7 H8].
 destruct(beta_total M b c(program230_field_index M i 9))as[a8 H9].
 exists(mkProgram230Configuration(carrier M) p a0 a1 a2 a3 a4 a5 a6 a7 a8). intros j Hj;do 10(destruct j;[assumption|]);lia.
Qed.
Lemma program230_state_at_functional M b c i s t:program230_state_at M b c i s->program230_state_at M b c i t->s=t.
Proof. intros HS HT. destruct s,t. f_equal.
 -exact(beta_unique M b c(program230_field_index M i 0)_ _(HS 0 ltac:(lia))(HT 0 ltac:(lia))).
 -exact(beta_unique M b c(program230_field_index M i 1)_ _(HS 1 ltac:(lia))(HT 1 ltac:(lia))).
 -exact(beta_unique M b c(program230_field_index M i 2)_ _(HS 2 ltac:(lia))(HT 2 ltac:(lia))).
 -exact(beta_unique M b c(program230_field_index M i 3)_ _(HS 3 ltac:(lia))(HT 3 ltac:(lia))).
 -exact(beta_unique M b c(program230_field_index M i 4)_ _(HS 4 ltac:(lia))(HT 4 ltac:(lia))).
 -exact(beta_unique M b c(program230_field_index M i 5)_ _(HS 5 ltac:(lia))(HT 5 ltac:(lia))).
 -exact(beta_unique M b c(program230_field_index M i 6)_ _(HS 6 ltac:(lia))(HT 6 ltac:(lia))).
 -exact(beta_unique M b c(program230_field_index M i 7)_ _(HS 7 ltac:(lia))(HT 7 ltac:(lia))).
 -exact(beta_unique M b c(program230_field_index M i 8)_ _(HS 8 ltac:(lia))(HT 8 ltac:(lia))).
 -exact(beta_unique M b c(program230_field_index M i 9)_ _(HS 9 ltac:(lia))(HT 9 ltac:(lia))).
Qed.
Print Assumptions program230_state_at_formula_correct.
Print Assumptions program230_state_at_total.
Print Assumptions program230_state_at_functional.
