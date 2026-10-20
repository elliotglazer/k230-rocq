(** Finite command prefixes of the exact numerical enumerator.  Parameters
    are arbitrary model elements; only the four command constructors are finite. *)
From PAModel Require Import Model Arithmetic FiniteCoding Pairing CodeExpressions
  NumericalProofs SearchStep.
Unset Implicit Arguments.

Definition command2_graph M tag x tail p : Prop :=
  exists head rest, p=succM M head /\ pair_graph M tag rest head /\ pair_graph M x tail rest.
Definition command4_graph M c x y u tail p : Prop :=
  exists tail2 tail3, pair_graph M y tail2 tail3 /\ pair_graph M u tail tail2 /\
    command2_graph M (addM M c (code_numeral M 3)) x tail3 p.

Lemma command2_total M tag x tail : exists p, command2_graph M tag x tail p.
Proof.
  destruct(pair_total M x tail)as[r Hr]. destruct(pair_total M tag r)as[h Hh].
  exists(succM M h),h,r. auto.
Qed.
Lemma command4_total M c x y u tail : exists p,command4_graph M c x y u tail p.
Proof.
  destruct(pair_total M u tail)as[r2 H2]. destruct(pair_total M y r2)as[r3 H3].
  destruct(command2_total M (addM M c(code_numeral M 3))x r3)as[p Hp].
  exists p,r2,r3. auto.
Qed.

Definition command_state M p np t w d h :search_state(carrier M):=
  mkSearchState(carrier M)p np t w d h.

Lemma command2_prefix M tag x tail p np t w d h :
  command2_graph M tag x tail p ->exists head rest,
  search_prefix_relation M(command_state M p np t w d h)
    head np tag rest x tail(addM M d x).
Proof.
  intros[head[rest[Hp[Hh Hr]]]]. exists head,rest.
  split.
  - right. split;[|reflexivity]. apply search_add_graph_correct.
    rewrite Hp. apply succ_as_add.
  - split;[now apply search_pair_graph_correct|].
    split;[now apply search_pair_graph_correct|].
    apply search_add_graph_correct. reflexivity.
Qed.

Lemma command_drop_step M tail p np t w d h w' :
  command2_graph M(code_numeral M 1)(zeroM M)tail p ->pair_graph M t w w' ->
  enumerator_step M(command_state M p np t w d h)
    (command_state M tail np h w' d h).
Proof.
  intros Hcmd Hw. destruct(command2_prefix M _ _ tail p np t w d h Hcmd)as[head[rest Hp]].
  exists head,np,(code_numeral M 1),rest,(zeroM M),tail,(addM M d(zeroM M)).
  split;[exact Hp|]. right;left. unfold command_state; cbn -[addM zeroM code_numeral search_stack search_bundle search_implication search_pair_graph].
  rewrite coding_add_zero_r. split;[reflexivity|]. split;[repeat split|].
  split;[reflexivity|]. split;[now apply search_pair_graph_correct|reflexivity].
Qed.

Lemma command_nip_step M tail p np t w d h h' w' :
  command2_graph M(code_numeral M 2)(zeroM M)tail p ->
  h<>code_numeral M 1 -> pair_graph M h' w' w ->
  enumerator_step M(command_state M p np t w d h)
    (command_state M tail np t w' d h').
Proof.
  intros Hcmd Hh Hw. destruct(command2_prefix M _ _ tail p np t w d h Hcmd)as[head[rest Hp]].
  exists head,np,(code_numeral M 2),rest,(zeroM M),tail,(addM M d(zeroM M)).
  split;[exact Hp|]. right;right;left. unfold command_state; cbn -[addM zeroM code_numeral search_stack search_bundle search_implication search_pair_graph].
  rewrite coding_add_zero_r. split;[reflexivity|]. split;[exact Hh|].
  split;[repeat split|]. split;[reflexivity|]. now apply search_pair_graph_correct.
Qed.

Lemma command_nip_halt M tail p np t w d :
  command2_graph M(code_numeral M 2)(zeroM M)tail p ->
  enumerator_halt M(command_state M p np t w d(code_numeral M 1)).
Proof.
  intro Hcmd. destruct(command2_prefix M _ _ tail p np t w d (code_numeral M 1) Hcmd)as[head[rest Hp]].
  exists head,np,(code_numeral M 2),rest,(zeroM M),tail,(addM M d(zeroM M)). auto.
Qed.

Lemma command_mp_success M x tail p np t w d h w' :
  command2_graph M(zeroM M)x tail p ->
  search_implication M t(addM M d x)h ->pair_graph M(zeroM M)w w' ->
  enumerator_step M(command_state M p np t w d h)
    (command_state M tail np(addM M d x)w'(addM M d x)(zeroM M)).
Proof.
  intros Hcmd Hi Hw. destruct(command2_prefix M _ _ tail p np t w d h Hcmd)as[head[rest Hp]].
  exists head,np,(zeroM M),rest,x,tail,(addM M d x).
  split;[exact Hp|]. left. unfold command_state; cbn -[addM zeroM code_numeral search_stack search_bundle search_implication search_pair_graph].
  split;[reflexivity|]. split;[repeat split|]. split;[reflexivity|].
  left. split;[exact Hi|]. split;[reflexivity|]. now apply search_pair_graph_correct.
Qed.

Lemma command_mp_failure M x tail p np t w d h :
  command2_graph M(zeroM M)x tail p ->
  ~search_implication M t(addM M d x)h ->
  enumerator_step M(command_state M p np t w d h)
    (command_state M tail np(zeroM M)w(addM M d x)(zeroM M)).
Proof.
  intros Hcmd Hi. destruct(command2_prefix M _ _ tail p np t w d h Hcmd)as[head[rest Hp]].
  exists head,np,(zeroM M),rest,x,tail,(addM M d x).
  split;[exact Hp|]. left. unfold command_state; cbn -[addM zeroM code_numeral search_stack search_bundle search_implication search_pair_graph].
  split;[reflexivity|]. split;[repeat split|]. split;[reflexivity|]. right. auto.
Qed.

Lemma command_ax_step M c x y u tail p np t w d h v w' :
  command4_graph M c x y u tail p ->
  search_stack M(addM M d x)h(addM M h y)c u t w w' ->
  (((c=addM M d x \/c=addM M h y)/\v=zeroM M)\/
    (c<>addM M d x /\c<>addM M h y /\search_bundle M(addM M d x)(addM M h y)c v)) ->
  enumerator_step M(command_state M p np t w d h)
    (command_state M tail np v w'(zeroM M)(zeroM M)).
Proof.
  intros[r2[r3[H3[H2 Hcmd]]]] Hw Hv.
  destruct(command2_prefix M _ _ r3 p np t w d h Hcmd)as[head[rest Hp]].
  exists head,np,(addM M c(code_numeral M 3)),rest,x,r3,(addM M d x).
  split;[exact Hp|]. right;right;right.
  exists c,y,r2,u,tail,(addM M h y).
  split;[apply search_add_graph_correct;reflexivity|].
  split;[now apply search_pair_graph_correct|].
  split;[now apply search_pair_graph_correct|].
  split;[apply search_add_graph_correct;reflexivity|].
  unfold command_state; cbn -[addM zeroM code_numeral search_stack search_bundle search_implication search_pair_graph]. repeat split;try reflexivity.
  - exact Hw.
  - exact Hv.
Qed.

Print Assumptions command_drop_step.
Print Assumptions command_ax_step.



