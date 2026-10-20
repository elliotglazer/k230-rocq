(** Literal cells, pointer reorientation and finite non-loop transitions of the
    arithmetic symbolic executor. *)
From PAModel Require Import Model Arithmetic CodeExpressions TM230LiteralActions TM230BinaryStep
 TM230BitArithmetic TM230LeftView TM230Paths TM230RunPrefixes TM230SymbolicSegments.
From K230 Require TM230.
From BusyCoq Require TM.
From Stdlib Require Import Lists.List setoid_ring.Ring.
Import ListNotations.
Unset Implicit Arguments.
Definition machine230_cell b:=machine230_make_segment b 0 1.
Section Cells.
Variable M:Model.
Local Notation D:=(carrier M).
Local Notation Z:=(zeroM M).
Local Notation S:=(succM M).
Local Notation one:=(S Z).
Local Notation two:=(S one).
Local Infix "+":=(addM M).
Local Infix "*":=(mulM M).
Add Ring machine230_cell_ring:(model_semiring M).
Lemma machine230_cell_value gap b tail word:
 machine230_segment_value M gap(machine230_cell b)tail word <->word=machine230_bitM M b+two*tail.
Proof.
 unfold machine230_segment_value,machine230_segment_length,machine230_cell;cbn[machine230_segment_bit machine230_segment_factor machine230_segment_constant code_numeral].
 replace(Z*gap+one)with one by ring.
 rewrite(machine230_run_prefix_successor M b Z tail word).
 setoid_rewrite(machine230_run_prefix_zero M b tail).
 split;[intros[inner[-> H]];exact H|intro H;exists tail;auto].
Qed.
Lemma machine230_segment_peel gap b a c tail word:
 machine230_segment_value M gap(machine230_make_segment b a(Datatypes.S c))tail word <->
 exists inner,machine230_segment_value M gap(machine230_make_segment b a c)tail inner /\
 machine230_segment_value M gap(machine230_cell b)inner word.
Proof.
 unfold machine230_segment_value,machine230_segment_length;cbn[machine230_segment_bit machine230_segment_factor machine230_segment_constant].
 change(machine230_run_prefix M b(code_numeral M a*gap+S(code_numeral M c))tail word <->
 exists inner,machine230_run_prefix M b(code_numeral M a*gap+code_numeral M c)tail inner /\
 machine230_segment_value M gap(machine230_cell b)inner word).
 replace(code_numeral M a*gap+S(code_numeral M c))with(S(code_numeral M a*gap+code_numeral M c))by(rewrite(succ_as_add M(code_numeral M c)),(succ_as_add M(code_numeral M a*gap+code_numeral M c));ring).
 rewrite machine230_run_prefix_successor. setoid_rewrite machine230_cell_value. reflexivity.
Qed.
Theorem machine230_reorient_cell gap q b ls rs ltail rtail s:
 machine230_symbolic_view M gap q true(machine230_cell b::ls)rs ltail rtail s ->
 machine230_symbolic_view M gap q false ls(machine230_cell b::rs)ltail rtail s.
Proof.
 intros[l[r[[rest[Hl Hcell]][Hr Hs]]]]. apply machine230_cell_value in Hcell.
 destruct s as[sq sl sh sr]. unfold machine230_left_view in Hs;cbn[machine230_state machine230_left machine230_head machine230_right]in Hs.
 destruct Hs as[Hsq[Hsr[Hsh Hw]]].
 destruct(machine230_pop_unique M sh sl(machine230_bitM M b)rest Hsh(machine230_bit_is_bit M b)
 ltac:(eapply eq_trans;[exact(eq_sym Hw)|rewrite Hcell;ring]))as[Eh El].
 subst sq sr sh sl. exists rest,(machine230_bitM M b+two*r). split;[exact Hl|]. split.
 -exists r. split;[exact Hr|]. apply machine230_cell_value;reflexivity.
 -unfold machine230_right_view;cbn[machine230_state machine230_left machine230_head machine230_right].
  split;[reflexivity|]. split;[reflexivity|]. split;[apply machine230_bit_is_bit|ring].
Qed.
Lemma machine230_right_to_left_step q b w q' l r s t:
 Public230.tmn q b=Some(w,TM.L,q')->
 machine230_right_view M q l(machine230_bitM M b+two*r)s ->
 machine230_left_view M q'(machine230_bitM M w+two*r)l t ->machine230_step M s t.
Proof.
 intros Htable Hs Ht. destruct s as[sq sl sh sr].
 unfold machine230_right_view in Hs;cbn[machine230_state machine230_left machine230_head machine230_right]in Hs.
 destruct Hs as[Hsq[Hsl[Hsh Hw]]].
 destruct(machine230_pop_unique M sh sr(machine230_bitM M b)r Hsh(machine230_bit_is_bit M b)
 ltac:(eapply eq_trans;[exact(eq_sym Hw)|ring]))as[Eh Er].
 subst sq sl sh sr. eapply(machine230_left_view_step M q b w q' r l).
 -exact Htable.
 -unfold machine230_left_view;cbn[machine230_state machine230_left machine230_head machine230_right].
  split;[reflexivity|]. split;[reflexivity|]. split;[apply machine230_bit_is_bit|ring].
 -replace(two*r+machine230_bitM M w)with(machine230_bitM M w+two*r)by ring. exact Ht.
Qed.
Theorem machine230_symbolic_cell_right gap q b w q' ls rs ltail rtail s:
 Public230.tmn q b=Some(w,TM.R,q')->
 machine230_symbolic_view M gap q false ls(machine230_cell b::rs)ltail rtail s ->
 exists t,machine230_symbolic_view M gap q' false(machine230_cell w::ls)rs ltail rtail t /\
 machine230_step M s t.
Proof.
 intros Htable[l[r[Hl[[rest[Hr Hcell]]Hs]]]]. apply machine230_cell_value in Hcell. subst r.
 destruct(machine230_right_view_total M q'(two*l+machine230_bitM M w)rest)as[t Ht].
 exists t. split.
 -exists(two*l+machine230_bitM M w),rest. split.
  +exists l. split;[exact Hl|]. apply machine230_cell_value;ring.
  +split;assumption.
 -exact(machine230_right_view_step M q b w q' l rest s t Htable Hs Ht).
Qed.
Theorem machine230_symbolic_cell_left gap q b w q' ls rs ltail rtail s:
 Public230.tmn q b=Some(w,TM.L,q')->
 machine230_symbolic_view M gap q false ls(machine230_cell b::rs)ltail rtail s ->
 exists t,machine230_symbolic_view M gap q' true ls(machine230_cell w::rs)ltail rtail t /\
 machine230_step M s t.
Proof.
 intros Htable[l[r[Hl[[rest[Hr Hcell]]Hs]]]]. apply machine230_cell_value in Hcell. subst r.
 destruct(machine230_left_view_total M q'(machine230_bitM M w+two*rest)l)as[t Ht].
 exists t. split.
 -exists l,(machine230_bitM M w+two*rest). split;[exact Hl|]. split.
  +exists rest. split;[exact Hr|]. apply machine230_cell_value;reflexivity.
  +exact Ht.
 -exact(machine230_right_to_left_step q b w q' l rest s t Htable Hs Ht).
Qed.
End Cells.
Print Assumptions machine230_reorient_cell.
Print Assumptions machine230_symbolic_cell_right.
Print Assumptions machine230_symbolic_cell_left.
