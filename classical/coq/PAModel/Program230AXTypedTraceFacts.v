(** Per-row agreement between exact public labels and symbolic intermediate states. *)
From PAModel Require Import Program230AXPrimitiveSchedule Program230AXNativeSymbolic
 Program230AXSymbolicTrace Program230AXTypedNormalization Program230AXRowShapes.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Lemma p230_ax_maps_equal_Forall2{A B C:Type}(f:A->C)(g:B->C)xs ys:
 map f xs=map g ys->Forall2(fun x y=>f x=g y)xs ys.
Proof.
 induction xs as[|x xs IH]in ys|-*;destruct ys as[|y ys];cbn;try discriminate;intro H.
 -constructor.
 -injection H as Hhead Htail;constructor;[exact Hhead|exact(IH ys Htail)].
Qed.
Lemma p230_ax_Forall2_combine{A B:Type}(R:A->B->Prop)xs ys:
 Forall2 R xs ys->Forall(fun item=>R(fst item)(snd item))(combine xs ys).
Proof. intro H;induction H;cbn;constructor;assumption. Qed.
Theorem p230_ax_typed_rows_labels:
 Forall(fun item=>p230_ax_native_of(fst(snd(fst item)))=
  Some(let '(op,_,_):=snd item in op))p230_ax_typed_rows.
Proof.
 unfold p230_ax_typed_rows.
 apply(p230_ax_Forall2_combine(fun site row=>p230_ax_native_of(fst(snd site))=Some(let '(op,_,_):=row in op))
 p230_ax_primitive_schedule p230_ax_native_rows).
 apply(p230_ax_maps_equal_Forall2(fun site=>p230_ax_native_of(fst(snd site)))(fun row=>Some(let '(op,_,_):=row in op))).
 pose proof p230_ax_exact_typed_projection as H.
 unfold p230_ax_typed_operations in H;rewrite map_map in H.
 rewrite <-p230_ax_native_rows_operations,map_map in H;exact H.
Qed.
Theorem p230_ax_typed_row_facts item:
 In item p230_ax_typed_rows->
 p230_ax_native_of(fst(snd(fst item)))=Some(let '(op,_,_):=snd item in op) /\
 p230_ax_native_row_correct(snd item) /\
 p230_ax_native_clean_row(snd item) /\p230_ax_row_shape(snd item) /\p230_ax_unpair_row_metadata(snd item).
Proof.
 intro Hin.
 assert(Hrow:In(snd item)p230_ax_native_rows).
 {rewrite <-p230_ax_typed_rows_states;apply in_map;exact Hin. }
 split;[exact(proj1(Forall_forall _ _)p230_ax_typed_rows_labels item Hin)|].
 split;[exact(proj1(Forall_forall _ _)p230_ax_native_rows_correct _ Hrow)|].
 split;[exact(proj1(Forall_forall _ _)p230_ax_native_rows_clean _ Hrow)|].
 split;[exact(proj1(Forall_forall _ _)p230_ax_native_rows_shapes _ Hrow)|].
 exact(proj1(Forall_forall _ _)p230_ax_native_rows_unpair_metadata _ Hrow).
Qed.
Print Assumptions p230_ax_typed_rows_labels.
Print Assumptions p230_ax_typed_row_facts.
