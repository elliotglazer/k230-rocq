(** Concrete symbolic premises needed by the actual primitive-history fold. *)
From PAModel Require Import CodeExpressions Program230Configurations Program230AXSymbolic
 Program230AXNativeSymbolic Program230AXSymbolicTrace.
From Stdlib Require Import Lists.List Arith.Arith Bool.Bool Lia.
Import ListNotations.
Unset Implicit Arguments.
Definition p230_ax_row_shape(row:p230_ax_native_row):Prop:=
 let '(op,before,_):=row in match op with
 |ANLoad r=>program230_register before 1=CEconst 0 /\(r=3 \/r=4 \/r=5)
 |ANCons=>exists x tail,program230_register before 2=CEpair x tail
 |ANUnpair=>program230_register before 8=CEvar 8 \/program230_register before 8=CEvar 9
 |_=>True end.
Definition p230_ax_row_shapeb(row:p230_ax_native_row):bool:=
 let '(op,before,_):=row in match op with
 |ANLoad r=>match program230_register before 1 with CEconst 0=>Nat.eqb r 3||Nat.eqb r 4||Nat.eqb r 5|_=>false end
 |ANCons=>match program230_register before 2 with CEpair _ _=>true|_=>false end
 |ANUnpair=>match program230_register before 8 with CEvar 8|CEvar 9=>true|_=>false end
 |_=>true end.
Lemma p230_ax_row_shapeb_sound row:p230_ax_row_shapeb row=true->p230_ax_row_shape row.
Proof.
 destruct row as[[op before]after];unfold p230_ax_row_shapeb,p230_ax_row_shape.
 destruct op as[|r| | | |a b];try(intros _;exact I).
 -destruct(program230_register before 1)as[n|n|x y|x y|x y];try discriminate.
  destruct n;try discriminate;intro H;split;[reflexivity|].
  apply Bool.orb_true_iff in H;destruct H as[H|H];[apply Bool.orb_true_iff in H;destruct H as[H|H]|];
  apply Nat.eqb_eq in H;auto.
 -destruct(program230_register before 2)as[n|n|x y|x y|x y];try discriminate.
  intros _;exists x,y;reflexivity.
 -destruct(program230_register before 8)as[n|n|x y|x y|x y];try discriminate.
  destruct n as[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]];try discriminate;intros _;auto.
Qed.
Theorem p230_ax_native_rows_shapes:Forall p230_ax_row_shape p230_ax_native_rows.
Proof.
 assert(H:forallb p230_ax_row_shapeb p230_ax_native_rows=true)by(vm_compute;reflexivity).
 apply Forall_forall;intros row HI;apply p230_ax_row_shapeb_sound.
 exact(proj1(forallb_forall _ _)H row HI).
Qed.
Definition p230_ax_unpair_row_metadata(row:p230_ax_native_row):Prop:=
 let '(op,before,after):=row in match op with ANUnpair=>
 (program230_register before 8=CEvar 8 /\program230_register after 6=CEvar 11 /\program230_register after 7=CEvar 9) \/
 (program230_register before 8=CEvar 9 /\program230_register after 6=CEvar 4 /\program230_register after 7=CEvar 10)
 |_=>True end.
Lemma p230_ax_unpair_metadata_of_step row:
 p230_ax_native_row_correct row->p230_ax_row_shape row->p230_ax_unpair_row_metadata row.
Proof.
 destruct row as[[op before]after];unfold p230_ax_native_row_correct,p230_ax_row_shape,p230_ax_unpair_row_metadata.
 destruct op as[|r| | | |a b];try(intros _ _;exact I).
 intros Hstep[H8|H9];cbn[p230_ax_native_step]in Hstep.
 -rewrite H8 in Hstep;injection Hstep as <-;left;repeat split;try exact H8;reflexivity.
 -rewrite H9 in Hstep;injection Hstep as <-;right;repeat split;try exact H9;reflexivity.
Qed.
Theorem p230_ax_native_rows_unpair_metadata:Forall p230_ax_unpair_row_metadata p230_ax_native_rows.
Proof.
 apply Forall_forall;intros row HI;apply p230_ax_unpair_metadata_of_step.
 -exact(proj1(Forall_forall _ _)p230_ax_native_rows_correct row HI).
 -exact(proj1(Forall_forall _ _)p230_ax_native_rows_shapes row HI).
Qed.
Print Assumptions p230_ax_native_rows_shapes.
Print Assumptions p230_ax_native_rows_unpair_metadata.
