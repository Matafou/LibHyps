(**************************************************************************
* A user-customizable auto-naming scheme for hypothesis in Coq            *
* Author: Pierre Courtieu                                                 *
* Distributed under the terms of the LGPL-v3 license                      *
***************************************************************************)
Require Import Arith ZArith List LibHyps.TacNewHyps.
Import ListNotations.
(** This file is a set of tactical (mainly "!! t" where t is a tactic)
    and tactics (!intros, !destruct etc), that automatically rename
    new hypothesis after applying a tactic. The names chosen for
    hypothesis is programmable using Ltac. See examples in comment
    below.

    Comments welcome. *)

(* Comment this and the Z-dependent lines below if you don't want
   ZArith to be loaded *)
Require Import ZArith.

(** ** The custom renaming tactic
  This tactic should be redefined along a coq development, it should
  return a fresh name build from an hypothesis h and its type th. It
  should fail if no name is found, so that the fallback scheme is
  called.

  Typical use, in increasing order of complexity, approximatively
  equivalent to the decreasing order of interest.

<<
Ltac my_rename_hyp h th :=
  match th with
    | (ind1 _ _ _ _) => fresh "ind1"
    | (ind2 _ _) => fresh "ind2"
    | f1 _ _ = true => fresh "f_eq_true"
    | f1 _ _ = false => fresh "f_eq_false"
    | f1 _ _ = _ => fresh "f_eq"
    | ind3 ?h ?x => fresh "ind3_" h
    | ind3 _ ?x => fresh "ind3" (* if fresh h failed above *)

    (* Sometime we want to look for the name of another hypothesis to
       name h. For example here we want to rename hypothesis h into
       "type_of_foo" if there is some H of type [type_of foo = Some
       h]. *)
    | type => (* See if we find something of which h is the type: *)
              match reverse goal with
              | H: type_of ?x = Some h => fresh "type_of_" x
              end

    | _ => previously_defined_renaming_tac1 th (* cumulative with previously defined renaming tactics *)
    | _ => previously_defined_renaming_tac2 th
  end.

(* Overwrite the definition of rename_hyp using the ::= operator. :*)

Ltac rename_hyp ::= my_rename_hyp.>> *)
(* Dummy constant *)
(* Definition h_:=Type. *)
Definition heq_:=Type.
Definition noname:=Type.
Definition DUMMY := fun x:Prop => x.


(* for hypothesis on numerical constants *)
Ltac numerical_names prefx t :=
  match t with
  | Z0 => fresh prefx "_0"
  | 0%Z => fresh prefx "_0"
  | (Zpos xH)%Z => fresh prefx "_1"
  | 2%Z => fresh prefx "_2"
  | 3%Z => fresh prefx "_3"
  | 4%Z => fresh prefx "_4"
  | 5%Z => fresh prefx "_5"
  | 6%Z => fresh prefx "_6"
  | 7%Z => fresh prefx "_7"
  | 8%Z => fresh prefx "_8"
  | 9%Z => fresh prefx "_9"
  | 10%Z => fresh prefx "_10"
  | O%nat => fresh prefx "_0"
  | 1%nat => fresh prefx "_1"
  | 2%nat => fresh prefx "_2"
  | 3%nat => fresh prefx "_3"
  | 4%nat => fresh prefx "_4"
  | 5%nat => fresh prefx "_5"
  | 6%nat => fresh prefx "_6"
  | 7%nat => fresh prefx "_7"
  | 8%nat => fresh prefx "_8"
  | 9%nat => fresh prefx "_9"
  | 10%nat => fresh prefx "_10"
  end.

Ltac box_name id :=
  let id_ := fresh "_" id in constr:(forall id_:Prop, DUMMY id_).

Ltac build_name acc l :=
  let l := eval lazy beta delta [List.app] iota in l in
  match l with
  | nil => acc
  | (forall id1:Prop, DUMMY id1)::?l' =>
    let newacc := fresh acc id1 in
    let res := build_name newacc l' in
    res
  end.



Ltac impl_prefix := constr:(forall _impl, DUMMY _impl).
Ltac forall_prefix := constr:(forall _forall, DUMMY _forall).
Ltac exists_prefix := constr:(forall _exist, DUMMY _exist).
Ltac default_prefix :=constr:(forall h, DUMMY h).
Ltac eq_prefix :=constr:(forall eq, DUMMY eq).
Ltac neq_prefix :=constr:(forall neq, DUMMY neq).

Ltac detect_prefix th :=
  match th with
  | ?A -> ?B => impl_prefix
  | forall z:?A , ?B => forall_prefix
  | exists z:?A , ?B => exists_prefix
  | _ => default_prefix
  end.

(* This is the customizable naming tactic, by default it fails, giving
   control to default naming tactics. *)
Ltac rename_hyp th := match th with
                        | _ => fail
                        end.

Ltac freshable t :=
  let x := fresh t "_dummy_sufx" in
  idtac.

Ltac rename_append_piece t l :=
    let res1 := constr:(@List.app Prop t l) in
    eval lazy delta [List.app] beta iota in res1.

(* Default naming of an application: we name the function if possible
   or fail, then we add all parameters that can be named either
   recursively or simply.
   TODO: remove implicits? Don't know how to do that. *)
Ltac rename_app stop acc th :=
  match th with
  | (?f ?x) =>
    let x'' := 
    match stop with
    | true => box_name x
    | false => fallback_rename_hyp stop x
    end in
    let x''' := rename_append_piece x'' acc in
    rename_app stop x''' f
  | (?f ?x) => rename_app stop acc f
  | ?f =>
    let f' := freshable f in
    let f'' := box_name f in
    constr:(f''::acc)
  end

(* go under binder and rebuild a term with a good name inside,
   catchable by a match context. *)
with build_dummy_quantified stop th :=
  lazymatch th with
  | forall z:?A , ?B =>
    constr:(
      fun z:A =>
        ltac:(
          let th' := constr:((fun z => B) z) in
          let th' := eval lazy beta in th' in
          let res := build_dummy_quantified stop th' in
          exact res))
 | ex ?f =>
    match f with
    | (fun z:?A => ?B) =>
    constr:(
      fun z:A =>
        ltac:(
          let th' := constr:((fun z => B) z) in
          let th' := eval lazy beta in th' in
          let res := build_dummy_quantified stop th' in
          exact res))
    end
  | _ =>
    fallback_rename_hyp stop th
  end

(** ** Calls the (user-defined) rename_hyp + and fallbacks to some
    default namings if needed. [h] is the hypothesis (ident) to
    rename, [th] is its type. *)

with fallback_rename_hyp_quantif stop th :=
    let prefx :=
        match th with
        | forall _ , _ => forall_prefix
        | ex (fun _ => _) => exists_prefix
        | _ => false
        end in
    lazymatch prefx with
    | false => fail
    | _ =>
      let sufx_buried := build_dummy_quantified stop th in
      let sufx :=
          match sufx_buried with
          | context [ (@cons Prop ?x ?y)] => constr:(x::y)
          end
      in
      constr:(prefx::sufx)
    end

with fallback_rename_hyp_specials stop th :=
      match th with
      (* First see if user has something that applies *)
      | _ => rename_hyp th
(*      | ~ ?t = ?u =>
        let hl := fallback_rename_hyp stop t in
        let hr := fallback_rename_hyp stop u in
        let res' := rename_append_piece hl hr in
        constr:((forall _neq:Prop, DUMMY _neq) :: res')*)
(*      | ?t = ?u => (* don't use the first arg of eq *)
        let hl := fallback_rename_hyp stop t in
        let hr := fallback_rename_hyp stop u in
        let res' := rename_append_piece hl hr in
            constr:((forall _eq:Prop, DUMMY _eq) :: res')*)
      end


(* stop is true if name is already long (i.e. some application has
   been traversed). *)
with fallback_rename_hyp stop th :=
      match th with
      | _ => fallback_rename_hyp_specials stop th
         (* customizable naming tactic has priority. *)
      (* | _ => rename_default h th (* some default ones may then happen *) *)
      | _ => match stop with (* then we go through quantifiers only if at top *)
             | true => fail
             | false => fallback_rename_hyp_quantif stop th
             end
      | _ =>
        let newstop :=
            let typth := type of th in
            match typth with
            | Prop => stop
            | _ => true
            end in
        rename_app newstop (@nil Prop) th (* default TODO: unify with above default? *)
      end.


Notation "'`' id '`'" := (forall id, DUMMY id) (at level 1,id ident,only parsing): autonaming_scope.
Notation "'#' X " := ltac:(let c := fallback_rename_hyp true X in exact c)
                            (at level 1,X constr, only parsing): autonaming_scope.
Notation "'$' X " := ltac:(let c := fallback_rename_hyp false X in exact c)
                            (at level 1,X constr, only parsing): autonaming_scope.

Ltac name c := (constr:(c)).

Local Open Scope autonaming_scope.
Local Open Scope list.

Ltac rename_hyp_default th :=
  let res := 
      match th with
      | (@eq _ ?x ?y) => name (`_eq` :: #x ++ #y)
      | ?x <> ?y => name (`_neq` :: #true ++ #false)
      | @cons _ ?x ?l => name (`_cons` :: #x ++ #l)
      end in
  res.

Ltac rename_hyp ::= rename_hyp_default.

Ltac fallback_rename_hyp_name th :=
  let l := fallback_rename_hyp false th in
  let prfx := default_prefix in
  match prfx with
  | context [forall z:Prop, DUMMY z] =>
    build_name z l
  end.

Ltac autorename H :=
  match type of H with
  | ?th =>
    match type of th with
    | Prop => 
      let dummy_name := fresh "dummy" in
      rename H into dummy_name; (* this renaming makes the renaming more or less
                                   idempotent, it is backtracked if the
                                   rename_hyp below fails. *)
      let newname := fallback_rename_hyp_name th in
      rename dummy_name into newname
    end
  | _ => idtac (* not in Prop or "no renaming pattern for " H *)
  end.
  
Ltac rename_new_hyps tac := tac_new_hyps tac autorename.

(* Need a way to rename or revert but revert needs to be done in the
   other direction (so better do ";; autorename ;!; revertHyp"), and
   may fail if something depends on the reverted hyp. So we should
   revert everything depending on the unrenamed hyp. *)
Ltac revert_if_norename H :=
  let t := type of H in
  match type of t with
  | Prop => match goal with
            | _ =>  let x := fallback_rename_hyp_name t in idtac
            (* since we are only in prop it is almost never the case
               that something depends on H but if this happens we revert
               everything that does. *)
            | _ => try revert dependent H
            end
  | _ => idtac
  end.

(*
Lemma dummy: forall x y,
    (forall nat : Type, (nat -> nat -> Prop) -> list nat -> Prop) ->
    0 <= 1 ->
    (0%Z <= 1%Z)%Z ->
    x <= y ->
    x = y ->
    0 = 1 ->
    (0 = 1)%Z ->
    ~x = y ->
    true = Nat.eqb 3 4  ->
    Nat.eqb 3 4 = true  ->
    true = Nat.leb 3 4  ->
    1 = 0 ->
    ~x = y ->
    ~1 < 0 ->
     (forall w w':nat , w = w' -> ~true=false)=(forall w w':nat , w = w' -> ~true=false) ->
     (forall w w':nat , w = w' -> ~true=false) ->  
     (forall w w':nat , w = w' -> true=false /\ True) -> 
     (forall w w':nat , w = w' -> true=false) -> 
     (forall w w':nat , w = w' -> False /\ True) -> 
     (exists w:nat , w = w -> ~(true=(andb false true)) /\ False) ->
     (exists w:nat , w = w -> True /\ False) ->
     (forall w w':nat , w = w' -> true=false) -> 
     (forall w w':nat , w = w' -> Nat.eqb 3 4=Nat.eqb 4 3) -> 
    List.length (cons 3 nil) = (fun x => 0)1 ->
    List.length (cons 3 nil) = x ->
    plus 0 y = y ->
    (true=false) ->
    (true<>false) ->
    (False -> (true=false)) ->
    forall (a b: nat) (env : list nat),
      ~ List.In a nil ->
      cons a (cons 3 env) = cons 2 env -> 
    forall z t:nat,
      IDProp ->
      a = b ->
      (0 < 1 -> 0 < 0 -> true = false -> ~(true=false)) ->
      (~(true=false)) ->
      (forall w w',w < w' -> ~(true=false)) ->
      (0 < 1 -> ~(1<0)) ->
      (0 < 1 -> 1<0) -> 0 < z -> True.
  (* auto naming at intro: *)
Proof.
  intros.
  Debug On.
  let th := type of H12 in
  let newname := fallback_rename_hyp_name th in
  idtac newname.


  onAllHyps autorename.
  
  Debug Off.

(*
  let th := type of H2 in
  let res :=
      match th with
      | (@eq _ ?x ?y) => let a := constr:(+{_eq}) in a
      end in
  let h_ := fresh "h" in
  (* let nme := build_name h_ res in *)
  idtac res*)


  let th := type of H2 in
  let newname := fallback_rename_hyp_name th in
  idtac newname.
(*  let th := type of H2 in
  match th with
  | (@eq _ ?a ?b) => let res := constr:( {* x *}) in idtac res
  end.*)



  onAllHyps autorename.
  let th10 := type of H2 in
  let newname := fallback_rename_hyp_name th10 in
  idtac newname.
  let x := fallback_rename_hyp false th10 in
  idtac x.
*)
(* ***************************************************** *)



