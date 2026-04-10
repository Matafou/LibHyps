Require Import Ltac2.Ltac2.
Require Sorting.Mergesort Structures.OrdersEx.
From Ltac2 Require Import Option Constr Printf.
Import Constr.Unsafe.
Local Set Default Proof Mode "Classic".
(* Require Import LibHyps.LibHypsDebug. *)

(* Utilities *)
Local Ltac2 invalid_arg (msg:string) := Control.throw (Invalid_argument (Some (Message.of_string msg))).

Local Ltac2 mk_evar ename typ :=
  let tac := ltac1:(ename typ|- evar (ename:typ)) in
  tac (Ltac1.of_ident ename) (Ltac1.of_constr typ).
  

Local Ltac2 Type premise := [ Int(int) | Ident(ident) ].

Local Ltac2 pr_premise () a :=
  match a with
  | Int(i) => fprintf "Int(%i)" i
  | Ident(id) => fprintf "Ident(%I)" id
  end.

Local Ltac2 minus_one (x:premise):premise :=
  match x with
  | Int n => Int (Int.sub n 1)
  | _ => x
  end.

Local Ltac2 map_minus_one (li:premise list) : premise list := List.map minus_one li.
Ltac2 Type when_cited := [ Evarize | Quantify].
Ltac2 mutable on_cited_vars := Quantify.
Ltac2 mutable dont_quantif_unused := true.

Local Ltac2 andb := Bool.and.
Local Ltac2 negb := Bool.neg.
Local Ltac2 orb := Bool.or.

Local Ltac2 Type whatToDo := [ ForceQuantif (binder) | ForceEvar(ident) | OptQuantif (binder) | OptEvar(ident) ].
(*
Local Ltac2 pr_whattodo () a :=
  match a with
    ForceQuantif bnd => fprintf "ForceQuantif(%a)" pr_binder bnd
   | OptQuantif bnd => fprintf "OptQuantif(%a)" pr_binder bnd
   | ForceEvar id => fprintf "ForceEvar(%I)" id
   | OptEvar id => fprintf "OptEvar(%I)" id
  end.
*)

(* build_premise_type (forall x,y, h1 -> h2 -> forall n,n, h3 -> h4)
   [2;3] return the "forall ..., (h2 -> h3)" where ... are the
   variables appearing in (h2 -> h3). *)
Local Ltac2 rec build_premise_type (t:constr) (li:int list) (lid:ident list) : constr :=
  match Unsafe.kind t with
  | Prod bnd t' =>
      let h_premis:ident option := Constr.Binder.name bnd in
      let typ_premis:constr := Constr.Binder.type bnd in
      let is_dep := Bool.neg (noccurn 1 t') in
      if is_dep (* dep product; forall x:T, U. *)
      then
        let (whattodo,lid'):(whatToDo*ident list) :=
          match lid, on_cited_vars with
          | [], Evarize => (OptQuantif(bnd),lid)
          | [], Quantify => (OptEvar(Option.get h_premis),lid)
          | id :: lid'' , Quantify =>
              if Ident.equal id (Option.get h_premis)
              then (ForceQuantif(bnd), lid'')
              else (OptEvar(Option.get h_premis) , lid)
          | id :: lid'' , Evarize =>
              if Ident.equal id (Option.get h_premis)
              then (ForceEvar(Option.get h_premis) , lid'')
              else (OptQuantif(bnd), lid)
          end 
        in
        let res := build_premise_type t' li lid' in
        match whattodo with
        | ForceQuantif bnd => make (Prod bnd res) 
        | ForceEvar id =>
            let ename:ident := Fresh.in_goal id in
            mk_evar ename typ_premis;
            let ev:constr := make (Var ename) in
            let ressubst := substnl [ev] 0 res in (* this also performs a pop *)
            (if (noccurn 1 res) (* andb (default_ignore_unused)  the evar will disappear if we ignore it *)
            then printf "Warning: an evar is created (?%I) but there is no reference to it in goals" ename
            else ());
            ressubst
        | OptQuantif bnd =>
            if andb (noccurn 1 res) dont_quantif_unused then liftn -1 1 res
            else make (Prod bnd res) 
        | OptEvar id =>
            if (noccurn 1 res) (* andb (default_ignore_unused)  the evar will disappear if we ignore it *)
            then liftn -1 1 res
            else
              let ename:ident := Fresh.in_goal id in
              mk_evar ename typ_premis;
              let ev:constr := make (Var ename) in
              let ressubst := substnl [ev] 0 res in (* this also performs a pop *)
              ressubst
        end
      else (* non dep premise: T -> U *)
        match li with
        | [] => invalid_arg "Empty occurence list, please report."
        | n :: li' =>
            if Int.le n 1 (* either the final premise, or we want to quantify it *)
            then
              if List.is_empty li'
              then
                if List.is_empty lid
                then typ_premis (* We found the final premise *)
                else invalid_arg "the list of variables is too long (or not in the right order?)"
              else (* We found a dependent premise we want to keep, but not the final one *)
                let popli' := List.map (fun x => Int.sub x 1) li' in
                let res := build_premise_type t' popli' lid in
                make (Prod bnd res) (* we keep the premise *)
            else
              (* We found a dependent premise we want to ignore *)
              let popli := List.map (fun x => Int.sub x 1) li in
              let res := build_premise_type t' popli lid in
              if noccurn 1 res (* if premise does NOT occur in result *)
              then
                let r := liftn -1 1 res in (* forget premis, pop rels accordingly. *)
                r
              else (* this dependent premise is actually needed for typing the result *)
                invalid_arg "Some other premise occurs in the built type."
        end
  | _ => invalid_arg "Not enough products"
  end.
(*
Goal True.
  ltac2:(let t := build_premise_type
                    constr:(forall n p m:nat, n<=m -> n<m -> n=p -> False)
                             [1] [ident:(n) ] in
         printf "res = %t" t).
  Undo.
  ltac2:(let t := build_premise_type
                    constr:(forall n p m:nat, n<=m -> n<m -> n=p -> False)
                             [1;2] [ident:(n) ] in
         printf "res = %t" t).
  Undo.
  ltac2:(let t := build_premise_type
                    constr:(forall n p m:nat, n<=m -> n<m -> n=p -> False)
                             [1;2] [ident:(n); ident:(m) ] in
         printf "res = %t" t).
  Undo.
  ltac2:(let t := build_premise_type
                    constr:(forall n p m:nat, n<=m -> n<m -> n=p -> False)
                    [Ident ident:(n) ; Int 1; Int 3] in
         printf "res = %t" t).

Abort.
*)

(* Local Ltac2 rec assert_premise (t:constr) (li:int list) : unit := *)
  (* let typ := build_premise_type t li in *)
  (* Std.assert (Std.AssertType None typ None). *)
(* Pure Ltac2 tactics *)
Module Ltac2.
  Ltac2 all_hyps_ident() := List.map (fun (x,_,_) => x) (Control.hyps ()).

  Ltac2 iter_hyps (tac:ident -> unit) (lh:ident list) :=
    List.iter tac lh.

  Ltac2 map_all_hyps (tac:'a -> unit) :=
    let all_hyps := all_hyps_ident() in
    iter_hyps tac all_hyps.

  Ltac2 map_all_hyps_rev (tac: 'a -> unit) :=
    let all_hyps := List.rev (all_hyps_ident()) in
    iter_hyps tac all_hyps.

  Ltac2 then_eachnh_gen (tac1:'a -> unit) (tac2:ident -> unit) (rev:bool) :=
    let hyps_before := all_hyps_ident() in
    let _ := tac1() in
    Control.enter
      (fun () => 
         let hyps_after := all_hyps_ident() in
         let new_hyps: ident list := List.filter_out (fun id => List.mem Ident.equal id hyps_before) hyps_after in
         iter_hyps tac2 (if rev then List.rev new_hyps else new_hyps)).

  Ltac2 then_eachnh (tac1:'a -> unit) (tac2:ident -> unit) :=
    then_eachnh_gen tac1 tac2 false.

  Ltac2 then_eachnh_rev (tac1:'a -> unit) (tac2:ident -> unit) :=
    then_eachnh_gen tac1 tac2 true.

End Ltac2.

Local Ltac2 rec assert_premise_type (t:constr) (li:int list) (lid:ident list) (name:ident option) : unit :=
  (* We call the tactic then subst any let ins (created along with evars). *)
  Ltac2.then_eachnh_rev
    (fun () => 
       let typ := build_premise_type t li lid in
       let intro_ptn :=
         Option.map (fun x => (Std.IntroNaming (Std.IntroIdentifier x))) name  in
       Std.assert (Std.AssertType (intro_ptn) typ None))
    (fun (h:ident) =>
       match Control.hyp_value h with
       | None => ()
       | Some _ => 
           Std.subst [h]
       end).
(*
Goal forall x y:nat, True.
  intros x y. 
  (ltac2:(assert_premise_type constr:(forall n p m:nat, n<=m -> n<m -> n=p -> False) [ 1;2;3] [] None)).
  Undo.

  (ltac2:(assert_premise_type constr:(forall n p m:nat, n<=m -> n<m -> n=p -> False) [ 1;2;3] [ident:(n)] None)).
  Undo.

  (ltac2:(assert_premise_type constr:(forall n p m:nat, n<=m -> n<m -> n=p -> False)
                                       [ 1;2;3]
                                       [ident:(n); ident:(m)]
                                       None)).
  Undo.
  (ltac2:(assert_premise_type constr:(forall n p m:nat, n<=m -> n<m -> n=p -> False)
                                       [ 1; 2; 3]
                                       [ident:(n);ident:(p)]
                                       None)).
  Undo.
  (ltac2:(assert_premise_type constr:(forall n p m:nat, n<=m -> n<m -> n=p -> False)
                                       [ 1; 2; 3]
                                       [ident:(n);ident:(p);ident:(m)]
                                       None)).
  Undo.
  (* wrong order in variables: n remains in the list after depleting ints *)
  Fail (ltac2:(assert_premise_type constr:(forall n p m:nat, n<=m -> n<m -> n=p -> False)
                                            [ 1; 2; 3]
                                            [ident:(p); ident:(n)]
                                            None)).
Abort.

*)
Local Ltac2 interp_ltac1_int_or_id_list (li:Ltac1.t list) : premise list :=
  List.map
    (fun x =>
       match Ltac1.to_int x with
         None => match (Ltac1.to_ident x) with
                 | None => invalid_arg "not an integer nor a ident"
                 | Some id => Ident id
                 end 
       | Some i => Int i
       end)
    li.


Local Ltac2 interp_ltac1_id_list (lid:Ltac1.t list) : ident list :=
  List.map (fun x => Option.get (Ltac1.to_ident x)) lid.

Local Ltac2 interp_ltac1_int_list (li:Ltac1.t list) : int list :=
  List.map (fun x => Option.get (Ltac1.to_int x)) li.


Local Ltac2 rec assert_premise_from_ltac1 (h:Ltac1.t) (li:Ltac1.t)  (lid:Ltac1.t) (name:Ltac1.t) : unit :=
  let h' := Option.get (Ltac1.to_constr h) in
  (* if li is not a list, then it means no li has been given, thus []. *)
  let li' := interp_ltac1_int_list (default [] (Ltac1.to_list li)) in
  let lid' := interp_ltac1_id_list (default [] (Ltac1.to_list lid)) in
  (* If name is not recognized it means that no name was given, thus None. *)
  let name' := Ltac1.to_ident name in
  let th' := type h' in
  
  assert_premise_type th' li' lid' name'.

Local Ltac dummy_term := constr:(Prop).


Global Tactic Notation "assert" "premise" ne_integer_list_sep(li,"->") "of" constr(h) "with" ne_ident_list_sep(lid,",") "as" ident(newH) :=
  let tac := ltac2:(h li lid newH |- assert_premise_from_ltac1 h li lid newH) in
  tac h li lid newH.


Global Tactic Notation "assert" "premise" ne_integer_list_sep(li,"->") "of" constr(h) "with" ne_ident_list_sep(lid,",") :=
  let tac := ltac2:(h li lid newH |- assert_premise_from_ltac1 h li lid newH) in
  let newH := dummy_term in
  tac h li lid newH.

Global Tactic Notation "assert" "premise" ne_integer_list_sep(li,"->") "of" constr(h) "as" ident(newH) :=
  let tac := ltac2:(h li lid newH |- assert_premise_from_ltac1 h li lid newH) in
  let lid := dummy_term in
  tac h li lid newH.

Global Tactic Notation "assert" "premise" ne_integer_list_sep(li,"->") "of" constr(h) :=
  let tac := ltac2:(h li lid newH |- assert_premise_from_ltac1 h li lid newH) in
  let lid := dummy_term in
  let newH := dummy_term in
  tac h li lid newH.

