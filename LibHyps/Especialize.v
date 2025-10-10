From Stdlib Require Import String.
(* Require ident_of_string. *)
Require Import Ltac2.Ltac2.
From Ltac2 Require Import Option Constr Printf.
Import Constr.Unsafe.
(* Declare Scope specialize_scope. *)
(* Delimit Scope specialize_scope with spec. *)
(* Local Open Scope specialize_scope. *)
Require IdentParsing.

From Stdlib Require Import String Ascii.
Open Scope string_scope.
Local Set Default Proof Mode "Classic".

(* The type describing how to specialize the arguments of a hyp. Premises are either
- transformed into a sub goal
- transformed into an evar
- requantified (default). *)
Inductive spec_arg : Type :=
  (* This 4 are meant to be put in a exhaustive list of what to do
  with args in order. The others are actually transformed into these
  ones on the fly *)
  Quantif | QuantifIgnore | SubGoal | Evar: string -> spec_arg
| SubGoalAtName: string -> spec_arg (* make a subgoal with named arg *)                   
| SubGoalAtNum: nat -> spec_arg (* make a subgoal with arg's number *)
| EvarAtName: string -> string -> spec_arg (* make an evar with the named arg. *)
| SubGoalUntilNum: nat -> spec_arg (* make subgoals with all non dep hyp until nth one. *)
| SubGoalAtAll: spec_arg. (* make subgoals with all non dep hyp. *)

Definition spec_args := list spec_arg .

(* List storing heterogenous terms, for storing telescopes. A simple
   product could also be used. *)
(*
Inductive Depl :=
| DNil: Depl
| DCons: forall (A:Type) (x:A), Depl -> Depl.
*)

(* if H head product is dependent, call tac1, else call tac2 *)
Ltac if_is_dep_prod H tac1 tac2 :=
  (* tryif is_dep_prod H then ltac:(tac1) else ltac:(tac2). *)
  let t := type of H in
  match goal with
  | |- _ => match goal with
            | |- _ => assert t;
                      let h := fresh "__h__" in
                      intro h;
                      (tryif clear h then fail else fail 1) (* we fail in both cases to backtrack the assert*)
            | |- _ => tac2
            | |- _ => fail 2 (* don't fall back to tac1 *)
            end
  | |- _ => tac1
  end.

Ltac2 rec length_constr_string (xs : constr) : int :=
  match kind xs with
  | App _ args =>
    match Int.equal (Array.length args) 2 with
    | true => Int.add 1 (length_constr_string (Array.get args 1))
    | _ => if equal xs 'String.EmptyString then 0 else Control.throw No_value
    end
  | Constr.Unsafe.Constructor _ _ => 0
  | _ => Control.throw No_value
  end.

Ltac2 string_of_constr_string (s : constr) : string :=
  let s := eval vm_compute in ($s : String.string) in
  let ret := String.make (length_constr_string s) (Char.of_int 0) in
  let t := constr:(true) in
  let rec fill i s :=
    (match kind s with
    | App _ args =>
      (if Int.equal (Array.length args) 2 then
         (String.set ret i (match kind (Array.get args 0) with App _ b => Char.of_int (
            Int.add (if equal (Array.get b 0) t then 1 else 0) (
            Int.add (if equal (Array.get b 1) t then 2 else 0) (
            Int.add (if equal (Array.get b 2) t then 4 else 0) (
            Int.add (if equal (Array.get b 3) t then 8 else 0) (
            Int.add (if equal (Array.get b 4) t then 16 else 0) (
            Int.add (if equal (Array.get b 5) t then 32 else 0) (
            Int.add (if equal (Array.get b 6) t then 64 else 0) (
                    (if equal (Array.get b 7) t then 128 else 0)))))))))
          | _ => Control.throw No_value end);
        fill (Int.add i 1) (Array.get args 1))
      else ())
    | _ => ()
    end) in
  fill 0 s;
  ret.

Ltac if_eqstr :=
  ltac2:(ident s tac1 tac2 |-
           (if String.equal
                 (Ident.to_string (Option.get (Ltac1.to_ident ident)))
                 (string_of_constr_string (Option.get (Ltac1.to_constr s)))
            then Ltac1.apply tac1 [] 
            else Ltac1.apply tac2 []) Ltac1.run).

Ltac2 ident_of_constr_string (s : constr) := Option.get (Ident.of_string (string_of_constr_string s)).

Ltac ident_of_constr_string_cps := ltac2:(s tac |-
  Ltac1.apply tac [Ltac1.of_ident (ident_of_constr_string (Option.get (Ltac1.to_constr s)))] Ltac1.run).

Ltac evar_as_string s t := ident_of_constr_string_cps s ltac:(fun s => let s' := fresh s in evar(s':t)).


(* ESPECIALIZE INTERNAL DOC *)
(* We show here by hand what the especialize tactic does. We start
with a hypothesis H of type

H: (forall n m:nat, n<m -> n<=m -> forall p:nat, p>0 -> p+1 = m+n)

Suppose we want:

1. let the user prove that the premise (n <= m) can be proved from the
   other premise (n < m) and can thus be removed from H

2. let the user prove the premise (p > 0) for a p yet to be determined
   (evar) and remove both p and (p>0) from H.
*)
Lemma foo: forall x y : nat, (forall n m:nat, n < m -> n <= m -> forall p:nat, p > 0 -> p+1 = m+n) -> False.
Proof.

  intros x y H. 
  (* - We start from a goal evarEV with no typing constraint. *)
  let ev1 := open_constr:(_) in
  assert ev1 as newH.
  (* then we refine this unknown goal by mimick H until we reach the
  premise we want to remove: *)
  intro n. (*or refine (fun (n:nat) => _) *)
  specialize (H n).
  intro m. 
  specialize (H m).

  (* 1 more times, but more automatic *)
  match type of H with
    (forall nme:?t, _) => (intro nme) (*refine (fun nme:t => _)*); specialize (H nme)
  end.
  
  (* We want to prove (n<=m) as a consequence of (n<m) in H. So here
  instead of mimickig H we assert the premise as a new goal. *)
  assert (n<=m) as h.
  all:swap 1 2.
  (* we go on by specializing H with this new goal *)
  specialize (H h).

  (* let us make the premise p an evar and specialize H with it. *)
  evar (p:nat).
  specialize (H p);subst p.
  (* Let us make another goal for (?p > 0) *)
  assert (?p>0) as h'.
  all:swap 1 2.
  (* we go on by specializing H with this new goal *)
  specialize (H h').
  (* Now we have finished, we finish refining the unknown goal with H itself. *)
  exact H.
  (* Now we are left with 2 subgoals and the initial goal where H has
     been specialized. *)
Abort.

(* debug *)
Require Import LibHyps.LibHypsTactics.
Module Prgoal_Notation.
  Ltac pr_goal :=
    match goal with
      |- ?g =>
        let allh := harvest_hyps revert_clearbody_all in
        (* let allh := all_hyps in *)
        idtac "GOAL: " allh " ⊢ " g
    end.
End Prgoal_Notation.


Local Ltac2 tag_info s := (String.concat "" [ "<infomsg>"; s; "</infomsg>" ]).
Local Ltac2 tag_msg m := Message.concat
                     (Message.concat (Message.of_string "<infomsg>") m)
                     (Message.of_string "</infomsg>").
Local Ltac2 str_to_msg s := tag_msg (Message.of_string s).
Local Ltac2 int_to_msg i := tag_msg (Message.of_int i).
Local Ltac2 id_to_msg id := tag_msg (Message.of_ident id).
Local Ltac2 constr_to_msg c := tag_msg (Message.of_constr c).

Local Ltac2 msgs s := Message.print (str_to_msg s).
Local Ltac2 msgi i := Message.print (int_to_msg i).
Local Ltac2 msgc c := Message.print (constr_to_msg c).
Local Ltac2 msgid id := Message.print (id_to_msg id).


Ltac2 pr_binder () (b:binder) :=
  let nme:ident option := Binder.name b in
  let typ:constr := Binder.type b in
  fprintf "(%I:%t)" (Option.get nme) typ.


Ltac2 pr_goal() :=
  let l := Control.hyps() in
  printf "<infomsg> Goal:";
  List.iter (fun (nme,_,typ) => printf "%I : %t" nme typ) l;
  printf "⊢ %t" (Control.goal());
  printf "</infomsg>".


Ltac2 intro_typed (name:ident) (typ:constr) :=
  let tac := ltac1:(name typ |- refine (fun (name:typ) => _)) in
  tac (Ltac1.of_ident name) (Ltac1.of_constr typ).

Ltac2 specialize_id_id (h:ident) (arg:ident) : unit :=
  let newhyp := Control.hyp arg in
  let hc:constr := Control.hyp h in
  let special := Unsafe.make (Unsafe.App hc [|newhyp|]) in
  Std.specialize (special , Std.NoBindings) None.
  
Ltac2 specialize_id_cstr (h:ident) (c:constr) : unit :=
  let hc:constr := Control.hyp h in
  let special := Unsafe.make (Unsafe.App hc [|c|]) in
  Std.specialize (special , Std.NoBindings) None.
  

(*
Goal False.
  let ev1 := open_constr:(_) in
  assert ev1.    
  ltac2:(intro_typed (Option.get (Ident.of_string "toto")) constr:(nat)).
*)

Ltac2 Type directarg := [ Quantif | QuantifIgnore | SubGoal | Evar(ident) ].
Ltac2 Type namearg := [
    SubGoalAtName(ident) (* make a subgoal with named arg *)                   
  | EvarAtName(ident,ident) (* make an evar with the named arg. *)
].
Ltac2 Type numarg := [
  | SubGoalAtNum(int) (* make a subgoal with arg's number *)
  | SubGoalUntilNum(int) (* make subgoals with all non dep hyp until nth one. *)
  | SubGoalAtAll (* make subgoals with all non dep hyp. *)
  ].

(* FIXME *)
Ltac2 is_dep_prod (t:constr): bool :=
  match kind t with
  | Prod _ subt => Bool.neg (is_closed subt)
  | _ => false
  end.

Ltac2 pr_numarg () a :=
  match a with
  | SubGoalAtNum(i) => fprintf "SubGoalAtNum(%i)" i
  | SubGoalUntilNum(i) => fprintf "SubGoalUntilNum(%i)" i
  | SubGoalAtAll => fprintf "SubGoalAtAll"
  end.

Ltac2 backtrack (msg:string) := Control.zero (Tactic_failure (Some (fprintf "Backtrack: %s" msg))).
Ltac2 invalid_arg (msg:string) := Control.throw (Invalid_argument (Some (Message.of_string msg))).

Ltac2 rec refine_hd (h:ident) (ldirectarg:directarg list) (lnameargs:namearg list)
  (lnumargs:numarg list) (n:int) :=
  let hc:constr := Control.hyp h in (* h as a constr *)
  let th:constr := Constr.type hc in (* type of h as a constr *)
  (* pr_goal(); *)
  printf "<infomsg>th = %t</infomsg>" th;
  printf "<infomsg>%a</infomsg>" pr_numarg (List.hd lnumargs);
  (* msgc th; *)
  let newn := if is_dep_prod th then n else (Int.add n 1) in
  match ldirectarg,lnameargs,lnumargs with
  | [],[],[] => exact $hc (* let tc := ltac1:(h |- exact h) in tc (Ltac1.of_constr hc) *)
  | (directarg::ldirectarg'),_,_ =>
      match Unsafe.kind th with
      | Prod bnd _ =>
          msgs "ICI";
          let h_premis := Constr.Binder.name bnd in
          let typ_premis := Constr.Binder.type bnd in
          let intronme:ident :=
            match h_premis with
              None => Option.get (Ident.of_string "h_premis")
            | Some idh => idh
            end in
          match directarg with
          | Quantif =>
              intro_typed intronme typ_premis;
              specialize_id_id h intronme;
              refine_hd h ldirectarg' lnameargs lnumargs newn
          | QuantifIgnore =>
              intro_typed intronme typ_premis;
              specialize_id_id h intronme;
              clear $intronme;
              refine_hd h ldirectarg' lnameargs lnumargs newn
          | Evar ename =>
              let tac := ltac1:(ename typ_premis|- evar (ename:typ_premis)) in
              tac (Ltac1.of_ident ename) (Ltac1.of_constr typ_premis) ;
              specialize_id_id h ename;
              subst $ename;
              refine_hd h ldirectarg' lnameargs lnumargs newn
          | SubGoal =>
              let gl := Fresh.in_goal @h in (* this uses base name "h" *)
              (unshelve (epose (_:$typ_premis) as $gl)) >
                [  | 
                  let special := Control.hyp gl in
                  specialize_id_cstr h special;
                  refine_hd h ldirectarg' lnameargs lnumargs newn ]
          end
      | _ => 
          match lnumargs with
          | [SubGoalAtAll] => exact $hc
          | _ => let _ := printf "th: %t" th in
                 invalid_arg "Not a product (directarg)"
          end
      end
  | _ =>
      msgs "ICI 2";
      Control.plus
        (fun() => refine_hd_name h ldirectarg lnameargs lnumargs n)
        (fun _ => Control.plus
                    (fun () => refine_hd_num h ldirectarg lnameargs lnumargs n)
                    (fun _ => refine_hd h [Quantif] lnameargs lnumargs n))

        (* (refine_hd_num (h:ident) (ldirectarg:directarg list) (lnameargs:namearg list) *)
           (* (lnumargs:numarg list) (n:int)) *)
  end
    with refine_hd_name (h:ident) (ldirectarg:directarg list) (lnameargs:namearg list)
         (lnumargs:numarg list) (n:int) :=
    let hc:constr := Control.hyp h in (* h as a constr *)
    let th:constr := Constr.type hc in (* type of h as a constr *)
    match ldirectarg,lnameargs,lnumargs with
    | [],[],[] => invalid_arg "refine_hd_name: assert false"
    | [],  (namearg :: lnameargs') , _ => 
        match Unsafe.kind th with
        | Prod bnd _ =>
            let h_premis := Constr.Binder.name bnd in
            let typ_premis := Constr.Binder.type bnd in
            let intronme:ident :=
              match h_premis with
                None => Option.get (Ident.of_string "h_premis")
              | Some idh => idh
              end in
            match namearg with
            | SubGoalAtName nme =>
                if map_default (Ident.equal nme) false h_premis
                then refine_hd h [SubGoal] lnameargs' lnumargs n
                else backtrack "refine_hd_name: SubGoalAtName"
            | EvarAtName nme nameevar =>
                if map_default (Ident.equal nme) false h_premis
                then refine_hd h [Evar nameevar] lnameargs' lnumargs n
                else backtrack "refine_hd_name: EvarAtName"
            end
        | _ => invalid_arg "Not a  product (refine_hd_name)"
        end
    | _ => backtrack "refine_hd_name: no namearg"
    end
  with refine_hd_num (h:ident) (ldirectarg:directarg list) (lnameargs:namearg list)
       (lnumargs:numarg list) (n:int) :=
    let hc:constr := Control.hyp h in (* h as a constr *)
    let th:constr := Constr.type hc in (* type of h as a constr *)
    let newn := if is_dep_prod th then n else (Int.add n 1) in
    match ldirectarg,lnameargs,lnumargs with
    | [],[],[] => invalid_arg "refine_hd_num: assert false"
    | [],_,numarg::lnumargs' =>
        match Unsafe.kind th with
        | Prod bnd _ =>
            match numarg with
            | SubGoalAtNum num =>
                if is_dep_prod th
                then backtrack "refine_hd_num: SubGoalAtNum, dep"
                else if Int.le newn num
                     then if Int.equal newn num
                          then refine_hd h [SubGoal] lnameargs lnumargs' n
                          else backtrack "refine_hd_num: SubGoalAtNum,nodep"
                     else invalid_arg "Did you not order the evar numbers?"
            | SubGoalUntilNum num =>
                if is_dep_prod th
                then backtrack "refine_hd_num: SubGoalUntilNum, dep"
                else
                  let _ := msgc th in
                  let _ := msgs "not dep" in
                  if Int.equal newn num
                  then refine_hd h [SubGoal] lnameargs lnumargs' n
                  else refine_hd h [SubGoal] lnameargs lnumargs n

            | SubGoalAtAll =>
                let _ := msgs "SubGoalAtAll:" in
                let _ := msgc th in
                if is_dep_prod th
                then backtrack "refine_hd_num: SubGoalAtAll, dep"
                else refine_hd h [SubGoal] lnameargs lnumargs n
            end
        | _ => backtrack "Not a product (refine_hd_num)."
        end
     | _ => backtrack "refine_hd_num: no numarg"
    end
.

(* tests *)
Definition eq_one (i:nat) := i = 1.
Definition hidden_product := forall i j :nat, i+1=j -> i+1=j -> i+1=j.


Lemma foo: forall x y : nat,
    (forall (n m p :nat) (hhh:n < m) (iii:n <= m),
        p > 0
        -> p > 2
        -> p > 1
        -> hidden_product) -> False.
Proof.
  intros x y H. 

  let ev1 := open_constr:(_) in
  assert ev1.


  (ltac2:(refine_hd
            (Option.get (Ident.of_string "H"))
            []
            [EvarAtName @m @m]
            [SubGoalAtAll]
            0)).

  (ltac2:(refine_hd
            (Option.get (Ident.of_string "H"))
            []
            [EvarAtName @m @m]
            [SubGoalUntilNum 3]
            0)).




  (ltac2:(refine_hd 
            (Option.get (Ident.of_string "H"))
            [Evar @ev]
            [EvarAtName @p @p ;SubGoalAtName @iii]
            [SubGoalAtNum 3]
            0)).




  let ev1 := open_constr:(_) in
  assert ev1;
  [ (ltac2:(refine_hd (Option.get (Ident.of_string "H"))
            [Quantif; Quantif; Evar @p] [] [] 0)) |].


    match goal with | |- False => idtac end; match type of X with forall (n:_) (m:_), n < m -> _ => idtac end .
  Undo 1.
  especialize H with n, p;
    [ match goal with | |- False => idtac end; match type of H with forall (m:_), _ < m -> _ => idtac end ].
  Undo 1.
  especialize H with p as h;
    [ match goal with | |- False => idtac end; match type of h with forall (n:_) (m:_), n < m -> _ => idtac end ].
  Undo 1.
  especialize H with n, p as h;
    [ match goal with | |- False => idtac end; match type of h with forall (m:_), _ < m -> _ => idtac end ].
  Undo 1.
  especialize H with p as ?;
    [ match goal with | |- False => idtac end; match type of H_spec_ with forall (n:_) (m:_), n < m -> _ => idtac end ].
  Undo 1.
  especialize H with n, p as ?;
    [ match goal with | |- False => idtac end; match type of H_spec_ with forall (m:_), _ < m -> _ => idtac end ].
  Undo 1.


Goal forall (h:forall t z x y:nat, x = y -> x = x -> z = y -> x <= y), False.
Proof.
  intros h. 
  let ev1 := open_constr:(_) in
  assert ev1.

  (* epose _. *)
  (* unshelve (ltac2:(epose (_) as hhh)). *)
  (* unshelve (ltac2:(specialize_id_cstr @h constr:(hhh))). *)
  
  

  (ltac2:(refine_hd (Option.get (Ident.of_string "h"))
                     [Quantif;Quantif;Evar @myx; Quantif; SubGoal; SubGoal] [] [] 0)).






  ltac2:(intro_typed (Option.get (Ident.of_string "toto")) constr:(nat)).



  let newn := if_is_dep_prod h ltac:(constr:(n)) ltac:(constr:(S n)) in
  match constr:((ldirectarg,lnameargs,lnumargs)) with
  | (nil,nil,nil) => exact h
  | (cons ?directarg ?ldirectarg',_,_) =>
      lazymatch type of h with
      | (forall (h_premis:?t) , _) =>
          let intronme := ident:(h_premis) in (* ltac hack, if the product was not named,
                                           then "h_premis" is taken "as is" by fresh *)
          match directarg with
          | Quantif =>
              refine (fun intronme: t => _);
              specialize (h intronme);
              refine_hd h ldirectarg' lnameargs lnumargs newn
          | QuantifIgnore => 
              (* let intronme := fresh x in *)
              refine (fun intronme: t => _);
              specialize (h intronme);
              clear h_premis;
              refine_hd h ldirectarg' lnameargs lnumargs newn
          | Evar ?ename => 
              evar_as_string ename t;
              (* hackish: this should get the evar just created *)
              let hename := match goal with H:t|-_ => H end in
              specialize (h hename);
              subst hename;
              refine_hd h ldirectarg' lnameargs lnumargs newn
          | SubGoal =>
              (unshelve evar_as_string "SubGoal" t);
              (* hackish: this should get the evar just created *)
              [ | let hename := match goal with
                                  H:t|-_ => H
                                end in
                  specialize (h hename);
                  clearbody hename;
                  refine_hd h ldirectarg' lnameargs lnumargs newn ]
          end
      | _ => fail 1
      end
  | (nil,cons ?namearg ?lnameargs',_) => 
      lazymatch type of h with
      | (forall (h_premis:?t) , _) =>
          let intronme := ident:(h_premis) in (* ltac hack, if the product was not named,
                                                 then "h_premis" is taken "as is" by fresh *)
          lazymatch namearg with
          | (SubGoalAtName ?nme) => 
              if_eqstr ident:(h_premis) nme
              ltac:(idtac;refine_hd h (cons SubGoal nil) lnameargs' lnumargs n)
              ltac:(fail 0)
          | (EvarAtName ?nme ?nameevar) => 
              if_eqstr ident:(h_premis) nme
              ltac:(idtac;refine_hd h (cons (Evar nameevar) nil) lnameargs' lnumargs n)
              ltac:(fail 0)
          end
      | _ => fail 0
      end
  | (nil,_,cons ?numarg ?lnumargs') => 
      lazymatch type of h with
      | (forall (h_premis:?t) , _) =>
          let intronme := ident:(h_premis) in (* ltac hack, if the product was not named,
                                                 then "h_premis" is taken "as is" by fresh *)
          match numarg with
          | (SubGoalAtNum ?num) => 
              if_is_dep_prod h
                ltac:(fail 0)
                       ltac:(idtac;
                             tryif convert constr:(PeanoNat.Nat.leb newn num) constr:(true)
                             then
                               tryif convert num newn
                               then refine_hd h (cons SubGoal nil) lnameargs lnumargs' n
                               else (fail 3)
                             else
                               (fail 10000 "Did you not order the evar numbers?"))
          | (SubGoalUntilNum ?num) => 
              if_is_dep_prod h
                ltac:(fail 0)
                ltac:(idtac;tryif convert num newn
                             then refine_hd h (cons SubGoal nil) lnameargs lnumargs' n
                             else refine_hd h (cons SubGoal nil) lnameargs lnumargs n)
          | SubGoalAtAll => 
              if_is_dep_prod h
                ltac:(fail 0)
                ltac:(idtac; refine_hd h (cons SubGoal nil) lnameargs lnumargs n)
          end
      | _ => fail 0
      end
  | _ => lazymatch type of h with
         | (forall (h_premis:?t) , _) => refine_hd h (cons Quantif nil) lnameargs lnumargs n
         | _ => refine_hd h (@nil spec_arg)(@nil spec_arg)(@nil spec_arg) n
         end
  | _ => fail "refine_hd"
  end.

(* initialize n to zero. *)
Ltac refine_spec h lnameargs lnumargs := refine_hd h constr:(@nil spec_arg) lnameargs lnumargs 0.




(* TODO:sort the names or work modulo order on names? Or simply avoid infinite loops.
   TODO: if there is only one "at" and no "with"
 nor "until", then allow for the subgoal to be kept like an assert. *)
(* builds the inital unknown goal, call the refining tactic, end up by
   replacing h or naming the new hyp. *)
(* Precondition: name is already fresh *)

From Stdlib Require Sorting.Mergesort Structures.OrdersEx.


Module SpecargOrder <: Structures.Orders.TotalLeBool.
  Definition t := spec_arg.
  
  Definition leb a b := 
    match a with
      SubGoalAtNum na => 
        match b with
          SubGoalAtNum nb => Nat.leb na nb
        | _ => true
        end
    | _ => true
    end.

(* Nat.leb. *)
  
  Theorem leb_total : forall a1 a2, leb a1 a2 = true \/ leb a2 a1 = true.
  Proof.
    intros a1 a2. 
    destruct a1;destruct a2;auto.
    setoid_rewrite PeanoNat.Nat.leb_le.
    apply PeanoNat.Nat.le_ge_cases.
  Qed.
End SpecargOrder.


Module NatSort := Sorting.Mergesort.Sort(SpecargOrder).

Local Ltac espec_gen H lnames lnums name replaceb :=
  (* morally this evar is of type Type, don't know how to enforce this
     without having an ugly cast in goals *)
  (* idtac "espec_gen " H " " l " " name " " replaceb;  *)
  (* idtac "lnums = " lnums; *)
  let lnums := eval compute in (NatSort.sort lnums) in
  (* idtac "lnums = " lnums; *)
  tryif is_var H 
  then (let ev1 := open_constr:(_) in
        match replaceb with
          true =>  
            assert ev1 as name ; [ (refine_spec H lnames lnums)
                                 | clear H;try rename name into H ]
        | false =>
            assert ev1 as name; [ (refine_spec H lnames lnums) | ]
        end)
  else (* replaceb should be false in this case. *)
    (let H' := fresh "H" in
     specialize H as H';
     let ev1 := open_constr:(_) in
     assert ev1 as name; [ (refine_spec H' lnames lnums) | clear H' ]).

(* ltac2 int -> constr nat *)
Ltac2 rec int_to_coq_nat n :=
  match Int.equal n 0 with
  | true => constr:(O)
  | false => let n := int_to_coq_nat (Int.sub n 1) in
             constr:(S $n)
  end.

Ltac2 int_to_constr_nat n :=
  let val := int_to_coq_nat n in
  Std.eval_vm None val.

Ltac2 rec li_to_speclist_SGAtNum (li: int list): constr :=
  match li with
    [] => constr:(@nil spec_arg)
  | i :: l' => 
      let cl := li_to_speclist_SGAtNum l' in
      let ci := int_to_constr_nat i in
      constr:(cons (SubGoalAtNum $ci) $cl)
  end.

Ltac2 rec li_to_speclist_SGUntilNum (li: int list): constr :=
  match li with
    [] => constr:(@nil spec_arg)
  | i :: l' => 
      let cl := li_to_speclist_SGUntilNum l' in
      let ci := int_to_constr_nat i in
      constr:(cons (SubGoalUntilNum $ci) $cl)
  end.

Ltac2 rec li_to_speclist_EVAtName (li: ident list): constr :=
  match li with
    [] => constr:(@nil spec_arg)
  | i :: l' => 
      let cl := li_to_speclist_EVAtName l' in
      let istr := Ident.to_string i in
      let icstr := IdentParsing.coq_string_of_string istr in
      constr:(cons (EvarAtName $icstr $icstr) $cl)
  end.

(* Ltac2 occurrences_to_evaratname (li:ident list): constr := li_to_speclist_EVAtName li. *)

Ltac2 espec_at_using_ltac1_gen (h:constr) (li:int list) (occsevar:ident list) (newH: ident) (replaceb:bool):unit :=
  (* FIXME: we should also refuse when a section variables is given. *)
  if Bool.and (Bool.neg (is_var h)) replaceb
  then
    Control.zero (Tactic_failure (Some (fprintf "You must provide a name with 'as'.")))
  else
    let c1 := li_to_speclist_SGAtNum li in
    let c2 := li_to_speclist_EVAtName occsevar in
    (* let c := Std.eval_red constr:(List.app $c2 $c1) in   *)
    let replaceb := if replaceb then constr:(true) else constr:(false) in
    ltac1:(h c2 c1 newH replaceb |- espec_gen h c2 c1 newH replaceb)
            (Ltac1.of_constr h)
            (Ltac1.of_constr c2)
            (Ltac1.of_constr c1)
            (Ltac1.of_ident newH)
            (Ltac1.of_constr replaceb).

Ltac2 espec_until_using_ltac1_gen (h:constr) (li:int list) (occsevar:ident list) (newH: ident) (replaceb:bool) (atAll:bool):unit :=
  (* FIXME: we should also refuse when a section variables is given. *)
  if Bool.and (Bool.neg (is_var h)) replaceb
  then
    Control.zero (Tactic_failure (Some (fprintf "You must provide a name with 'as'.")))
  else
    let c1 := if atAll then constr:(cons SubGoalAtAll nil) else li_to_speclist_SGUntilNum li in
    let c2 := li_to_speclist_EVAtName occsevar in
    (* let c := Std.eval_red constr:(List.app $c2 $c1) in   *)
    let replaceb := if replaceb then constr:(true) else constr:(false) in
    ltac1:(h c2 c1 newH replaceb |- espec_gen h c2 c1 newH replaceb)
            (Ltac1.of_constr h)
            (Ltac1.of_constr c2)
            (Ltac1.of_constr c1)
            (Ltac1.of_ident newH)
            (Ltac1.of_constr replaceb).

Ltac2 interp_ltac1_id_list (lid:Ltac1.t) : ident list :=
  List.map (fun x => Option.get (Ltac1.to_ident x)) (Option.get (Ltac1.to_list lid)).

Ltac2 interp_ltac1_int_list (li:Ltac1.t) : int list :=
  List.map (fun x => Option.get (Ltac1.to_int x)) (Option.get (Ltac1.to_list li)).

Ltac2 interp_ltac1_hyp (h:Ltac1.t) : constr := Option.get (Ltac1.to_constr h).

(*                 let t:constr option := Ltac1.to_constr li in
                match t with
                  Some x => if Constr.equal x constr:(SubGoalAtAll)
                            then constr:(cons SubGoalAtAll nil)
                            else Control.zero (Tactic_failure (Some (fprintf "bad at specification.")))

                | _ => []
                end
 *)
(* call Ltac2'especialize on argscoming from Ltac1 notation *)
Ltac2 call_specialize_ltac2_gen (h:Ltac1.t) (li:Ltac1.t) levars newh (replaceb:bool) :=
  let li2 := match Ltac1.to_list li with
              None => []
            | Some _ => interp_ltac1_int_list li
            end in
  let levar2 := match Ltac1.to_list levars with
               None => []
             | Some _ => interp_ltac1_id_list levars
             end in
    espec_at_using_ltac1_gen
      (interp_ltac1_hyp h)
      li2
      levar2
      (Option.get (Ltac1.to_ident newh))
      replaceb.


(* call Ltac2'especialize on argscoming from Ltac1 notation *)

Ltac2 call_specialize_until_ltac2_gen (h:Ltac1.t) li levars newh replaceb (atAll:bool) :=
  let li2 := match Ltac1.to_list li with
               None => []
             | Some _ => interp_ltac1_int_list li
             end in
  let levar2 := match Ltac1.to_list levars with
                  None => []
                | Some _ => interp_ltac1_id_list levars
                end in
  if Int.gt (List.length li2) 1
  then
    (* msgi (List.length li'); *)
    Control.zero (Tactic_failure (Some (fprintf "In 'specialize X until I', I must be a singleton.")))
  else 
    espec_until_using_ltac1_gen (interp_ltac1_hyp h) li2 levar2
         (Option.get (Ltac1.to_ident newh)) replaceb atAll.


Ltac gen_hyp_name h := match goal with
                       | |- _ => let _ := is_var h in fresh h "_spec_"
                       | |- _ => fresh "H_spec_"
                       end.
Ltac dummy_term := constr:(Prop).


(* ESPECIALIZE AT *)
(* ********************* *)

Tactic Notation "especialize" constr(h) "with" ne_ident_list_sep(levars,",") "at" ne_integer_list_sep(li,",") "as" ident(newH) :=
  let tac := ltac2:(h li levars newH |- call_specialize_ltac2_gen h li levars newH false) in
  tac h li levars newH.

Tactic Notation "especialize" constr(h) "at" ne_integer_list_sep(li,",") "with" ne_ident_list_sep(levars,",") "as" ident(newH) :=
  let tac := ltac2:(h li levars newH |- call_specialize_ltac2_gen h li levars newH false) in
  tac h li levars newH.


Tactic Notation "especialize" constr(h) "with" ne_ident_list_sep(levars,",") "at" ne_integer_list_sep(li,",") "as" "?" :=
  let tac := ltac2:(h li levars newH |- call_specialize_ltac2_gen h li levars newH false) in
  let newH := gen_hyp_name h in
  tac h li levars ident:(newH).

Tactic Notation "especialize" constr(h) "at" ne_integer_list_sep(li,",") "with" ne_ident_list_sep(levars,",") "as" "?" :=
  let tac := ltac2:(h li levars newH |- call_specialize_ltac2_gen h li levars newH false) in
  let newH := gen_hyp_name h in
  tac h li levars ident:(newH).

(* ********************* *)
Tactic Notation "especialize" constr(h) "at" ne_integer_list_sep(li,",") "with" ne_ident_list_sep(levars,",") :=
  let tac := ltac2:(h li levars newH |- call_specialize_ltac2_gen h li levars newH true) in
  let dummy_id := gen_hyp_name h in
  tac h li levars ident:(dummy_id).

Tactic Notation "especialize" constr(h) "with" ne_ident_list_sep(levars,",") "at" ne_integer_list_sep(li,",") :=
  let tac := ltac2:(h li levars newH |- call_specialize_ltac2_gen h li levars newH true) in
  let dummy_id := gen_hyp_name h in
  tac h li levars ident:(dummy_id).

(* ********************* *)
Tactic Notation "especialize" constr(h) "with" ne_ident_list_sep(levars,",") "as" ident(newH) :=
  let tac := ltac2:(h li levars newH |- call_specialize_ltac2_gen h li levars newH false) in
  let li := dummy_term in       (* something that is not a list. *)
  tac h li levars newH.

Tactic Notation "especialize" constr(h) "with" ne_ident_list_sep(levars,",") "as" "?" :=
  let tac := ltac2:(h li levars newH |- call_specialize_ltac2_gen h li levars newH false) in
  let li := dummy_term in       (* something that is not a list. *)
  let newH := gen_hyp_name h in
  tac h li levars ident:(newH).

(* ********************* *)
Tactic Notation "especialize" constr(h) "at" ne_integer_list_sep(li,",") "as" ident(newH) :=
    let tac := ltac2:(h li levars newH |- call_specialize_ltac2_gen h li levars newH false) in
    let levars := dummy_term in       (* something that is not a list. *)
    tac h li levars newH.

(* ********************* *)
Tactic Notation "especialize" constr(h) "at" ne_integer_list_sep(li,",") "as" "?" :=
    let tac := ltac2:(h li levars newH |- call_specialize_ltac2_gen h li levars newH false) in
    let levars := dummy_term in       (* something that is not a list. *)
    let newH := gen_hyp_name h in
    tac h li levars ident:(newH).

(* ********************* *)
Tactic Notation "especialize" constr(h) "with" ne_ident_list_sep(levars,",") :=
  let tac := ltac2:(h li levars newH |- call_specialize_ltac2_gen h li levars newH true) in
  let li := dummy_term  in       (* something that is not a list. *)
  let dummy_id := gen_hyp_name h in
  tac h li levars ident:(dummy_id).

(* ********************* *)
Tactic Notation "especialize" constr(h) "at" ne_integer_list_sep(li,",") :=
    let tac := ltac2:(h li levars newH |- call_specialize_ltac2_gen h li levars newH true) in
    let levars := dummy_term in       (* something that is not a list. *)
    let dummy_id := gen_hyp_name h in
    tac h li levars ident:(dummy_id).




(* ESPECIALIZE UNTIL *)
(* ********************* *)
(* at * is actually a special case of until *)
Tactic Notation "especialize" constr(h) "at" "*" "with"  ne_ident_list_sep(levars,",") :=
    let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH true true) in
    let dummy_id := gen_hyp_name h in
    let li := dummy_term in
    tac h li levars ident:(dummy_id).

Tactic Notation "especialize" constr(h) "with"  ne_ident_list_sep(levars,",") "at" "*" :=
    let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH true true) in
    let dummy_id := gen_hyp_name h in
    let li := dummy_term in
    tac h li levars ident:(dummy_id).

Tactic Notation "especialize" constr(h) "at" "*" "with"  ne_ident_list_sep(levars,",") "as" ident(newH)
  :=
    let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH false true) in
    let li := dummy_term in
    tac h li levars newH.

Tactic Notation "especialize" constr(h) "with"  ne_ident_list_sep(levars,",") "at" "*" "as" ident(newH) :=
    let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH false true) in
    let li := dummy_term in
    tac h li levars newH.


Tactic Notation "especialize" constr(h) "with"  ne_ident_list_sep(levars,",") "at" "*" "as" "?" :=
    let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH false true) in
    let li := dummy_term in
    tac h li levars ident:(dummy_id).

Tactic Notation "especialize" constr(h) "at" "*" "as" ident(newH) :=
    let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH false true) in
    let levars := dummy_term in       (* something that is not a list. *)
    let dummy_id := gen_hyp_name h in
    let li := dummy_term in
    tac h li levars newH.

Tactic Notation "especialize" constr(h) "at" "*" "as" "?" :=
    let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH false true) in
    let levars := dummy_term in       (* something that is not a list. *)
    let dummy_id := gen_hyp_name h in
    let li := dummy_term in
    tac h li levars ident:(dummy_id).

Tactic Notation "especialize" constr(h) "at" "*" :=
    let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH true true) in
    let levars := dummy_term in       (* something that is not a list. *)
    let dummy_id := gen_hyp_name h in
    let li := dummy_term in
    tac h li levars ident:(dummy_id).


Tactic Notation "especialize" constr(h) "until" ne_integer_list_sep(li,",") "with" ne_ident_list_sep(levars,",") "as" ident(newH) :=
  let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH false false) in
  tac h li levars newH.

(* Strangely putting "with" before "until" is not recognized at
   parsing. Probably because "until" is not a keyword.
   Error: Syntax error: [ltac_use_default] expected after [tactic] (in
   [tactic_command]). *)
 Tactic Notation "especialize" constr(h) "with" ne_ident_list_sep(levars,",") "until" ne_integer_list_sep(li,",") "as" ident(newH) :=
  let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH false false) in
  tac h li levars newH.

 Tactic Notation "especialize" constr(h) "until" ne_integer_list_sep(li,",") "with" ne_ident_list_sep(levars,",") "as" ident(newH) :=
  let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH false false) in
  tac h li levars newH.

Tactic Notation "especialize" constr(h) "until" ne_integer_list_sep(li,",") "with" ne_ident_list_sep(levars,",") "as" "?" :=
  let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH false false) in
  let nme := gen_hyp_name h in
  tac h li levars ident:(nme).

Tactic Notation "especialize" constr(h) "with" ne_ident_list_sep(levars,",") "until" ne_integer_list_sep(li,",") "as" "?" :=
  let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH false false) in
  let nme := gen_hyp_name h in
  tac h li levars ident:(nme).


(* "with" must be first, probably because it is not a keyword: *)
Tactic Notation "especialize" constr(h) "until" ne_integer_list_sep(li,",") "with" ne_ident_list_sep(levars,",") :=
  let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH true false) in
  let nme := gen_hyp_name h in
  tac h li levars ident:(nme).

(* "with" must be first, probably because it is not a keyword: *)
Tactic Notation "especialize" constr(h) "with" ne_ident_list_sep(levars,",") "until" ne_integer_list_sep(li,",") :=
  let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH true false) in
  let nme := gen_hyp_name h in
  tac h li levars ident:(nme).

(* "with" must be first, probably because it is not a keyword: *)
Tactic Notation "especialize" constr(h) "until" ne_integer_list_sep(li,",") "as"  ident(newH) :=
  let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH false false) in
  let levars := dummy_term in
  tac h li levars ident:(newH).

(* "with" must be first, probably because it is not a keyword: *)
Tactic Notation "especialize" constr(h) "until" ne_integer_list_sep(li,",") "as"  "?" :=
  let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH false false) in
  let nme := gen_hyp_name h in
  let levars := dummy_term in
  tac h li levars ident:(nme).

(* "with" must be first, probably because it is not a keyword: *)
Tactic Notation "especialize" constr(h) "until" ne_integer_list_sep(li,",") :=
  let tac := ltac2:(h li levars newH |- call_specialize_until_ltac2_gen h li levars newH true false) in
  let nme := gen_hyp_name h in
  let levars := dummy_term in
  tac h li levars ident:(nme).



(* Experimenting a small set of tactic to manipulate a hyp: *)
(*
Ltac quantify H :=
  match type of H with
    (forall x:?t, _) => refine (fun (x:t) => _); specialize (H x)
  end.

Ltac evary H :=
  match type of H with
    (forall x:?t, _) => evar (x:t); specialize (H x);subst x
  end.

Ltac goaly H :=
  match type of H with
    (forall x:?t, _) => [> assert (x:t); [ | specialize (H x)]]
  end.
  
Ltac stopy H := exact H.
Ltac start name :=
  let ev1 := open_constr:(_) in
  assert ev1 as name.

Lemma foo: forall x y : nat,
    (forall (n m p :nat) (hhh:n < m) (iii:n <= m), p > 0 -> p+m=n) -> False.
Proof.
  intros x y H. 
  start newH.
  quantify H.
  quantify H.
  quantify H.
  quantify H.
  goaly H.
  { now apply PeanoNat.Nat.lt_le_incl. }
  stopy H.
Abort.
*)  



(* tests *)
Definition eq_one (i:nat) := i = 1.
Definition hidden_product := forall i j :nat, i+1=j -> i+1=j -> i+1=j.

Lemma foo: forall x y n m p :nat,
    (forall  (hhh:n < m) (iii:n <= m),
        p > 0
        -> p > 2
        -> p > 1
        -> hidden_product) -> False.
Proof.
  intros x y n m p H. 
  especialize H at *;[ | | | | | ].
  5: match goal with
       H1 : n < m
         , H2 : n <= m
           , H3 : p > 0
             , H4 : p > 2 |- _ => idtac
     end.
Abort.

Lemma foo: forall x y : nat,
    (forall (n m p :nat) (hhh:n < m) (iii:n <= m),
        p > 0
        -> p > 2
        -> p > 1
        -> hidden_product) -> False.
Proof.
  intros x y H. 
Abort.
