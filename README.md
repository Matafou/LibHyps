This Library provides several coq tactics and tacticals to deal with
hypothesis during a proof.

Main page and documentation: https://github.com/Matafou/LibHyps

Demo file [demo.v](https://github.com/Matafou/LibHyps/blob/master/tests/demo.v) acts as a documentation.

# Short description:

LibHyps provides utilities for hypothesis manipulations. For example a
    few tacticals to deal with "new" hypothesis (new = their name did
    not appear in the previous goal):

- `tac /r`: applies tac then revert new hypothesis.
- `tac /s`: applies tac then try to `subst` with new hyps.
- `tac /n`: applies tac then try to automatically rename new hyps from their type.
- `tac /g`: applies tac then try to tidy non-prop hyps to save room in your goal.
- `tac/sng` : combination of the above
- `tac1 ; { tac2 }` applies tac1, then tac2 on each new hyp (generic version of above).
- `especialize H at ...` to generate one or several subgoals from the
  premise(s) of `H` (which can be a hypothesis name or an lemma name).
  This tactic comes with many variants. See below.
- `assert premise i of H` generates a subgoal to prove the `i`th
  premise of `H`, without specializing `H`.

# Quick Test
## Quick install using opam

If you have not done it already add the coq platform repository to opam!

```bash
opam repo add coq-released https://coq.inria.fr/opam/released
```

and then:

```bash
opam install coq-libhyps
```

## Quick install using github:

Clone the github repository:

```bash
git clone https://github.com/Matafou/LibHyps
```
then compile:
```bash
configure.sh
make
make install
```

## Quick test:

```coq
Require Import LibHyps.LibHyps.
```

Demo files [demo.v](https://github.com/Matafou/LibHyps/blob/master/tests/demo.v).



## The especialize tactic

Let `H` be a hypothesis (or lemma) with type `∀ x y z, H1 x -> H2 y -> H3 x y -> C x y z`.

```
especialize H at 2.
```

Creates a subgoal of the form:

```
 ∀ x y z, H1 x -> H2 y
```
  
and applies it the subgoal to `H` which thus becomes:
  
```
H: ∀ x y z, H1 x -> H3 x y -> C x y z
```

Variants
+ `especialize H at 2 as h.` specializes a *copy* of `H` named `h`.
  Leaves `H` unchanged. quantifying them.
+ `especialize H at 2,3.`
+ `especialize H at *.` means specialize *all* premises
+ `especialize H until 2.` all premises until the 2nd.

+ By default all non-dependent hypothesis of `H` are left quantified
  (hence its type above `∀ x y z, H1 -> H2`). But you can specify the
  ones that should rather be transformed into existential variables.
  Examples:

  + `especialize H at 2 with y.` Creates an evar `?y` subgoal of the form:

    ```
     ∀ x z, H1 x -> H2 ?y
    ```
  
    and specializes `H` with this subgoal and evar `?y`:
  
    ```
    H: ∀ x z, H1 x -> H3 x ?y -> C x ?y z
    ```
    (where H1 and H3 reference `?y` now).
    
  + Several evars can be specified, they must be in order:

    ```especialize H at 2 with x,y.```


Note that (contrary to previous versions of this library), if you
forget to list a variable, the tactic won't fail. Instead it will
simply leave the variable quantified in the original hypothesis **and
in subsequently created subgoals**.

For example, after this:

  ``` coq
  Lemma test_espec8: forall x:nat, (forall a :nat, a = 1 -> x = 1 -> False) -> x > 1.
  Proof.
    intros x h. 
  ```

the goal looks like this

``` coq
  x : nat
  h : forall a : nat, a = 1 -> x = 1 -> False
  ============================
  x > 1
```

the following tactic:

``` coq
especialize h with a at 1.
```

gives two subgoals:

``` coq
  x : nat
  ============================
  ?a = 1

  x : nat
  h : x = 1 -> False
  ============================
  x > 1

```

Whereas

``` coq
especialize h at 1.
```

gives (note how `a` is quantified in both subgoals, which makes the
first one unprovable):

``` coq
  x, a : nat
  ============================
  a = 1
  
  x : nat
  h : nat -> x = 1 -> False
  ============================
  x > 1
```


## QUICK REF: Pre-defined tacticals /s /n...

The most useful user-dedicated tacticals are the following

  + `tac /s` try to apply `subst` on each new hyp.
  + `tac /r` revert each new hyp.
  + `tac /n` auto-rename each new hyp.
  + `tac /g` group all non-Prop new hyp at the top of the goal.
  + combine the above, as in `tac /s/n/g`.
  + usual combinations have shortcuts: `\sng`, `\sn`,`\ng`,`\sg`...

# Install


# More information

## Deprecation from 1.0.x to 2.0.x

  + "!tac", "!!tac" etc are now only loaded if you do: `Import
    LibHyps.LegacyNotations.`, the composable tacticals described
    above are preferred.
  + "tac1 ;; tac2" remains, but you can also use "tac1; { tac2 }".
  + "tac1 ;!; tac2" remains, but you can also use "tac1; {< tac2 }".

## KNOWN BUGS

Due to Ltac limitation, it is difficult to define a tactic notation
`tac1 ; { tac2 }` which delays `tac1` and `tac2` in all cases.
Sometimes (rarely) you will have to write `(idtac; tac1); {idtac;
tac2}`. You may then use tactic notation like: `Tactic Notation tac1'
:= idtac; tac1.`.

## Examples

```coq
Require Import LibHyps.LibHyps.

Lemma foo: forall x y z:nat,
    x = y -> forall  a b t : nat, a+1 = t+2 -> b + 5 = t - 7 ->  (forall u v, v+1 = 1 -> u+1 = 1 -> a+1 = z+2)  -> z = b + x-> True.
Proof.
  intros.
  (* ugly names *)
  Undo.
  (* Example of using the iterator on new hyps: this prints each new hyp name. *)
  intros; {fun h => idtac h}.
  Undo.
  (* This gives sensible names to each new hyp. *)
  intros ; { autorename }.
  Undo.
  (* short syntax: *)
  intros /n.
  Undo.
  (* same thing but use subst if possible, and group non prop hyps to the top. *)
  intros ; { substHyp }; { autorename}; {move_up_types}.
  Undo.
  (* short syntax: *)  
  intros /s/n/g.
  Undo.
  (* Even shorter: *)  
  intros /sng.

  (* Let us instantiate the 2nd premis of h_all_eq_add_add without
     copying its type. And instantiating u with an evar. *)
  especialize h_all_eq_add_add_ with u at 2.
  { apply Nat.add_0_l. }
  Undo 6.
  intros until 1.
  (** The taticals apply after any tactic. Notice how H:x=y is not new
    and hence not substituted, whereas z = b + x is. *)
  destruct x eqn:heq;intros /sng.
  - apply I.
  - apply I.
Qed.
Lemma foo: forall x y z:nat,
    x = y -> forall  a b t : nat, a+1 = t+2 -> b + 5 = t - 7 ->  (forall u v, v+1 = 1 -> u+1 = 1 -> a+1 = z+2)  -> z = b + x-> True.
Proof.
  intros.
  (* ugly names *)
  Undo.
  (* Example of using the iterator on new hyps: this prints each new hyp name. *)
  intros; {fun h => idtac h}.
  Undo.
  (* This gives sensible names to each new hyp. *)
  intros ; { autorename }.
  Undo.
  (* short syntax: *)
  intros /n.
  Undo.
  (* same thing but use subst if possible, and group non prop hyps to the top. *)
  intros ; { substHyp }; { autorename}; {move_up_types}.
  Undo.
  (* short syntax: *)
  intros /s/n/g.
  Undo.
  (* Even shorter: *)
  intros /sng.

  (* Let us instantiate the 2nd premis of h_all_eq_add_add without copying its type: *)
  especialize h_all_eq_add_add_ with u at 2.
  { apply Nat.add_0_l. }
  (* now h_all_eq_add_add is specialized *)
  Undo 6.
  intros until 1.
  (** The taticals apply after any tactic. Notice how H:x=y is not new
    and hence not substituted, whereas z = b + x is. *)
  destruct x eqn:heq;intros /sng.
  - apply I.
  - apply I.
Qed.
```

## Short Documentation

The following explains how it works under the hood, for people willing
to apply more generic iterators to their own tactics. See also the code.
  
### Iterator on all hypothesis

  + `onAllHyps tac` does `tac H` for each hypothesis `H` of the current goal.
  + `onAllHypsRev tac` same as `onAllHyps tac` but in reverse order
    (good for reverting for instance).

### Iterators on EACH NEW hypothesis

  + `tac1 ;{ tac2 }` applies `tac1` to current goal and then `tac2` to
    each new hypothesis in each subgoal (iteration: older first).
  + `tac1 ;{< tac2 }` is similar but applies tac2 on newer hyps first.

### Customizable hypothesis auto naming system

Using previous taticals (in particular the `;!;` tactical), some
tactic allow to rename hypothesis automatically.

- `autorename H` rename `H` according to the current naming scheme
  (which is customizable, see below).

- Hence `onAllHyps autorename` applies `autorename` to all hypothesis.

#### How to cstomize the naming scheme

The naming engine analyzes the type of hypothesis and generates a name
mimicking the first levels of term structure. At each level the
customizable tactic `rename_hyp` is called. One can redefine it at
will. It must be of the following form (Ltac2):

```coq
Require Import Ltac2.Ltac2.
From Stdlib Require Import List.
Import ListNotations.
Local Set Default Proof Mode "Classic". (* Optional This restores ltac1 proof mode. *)

(** Redefining rename_hyp*)
(* First define a naming ltac. It takes the current level n and
   the sub-term th being looked at. It returns a "name". *)
Ltac2 rename_hyp_2 _ th :=
  match! th with
  | true <> false => [ String "tNEQf" ]
  | true = false => [ String "tEQf" ]
  end.

Ltac2 Set rename_hyp := rename_hyp_2.

(* Suppose I want to add later another naming rule: *)
Ltac2 rename_hyp_3 n th :=
  match! th with
  | Nat.eqb ?x ?y = true => [ String "Neqb"; Rename x ; Rename y ]
  | true = Nat.eqb ?x ?y => [ String "Neqb" ; Rename x ;  Rename y ]
  | _ => rename_hyp_2 n th (* call the previously defined tactic *)
  end.

(* Then overwrite the definition of rename_hyp using the ::= operator. :*)
Ltac2 Set rename_hyp := rename_hyp_3.
```

Where `Rename` stands for calling the naming scheme recursively
(unless the maximum depth is reached).

#### How to define variants of these tacticals?

Some more example of tacticals performing cleaning and renaming on new
hypothesis.

```coq
(* subst or revert *)
Tactic Notation (at level 4) "??" tactic4(tac1) :=
  (tac1 ;; substHyp ;!; revertHyp).
(* subst or rename or revert *)
Tactic Notation "!!!" tactic3(Tac) := (Tac ;; substHyp ;!; revert_if_norename ;; autorename).
(* subst or rename or revert + move up if in (Set or Type). *)
Tactic Notation (at level 4) "!!!!" tactic4(Tac) :=
      (Tac ;; substHyp ;!; revert_if_norename ;; autorename ;; move_up_types).
```


# About the logical "completeness" of `especialize`

Suppose we have this goal:


```coq
  Lemma foo: (forall x:nat, x = 1 -> (x>0) -> x < 0) -> False.
  Proof.
    intros h.

h : forall x : nat, x = 1 -> x > 0 -> x < 0
  ============================
  False

especialize h with x at 2.


  h : ?x = 1 -> ?x > 0 -> ?x < 0
  ============================
  ?x > 0

goal 2 (ID 88) is:
 False

```

Note that in this case it would be preferable (and logically more
accurate) to have a hypothesis `h2: ?x = 1` in the context, since the
premise 2 of H needs only to be proved when premise 1 is true. Note
however that in this kind of situation most users would wait to be
able to prove premise 1 before instantiating premise 2. `especialize`
does not cover this kind of subtleties. Another tactic is under
development to support this kind of reasoning.



<!--  LocalWords:  subgoal unifiable evars
 -->
