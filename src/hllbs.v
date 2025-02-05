(** Title: Verifying a Lazy Concurrent List-Based Set Algorithm in Iris

    Author: Daniel Nezamabadi

    Course: "Research in Computer Science" at ETH Zurich

    Date: February 03, 2025

    Supervisors: Isaac van Bakel, Prof. Dr. Ralf Jung

    Department of Computer Science, ETH Zürich *)

(** * Abstract ****************************************************************)

(** We implemented the data structure presented in
    "A Lazy Concurrent List-Based Set Algorithm" by Heller et al., in HeapLang,
    defined logically atomic specifications for [add], [remove], and [contains],
    and proved the implementation of [add] and [remove] correct with regard to
    those specifications in Iris. We also briefly discuss the difficulty of
    verifying [contains] and an alternative way of setting up the invariant. *)

(** * Introduction ************************************************************)

(** In "A Lazy Concurrent List-Based Set Algorithm", Heller et al.,
    present a concurrent, list-based set algorithm in which insertion and
    removal operations are optimistic, removal operations are lazy
    (the target is first marked as removed, then physically unlinked) and
    membership test operations are wait-free (every call finishes in a finite
    number of steps) and never interfere with any concurrent operations.

    The optimistic operations traverse the list without locking, locking only
    the target entry and its predecessor, followed by a check for
    synchronization conflicts. If no conflict has been detected, the operation
    is executed. Otherwise, the operation is restarted.

    While the algorithm has been studied in the context of formal verification
    before, it has (to our knowledge) yet to be verified using separation logic.
    This work implements the data structure and its methods in HeapLang, defines
    the specification for the data structure and its method, and proves the
    specifications for creating a new set, adding a key to the set, and removing
    a key from the set using Iris. We do not prove the correctness of the
    contains method, as it is out of scope for this project. *)

(** * Mechanization ***********************************************************)

Require Import ZArith.
From iris.algebra Require Import excl_auth gset dfrac.
From iris.program_logic Require Import atomic.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import lock.

Section hllbs.

  (** ** Setting Up Iris ******************************************************)

  (** Before jumping into defining and proving, we first setup Iris by bringing
      a namespace and some ghost state into our context, followed by some
      notation. *)

  (** As in the treiber example in the Iris example repository, we quantify the
      namespace [N] over the section. This allows the user to instantiate
      the namespace, making it possible to use this module as a library. *)
  Context (N : namespace).

  Class setG Σ := SetG {
    (** We leverage the general lock interface provided by Iris for HeapLang. *)
    set_lock :: lock;
    set_lockG :: lockG Σ;
    (** Similar to the treiber example, we use [excl_authR] to model the
        contents of the set. *)
    set_contG :: inG Σ (excl_authR (gsetO ZO));
    (** We use [authR (gset loc)] to model a monotonically increasing set of
        locations, which we use to keep track of all (valid) nodes that have ever
        been allocated for a particular set. *)
    set_nodesG :: inG Σ (authR (gset loc));
    (** We use [agreeR loc] to keep track of the fact that a set has a unique
        tail node without exposing this fact to the user. *)
    set_tailG :: inG Σ (agreeR loc) }.

  Context `{!heapGS Σ, !setG Σ}.
  Notation iProp := (iProp Σ).

  (** ** Nullable References **************************************************)

  (** Since the data structure makes use of nullable references, we need to
      model them in Coq and HeapLang. A standard way of doing this is to model
      a nullable reference as an option. *)

  (** *** Nullable References in Coq ******************************************)
  Notation lopt := (option loc).

  (** *** Nullable References in HeapLang ************************************)
  Definition lopt_to_val (x : lopt) : val :=
    match x with
    | None => NONEV
    | Some ℓ => SOMEV #ℓ
    end.
  Notation "lopt# x":= (lopt_to_val x) (at level 8, format "lopt# x").

  (** We also need to define what it means to dereference a nullable reference
      in HeapLang. To model a NullPointerException, we make [deref] return a
      bogus expression, resulting in the execution getting stuck. *)
  Notation stuck := (#() #()).
  Definition deref : val :=
    λ: "node",
      match: (! "node") with
        SOME "node" => "node"
      | NONE => stuck  (* "NullPointerException" *)
      end.

  Lemma deref_spec (ℓ : loc) (v : val) :
    {{{ ℓ ↦□ SOMEV v }}}
      deref #ℓ
    {{{ RET v ; True }}}.
  Proof.
    iIntros (Φ) "Hℓ HΦ".
    wp_lam. wp_load. wp_match.
    iApply ("HΦ" with "[$]").
  Qed.

  (** ** Extended Integers ****************************************************)

  (** The paper states that the algorithm ".. works for any ordered set of
      keys that has maximum and minimum values and is well-founded, that is for
      any given key, there are only finitely many smaller keys".
      HeapLang integers are not bounded, which is why we use a sum to represent
      unbounded integers with negative and positive infinity.

      Note that this new "type" is not well-founded. This is not a problem as
      the well-foundedness seems to be only used to argue that contains is
      wait-free, which is not something that we prove in Iris. *)

  (** *** Extended Integers in Coq ********************************************)

  Inductive extZ :=
  (** Finite integer *)
  | Fin (z : Z)
  (** Positive infinity. *)
  | PInf
  (** Negative infinity. *)
  | NInf.

  (** [extZ] is not an empty type.
      This is for example required to use [bi.later_exist]. *)
  Global Instance extZ_inhabited : Inhabited extZ .
  Proof. constructor. apply NInf. Qed.

  (** Equality on [extZ] is decidable.
      This allows us to check whether the key is in the set or not by
      using [destruct (decide (ck = Fin key))] in the proof. *)
  Global Instance extZ_eqdecision: EqDecision extZ.
  Proof. solve_decision. Qed.

  (** Defines the "less than" relation for extended integers.
      [NInf] is less than everything except itself, [PInf] is larger than
      everything except itself, and [Fin x] is less than [Fin y] if [x < y]. *)
  Definition lt (x y : extZ) :=
    match x, y with
    | Fin x, Fin y => (x < y)%Z
    | NInf, _ => y ≠ NInf
    | _, PInf => x ≠ PInf
    | _, _ => False
    end.

  (** Defines the "less than or equal" relation for extended integers. *)
  Definition leq (x y : extZ) :=
    match x, y with
    | Fin x, Fin y => (x ≤ y)%Z
    | NInf, _ => True
    | _, PInf => True
    | _, _ => False
    end.

  (** Some basic lemmas about comparing extended integers. *)

  Lemma fin_neq_z (x y : Z) :
    (Fin x) ≠ (Fin y) <-> x ≠ y.
  Proof.
    split.
    - congruence.
    - intros. injection. congruence.
  Qed.

  Lemma leq_neq_lt (x y : extZ) :
    leq x y -> y ≠ x -> lt x y.
  Proof.
    destruct x, y; simpl; intros Hleq Hneq; try done.
    rewrite fin_neq_z in Hneq. lia.
  Qed.

  Lemma lt_trans (x y z : extZ) :
    lt x y -> lt y z -> lt x z.
  Proof. destruct x, y, z; simpl; intros Hlt1 Hlt2; try auto with lia. Qed.

  Lemma lt_leq_trans (x y z : extZ) :
    lt x y -> leq y z -> lt x z.
  Proof. destruct x, y, z; simpl; intros Hlt1 Hlt2; try auto with lia. Qed.

  (** *** Extended Integers in HeapLang ***************************************)

  (** Shorthands for positive and negative infinity in HeapLang. *)
  Notation PINV := (InjLV (#true)).
  Notation NINV := (InjLV (#false)).

  (** Converts an extended integer into a HeapLang value. *)
  Definition extZ_to_val (x : extZ) : val :=
    match x with
    | Fin z => SOMEV #z
    | PInf => PINV
    | NInf => NINV
    end.
  Notation "extZ# x":= (extZ_to_val x) (at level 8, format "extZ# x").

  (** Implements "less than" on extended integers values in HeapLang. *)
  Definition ltv : val :=
    λ: "x" "y",
      match: "x" with
        InjL "x_pos" =>
          (match: "y" with
             InjL "y_pos" => (~"x_pos") && "y_pos"
           | InjR "y_i" => (~"x_pos")
           end)
      | InjR "x_i" =>
          (match: "y" with
             InjL "y_pos" => "y_pos"
           | InjR "y_i" => "x_i" < "y_i"
           end)
      end.

  (** Implements "equals" on extended integers values in HeapLang. *)
  Definition eqv: val :=
    λ: "x" "y",
      match: "x" with
        InjL "x_pos" =>
          (match: "y" with
             InjL "y_pos" => "x_pos" = "y_pos"
           | InjR "y_i" => #false
           end)
      | InjR "x_i" =>
          (match: "y" with
             InjL "y_pos" => #false
           | InjR "y_i" => "x_i" = "y_i"
           end)
      end.

  (** If we know that [ez] is not the same as [Fin z'], the HeapLang function
      checking whether they are equal will return false. *)
  Lemma eqv_neq_fin (ez : extZ) (z' : Z) :
    {{{ ⌜ ez ≠ Fin z' ⌝ }}}
    eqv extZ#ez (InjRV #z')
    {{{ RET #false; True }}}.
  Proof.
    iIntros (Φ) "%Hneq HΦ".
    destruct ez.
    - wp_lam. wp_pures.
      rewrite bool_decide_eq_false_2; [|congruence].
      by iApply "HΦ".
    - wp_lam. wp_pures. by iApply "HΦ".
    - wp_lam. wp_pures. by iApply "HΦ".
  Qed.

  (** Some inversion lemmas. **************************************************)

  Lemma extZ_inv_fin (k : Z) (ek : extZ) :
    InjRV #k = extZ#ek -> ek = (Fin k).
  Proof.
    intros Heq.
    rewrite /extZ_to_val in Heq.
    destruct ek.
    - by injection Heq as ->.
    - discriminate.
    - discriminate.
  Qed.

  Lemma extZ_inv_ninf (ek : extZ) :
    InjLV #false = extZ#ek -> ek = NInf.
  Proof. destruct ek; done. Qed.

  Lemma extZ_inv_pinf (ek : extZ) :
    InjLV #true = extZ#ek -> ek = PInf.
  Proof. destruct ek; done. Qed.

  (** ** Lazy Concurrent List-Based Set ***************************************)

  (** We now have the basic constructs ready, and can start to define the set
      data structure. First, we will give the implementation in HeapLang,
      followed by the invariant. After that we define (many!) auxiliary lemmas
      to finally prove the atomic specification for [add] and [remove].

      Recall that we will not prove [contains]. This is because its
      linearization point is non-trivial in the case of an unsuccessful call.
      We postpone a more thorough discussion to the end.  *)

  (** *** Modeling the Nodes **************************************************)

  (** Since the set is implemented as a linked list, we will need to model its
      nodes in HeapLang. The paper defines a node as the following Java class:

      private class Entry {
        int key;
        Entry next;
        boolean marked;
        lock lock;
      }

      In HeapLang, we will model the reference to an Entry object [e] as
      [e ↦□ (key, ℓℓₙ, ℓₘ, lock)], where [key] is an extended integer,
      [ℓℓₙ] a reference to the reference of the next node, [ℓₘ] a reference
      to a boolean which indicates whether a node has been logically deleted,
      and [lock] an instance of a lock.

      This representation has the advantage that once we have read a node from
      the list, we will always be able to read its key and access its lock.
      Additionally, as we will see later, by opening the set invariant it is
      also always possible to get half the permission to [ℓℓₙ] and [ℓₘ]
      allowing us to read the reference to the next node and check
      whether a node has been marked. By acquiring the lock, we can collect the
      other half of the permission and also update their values.
      Some exceptions apply though: the sentinel head and node values should
      never be (logically) deleted, the tail node should always point to null,
      and once a node has been physically removed, it should remain logically
      removed as well. The double-references allow us to have more fine-grained
      control.

      In a way, this is just making the assumptions about a node explicit:
      - Once we read a node, we should always be able to access all of its
        contents
      - The key and lock of a node can never be updated
      - next and marked can be updated
      The last point in particular hints at why modeling a node as a "pure"
      tuple without references is not straightforward. Imagine thread A reads
      some node, i.e. a 4-tuple, and then gets preempted. Thread B changes
      that node's next reference by inserting an element. Now, when thread A
      resumes, it would read a stale version of the next reference! This issue
      is caused by the fact that the algorithm does not lock nodes while walking
      the list.

      What follows is an implementation of this idea for the nodes. Note that
      [new_node] returns a "normal" reference. The conversion to a persistent,
      read-only points-to happens later.
   *)

  Definition get_key : val :=
    λ: "node", Fst (Fst (Fst (deref "node"))).

  Definition get_next : val :=
    λ: "node", Snd (Fst (Fst (deref "node"))).

  Definition set_next : val :=
    λ: "node" "next",
      get_next "node" <- SOME "next".

  Definition get_mark : val :=
    λ: "node", (Snd (Fst (deref "node"))).

  Definition is_marked : val :=
    λ: "node", ! (get_mark "node").

  Definition set_mark : val :=
    λ: "node", get_mark "node" <- #true.

  Definition get_lock : val :=
    λ: "node", Snd (deref "node").

  Definition lock_node : val :=
    λ: "node", acquire (get_lock "node").

  Definition unlock_node : val :=
    λ: "node", release (get_lock "node").

  Definition new_node : val :=
    λ: "key" "next",
      let: "next'" := ref "next" in
      let: "mark" := ref #false in
      let: "lock" := newlock #() in
      ref (SOME ("key", "next'", "mark", "lock")).

  (** *** Helper Functions ****************************************************)

  (** In this section we define the walk and validate methods. Factoring out
      the recursive part of the walk makes it easier to reason about.
      Additionally, [walk2] and [validate] are used both in [add] and [remove],
      so by factoring these into separate functions we hopefully avoid some
      unnecessary duplication. *)

  (** Used by [contains] to walk the linked list. Note that we do not lock any
      nodes. *)
  Definition walk : val :=
    rec: "walk" "key" "curr" :=
      if: (ltv (get_key (! "curr")) "key")
      then ("curr" <- deref (get_next (! "curr")) ;;
            "walk" "key" "curr")
      else #().

  (** Used by [add] and [remove] to walk the linked list. Note that we need to
      keep also track of the predecessor node. Similar to [walk], no nodes are
      locked. *)
  Definition walk2 : val :=
    rec: "walk2" "key" "pred" "curr" :=
      if: (ltv (get_key (! "curr")) "key")
      then ("pred" <- ! "curr" ;;
            "curr" <- deref (get_next (! "curr")) ;;
            "walk2" "key" "pred" "curr")
      else #().

  (** After locking, [validate] is called to check whether we are in a valid
      state to execute an operation. In particular, this means that neither the
      predecessor nor the current node has been (logically) deleted, and that
      they are directly connected, which excludes physical changes like another
      thread removing the current node or inserting something in between those
      two nodes. *)
  Definition validate : val :=
    λ: "pred" "curr",
      (~(is_marked "pred")) && (~(is_marked "curr"))
      && ((deref (get_next "pred")) = "curr").

  (** *** Set Operations ******************************************************)

  (** We now have all pieces ready to define the main set operations:
      - Creating a new set
      - Adding something to a set
      - Removing something from a set
      - Checking whether a value is contained in a set *)

  (** An empty set consists of two sentinel nodes: the head with value negative
      infinity pointing to the tail with value positive infinity. The tail
      does not point to anything. *)
  Definition new_set : val :=
    λ: <>,
      let: "tail" := new_node PINV NONEV in
      let: "head" := new_node NINV (SOME "tail") in
      "head".

  (** [add] is implemented in the following way:
      1. Find the position of key in the sorted linked list without locking
      2. Once the position has been found, lock the predecessor and current node
      3. Make sure that we are in a valid state to do an add - if not, retry
      4a. If the key is already in the list, unlock the nodes and return false
      4b. If the key is not in the list, create a new node,
          hook it into the list, unlock the nodes, and return true.
   *)
  Definition add : val :=
    rec: "add" "head" "key" :=
      let: "pred" := ref "head" in
      let: "curr" := ref (deref (get_next "head")) in
      walk2 "key" "pred" "curr" ;;
      lock_node (! "pred") ;; lock_node (! "curr");;
      if: (validate (! "pred") (! "curr"))
      then
        (if: (eqv (get_key (! "curr")) "key")
         then (unlock_node (! "curr") ;; unlock_node (! "pred") ;; #false)
         else
           (let: "entry" := (new_node "key" (SOME (! "curr"))) in
            (set_next (! "pred") "entry" ;;
             unlock_node (! "curr") ;; unlock_node (! "pred") ;; #true)))
      else (unlock_node (! "curr") ;; unlock_node (! "pred") ;;
            "add" "head" "key").

  (** [remove] is implemented in a very similar way as [add]. Note that before
      physically removing a node, we first logically remove it (i.e. mark it).
      This ends up being the linearization point in the case where the key is
      in the set. *)
  Definition remove : val :=
    rec: "remove" "head" "key" :=
      let: "pred" := ref "head" in
      let: "curr" := ref (deref (get_next "head")) in
      walk2 "key" "pred" "curr" ;;
      lock_node (! "pred") ;; lock_node (! "curr");;
      if: (validate (! "pred") (! "curr"))
      then
        (if: (~(eqv (get_key (! "curr")) "key"))
         then (unlock_node (! "curr") ;; unlock_node (! "pred") ;; #false)
         else
           (set_mark (! "curr") ;;  (* logically remove first *)
            set_next (! "pred") (deref (get_next (! "curr"))) ;;
            unlock_node (! "curr") ;; unlock_node (! "pred") ;; #true))
      else (unlock_node (! "curr") ;; unlock_node (! "pred") ;;
            "remove" "head" "key").

  (** [contains] looks deceptively simple. It simply walks through the list
      and checks whether there is an ummarked node with that key at the
      expected position. Note that it never locks anything; in fact, it is
      wait-free. *)
  Definition contains : val :=
    λ: "head" "key",
      let: "curr" := ref "head" in
      walk "key" "curr" ;;
      (eqv (get_key (! "curr") "key")) && (~is_marked (! "curr")).

  (** *** Invariant ***********************************************************)

  (** It is now time to define the invariant that will allow us to prove
      logical atomicity.

      On a high level, the contents of the set are determined by the
      nodes that are reachable via the head. We model this linked list in our
      invariant using a list of tuples that contain the location of a node,
      whether it is marked, and its key, and call it [llist]. We will see later
      why we keep track of the locations.

      Given such a list, we can determine the set of keys by considering only
      those nodes that are not marked. This is defined in [ll_keys], and is
      represented with the ghost state [own γc (●E ls)] and [own γc (◯E ls)],
      which keeps the set in sync with the physical representation and also
      allows us to make statements about the content of the set using
      [set_content].

      The responsibility of connecting an instance of [llist] to a "physical"
      state in HeapLang falls on [phys_list_aux]. Until now, the invariant is
      similar to the one described in the treiber example.

      However, this description is incomplete, as it does not say anything about
      nodes that have been physically deleted, i.e. are not reachable from the
      head. This is a problem, because it is possible for a thread to end up
      on such a node, as the walk does not lock nodes.

      Imagine the set {1}, with the following physical representation:

      head
        ▼
      ┌───┐  ┌───┐  ┌───┐
      │-∞ ├─►│ 1 ├─►│+∞ │
      └───┘  └───┘  └───┘

      Now, we run add(2) and remove(1) in parallel, with add(2) running on
      thread 1, and remove(1) running on some other thread.
      First, add(2) initializes pred and curr to point to the nodes with values
      -∞ and 1 respectively, after which it gets preempted.
      Secondly, remove(1) fully executes, resulting in the following physical
      representation, with pred and curr being part of the state of thread 1
      running add(2), and the node with value 1 being both marked and physically
      removed:

             head
               ▼
             ┌───┐   ┌───┐
      pred─► │-∞ ├──►│+∞ │
             └───┘ ┌►└───┘
             ┌───x │
      curr─► │ 1 ├─┘
             └───┘

      Since the value of curr is less than 2, thread 1 must continue its walk
      by accessing the next field of the curr node. In other words, we need
      permission to at least read the next field of a removed node.
      As curr is not reachable from the head, it is not part of [llist], and by
      extension not captured by [phys_list_aux], which means that we will need
      to add a bit more bookkeeping.

      Thus, we keep track of all nodes that have ever been allocated using
      [nodes]. In particular, the monotonic set (i.e. a set to which we can only
      add nodes, never remove) [own γn (● (removed ∪ ll_locs ll ∪ {[hℓ; tℓ]}))]
      contains the locations of those nodes. This is also the reason we keep
      track of the locations in an instance of [llist].
      One can then interpret [own γn (◯ {[ℓ]})] as owning a certificate for
      "ℓ is a valid node".

      The sentinel tail and head nodes are described in [tail_node] and
      [phys_list].

      [removed_perm] contains the permissions for the removed nodes, while
      [phys_list_aux] contains the permissions for nodes that are reachable
      from the head. The sentinel values are special and their
      permissions are in the previously mentioned [tail_node] and [phys_list].
      Together with [nodes], we can achieve what we mentioned in the section
      "Modeling the Nodes", namely that once we read a node, we should always
      be able to access all of its contents. In particular, this is achieved
      by using the set invariant [set_inv], together with the persistent facts
      [ℓ ↦□ SOMEV (extZ#k, #ℓℓₙ, #ℓₘ, lk)] and [own γn (◯ {[ℓ]})].
      [get_is_lock] provides a more concrete example of this. (The persistent
      fact [own γt (to_agree tℓ)] in that lemma is mostly a technicality.) *)

  (** Representation of the linked list reachable from the head. *)
  Notation llist := (list (loc * bool * Z)).

  (** Returns the list of unmarked nodes reachable from the head. *)
  Definition unmarked (ll : llist) : llist :=
    filter (λ x, negb ((snd ∘ fst) x)) ll.

  (** Returns the set of keys belonging to unmarked nodes. *)
  Definition ll_keys (ll : llist) : gset Z :=
    list_to_set (map snd (unmarked ll)).

  (** Returns the set of locations reachable from the head. *)
  Definition ll_locs (ll : list (loc * bool * Z)) : gset loc :=
    list_to_set (map (fst ∘ fst) ll).

  (** Keeps track of all nodes that have ever been allocated and their
      constraints. *)
  Definition nodes (hℓ : loc) (removed : gset loc) (ll : llist) (tℓ : loc) (γn : gname) : iProp :=
    (** Monotonic (ghost) set that keeps track of all nodes that have ever been
        allocated *)
    own γn (● (removed ∪ ll_locs ll ∪ {[hℓ; tℓ]})) ∗
    (** Sentinels, removed nodes, and nodes reachable from the set are all
       different *)
    ⌜ removed ## ll_locs ll ∧ removed ## {[tℓ]} ∧ ll_locs ll ## {[hℓ; tℓ]} ⌝ ∗
    (* Technicality that makes proofs a bit less painful. *)
     ⌜ hℓ ≠ tℓ ⌝.

  (** Locking a node gives us half the permission to the next field and marked
      field. If one acquires the other half from the invariant, one can use this
      to modify those fields. *)
  Definition lock_content (ℓₙ : loc) (ℓₘ : loc) : iProp :=
    ∃ (next : lopt) (mark : bool), ℓₙ ↦{#1/2} lopt#next ∗ ℓₘ ↦{#1/2} #mark.

  (** The tail node is a valid node, that has key positive infinity, will always
      point to null, and can never be logically deleted. *)
  Definition tail_node (tℓ : loc) (γn : gname) : iProp :=
    ∃ (tℓℓₙ tℓₘ : loc) (tlk : val) tlkn,
      own γn (◯ {[tℓ]}) ∗
      tℓ ↦□ SOMEV (extZ#PInf, #tℓℓₙ, #tℓₘ, tlk) ∗ tℓℓₙ ↦□ NONEV ∗
      tℓₘ ↦□ #false ∗ is_lock tlkn tlk (lock_content tℓℓₙ tℓₘ).

  (** ℓ represents ll physically as a linked list. The lower bound ensures that
      keys are strictly increasing, which gives us sortedness and
      no duplicates. *)
  Fixpoint phys_list_aux (lb : extZ) (ℓ : loc) (ll : llist) (tℓ : loc) (γn : gname) : iProp :=
    match ll with
    | [] => ⌜ ℓ = tℓ ⌝
    | (lℓ, lmark, lkey) :: ll =>
        (** [ℓ] matches the head of [ll] *)
        ∃ (key : Z) (ℓℓₙ ℓₘ : loc) (lk : val) lkn,
          ℓ ↦□ SOMEV (extZ#(Fin key), #ℓℓₙ, #ℓₘ, lk)
          ∗ ⌜ ℓ = lℓ ⌝ ∗ ⌜ key = lkey ∧ lt lb (Fin key) ⌝ ∗
          (∃ (nℓ : loc),
              (** [ℓ] points to a valid node that represents the tail of [ll] *)
              ℓℓₙ ↦{#1/2} lopt#(Some nℓ)
              ∗ phys_list_aux (Fin key) nℓ ll tℓ γn
              ∗ own γn (◯ {[nℓ]}))
          ∗ ℓₘ ↦{#1/2} #lmark
          (** In contrast to the treiber example, we have a lock. This means
              that [phys_list_aux] is not timeless. *)
          ∗ is_lock lkn lk (lock_content ℓℓₙ ℓₘ)
    end.

  (** Captures all nodes reachable from the head, including the head and tail
      sentinel values. *)
  Definition phys_list (hℓ : loc) (ll : llist) (tℓ : loc) (γn : gname) : iProp :=
    ∃ (hℓℓₙ hnℓ hℓₘ : loc) (hlk : val) hlkn,
      tail_node tℓ γn
      ∗ own γn (◯ {[hℓ]})
      ∗ hℓ ↦□ SOMEV (extZ#NInf, #hℓℓₙ, #hℓₘ, hlk)
      ∗ hℓℓₙ ↦{#1/2} lopt#(Some hnℓ)
      ∗ phys_list_aux NInf hnℓ ll tℓ γn
      ∗ own γn (◯ {[hnℓ]})
      ∗ hℓₘ ↦□ #false
      ∗ is_lock hlkn hlk (lock_content hℓℓₙ hℓₘ).

  (** Stores the permissions for removed nodes. *)
  Definition removed_perm (removed : gset loc) (γn : gname) : iProp :=
    [∗ set] ℓ ∈ removed,
      ∃ (key : Z) (ℓℓₙ ℓₘ : loc) (lk : val) lkn,
        (** We can only remove non-sentinel nodes *)
        ℓ ↦□ SOMEV (extZ#(Fin key), #ℓℓₙ, #ℓₘ, lk) ∗
        (∃ (nℓ nℓℓₙ nℓₘ: loc) (nk : extZ) (nlk : val),
            (** Removed nodes point to valid nodes that have a strictly larger
                key. This is important for walking the list. *)
           ℓℓₙ ↦{#1/2} lopt#(Some nℓ) ∗ own γn (◯ {[nℓ]}) ∗
           nℓ ↦□ SOMEV (extZ#nk, #nℓℓₙ, #nℓₘ, nlk) ∗ ⌜ lt (Fin key) nk⌝) ∗
        ℓₘ ↦□ #true ∗
        is_lock lkn lk (lock_content ℓℓₙ ℓₘ).

  (** Ties the invariant together: the set at hℓ can be described by some
      set of keys, some set of removed nodes, the list of nodes reachable from
      the head, and the tail. *)
  Definition set_inv (hℓ : loc) (γn : gname) (γc : gname) (γt : gname) : iProp :=
    ∃ (removed : gset loc) (ls : gset Z) (ll : llist) (tℓ : loc),
      nodes hℓ removed ll tℓ γn ∗ own γc (●E ls) ∗ own γt (to_agree tℓ) ∗
      ⌜ ll_keys ll = ls ⌝ ∗ phys_list hℓ ll tℓ γn ∗ removed_perm removed γn.

  (** The actual Iris invariant. *)
  Definition is_set (hℓ : loc) (γn : gname) (γc : gname) (γt : gname) : iProp :=
    inv N (set_inv hℓ γn γc γt).

  (** Allows us to make statements about the content of a set. Used in
      [add_spec], [remove_spec], and [contains_spec]. *)
  Definition set_content (γc : gname) (ls : gset Z) : iProp :=
    own γc (◯E ls).

  (** *** Helper lemmas *******************************************************)

  (** Before we are able to prove the specification for [add] and [remove],
      we will need quite a few helper lemmas about (parts) of our
      invariant.*)

  (** **** Ghost state ********************************************************)

  (** We will now provide some lemmas to interact with the ghost state. Recall
      that [●E xs] and [◯E ys] are used to represent the set's contents, while
      [● xs] and [◯ ys] are used to represent the set of allocated nodes. *)

  (** The following two lemmas have been borrowed from the POPL 18 Iris tutorial
      (see https://gitlab.mpi-sws.org/iris/tutorial-popl18). *)

  (** The view of the authority agrees with the local view. *)
  Lemma eauth_agree γ xs ys :
    own γ (●E xs) -∗ own γ (◯E ys) -∗ ⌜xs = ys⌝.
  Proof.
    iIntros "Hγ● Hγ◯".
    by iCombine "Hγ● Hγ◯"
         gives %[<-%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
  Qed.

  (** The view of the authority can be updated together with the local view. *)
  Lemma eauth_update γ ys xs1 xs2 :
    own γ (●E xs1) -∗ own γ (◯E xs2) ==∗
    own γ (●E ys) ∗ own γ (◯E ys).
  Proof.
    iIntros "Hγ● Hγ◯".
    iMod (own_update_2 _ _ _ (●E ys ⋅ ◯E ys)
           with "Hγ● Hγ◯") as "[$$]"; [|done].
    by apply auth_update, option_local_update, exclusive_local_update.
  Qed.

  (** We can always add someting to the monotonic set. *)
  Lemma auth_update γ xs ys :
    ⌜ xs ⊆ ys ⌝ -∗ own γ (● xs) ==∗ own γ (● ys).
  Proof.
    iIntros "%Hsub Hγ●".
    iMod (own_update _  _ (● ys) with "[$Hγ●]") as "Hγ●"; [|done].
    by eapply auth_update_auth, gset_local_update.
  Qed.

  (** With this lemma we can extract [◯ {[ℓ]}], i.e., the fact that ℓ is
      a valid node, provided that ℓ is in the set of allocated nodes. *)
  Lemma auth_frag (γ : gname) (xs : gset loc) (ys : gset loc) :
    xs ⊆ ys ->  own γ (● ys) ==∗ own γ (● ys) ∗ own γ (◯ xs).
  Proof.
    (* With help from Paolo G. Giarrusso on Mattermost - thanks! *)
    iIntros "%Hsub Hγ●".
    iMod (own_update _ _ (● ys ⋅ ◯ ys) with "Hγ●") as "Hγ".
    { by apply (auth_update_alloc ys ys ys), gset_local_update. }
    iDestruct (own_op with "Hγ") as "[Hγ● Hγ◯]".
    iDestruct (own_mono with "Hγ◯") as "Hγ◯".
    { by apply auth_frag_mono, gset_included. }
    by iFrame.
  Qed.

  (** *** lists, [ll_locs], [ll_keys], and [all_ll_keys] **********************)

  (** In this section we introduce a few lemmas that are in particular useful
      for rewriting our functions that connect [llist] with sets. *)

  Lemma cons_as_app : forall (A : Type) (x : A) (xs : list A),
      x :: xs = [x] ++ xs.
  Proof. intros. simpl. reflexivity. Qed.

  Lemma in_ll_locs_cons (ℓ ℓ' : loc) (b : bool) (k : Z) (ll : llist) :
    ℓ ∈ ll_locs ((ℓ', b, k) :: ll) -> ℓ = ℓ' ∨ ℓ ∈ ll_locs ll.
  Proof. set_solver. Qed.

  Lemma ll_locs_app (ll₁ ll₂ : llist) :
    ll_locs (ll₁ ++ ll₂) = ll_locs ll₁ ∪ ll_locs ll₂.
  Proof. rewrite /ll_locs. set_solver. Qed.

  Lemma ll_locs_singleton (ℓ : loc) (m : bool) (z : Z) :
    ll_locs [(ℓ, m, z)] = {[ℓ]}.
  Proof. rewrite /ll_locs. set_solver. Qed.

  Lemma ll_locs_com12 (ll₁ ll₂ ll₃: llist) :
    ll_locs (ll₁ ++ ll₂ ++ ll₃) = ll_locs (ll₂ ++ ll₁ ++ ll₃).
  Proof. rewrite !ll_locs_app. set_solver. Qed.

  Lemma ll_locs_add (ll llpre llsuf : llist) (eℓ : loc) (em : bool) (ekz : Z) :
    ll = llpre ++ llsuf ->
    ll_locs (llpre ++ (eℓ, em, ekz) :: llsuf) = (ll_locs ll ∪ {[ eℓ ]}).
  Proof.
    intros Hll.
    rewrite !cons_middle ll_locs_com12 ll_locs_app. rewrite <- Hll.
    rewrite {1}/ll_locs. simpl. by rewrite right_id_L union_comm_L.
  Qed.

  Lemma ll_keys_app (ll₁ ll₂ : llist) :
    ll_keys (ll₁ ++ ll₂) = ll_keys ll₁ ∪ ll_keys ll₂.
  Proof. rewrite /ll_keys /unmarked filter_app. set_solver. Qed.

  Lemma ll_keys_cons (ℓ : loc) (m : bool) (k : Z) (ll : llist) :
    ll_keys ((ℓ, m, k) :: ll) = ll_keys [(ℓ, m, k)] ∪ ll_keys ll.
  Proof. by rewrite cons_as_app ll_keys_app. Qed.

  Lemma ll_keys_com12 (ll₁ ll₂ ll₃: llist) :
    ll_keys (ll₁ ++ ll₂ ++ ll₃) = ll_keys (ll₂ ++ ll₁ ++ ll₃).
  Proof. rewrite !ll_keys_app. set_solver. Qed.

  Lemma ll_keys_singleton (ℓ : loc) (m : bool) (z : Z) :
    ll_keys [(ℓ, m, z)] = if m then ∅ else {[z]}.
  Proof. destruct m; rewrite /ll_keys; set_solver. Qed.

  Lemma ll_keys_remove (ls : gset Z) (llpre llsuf : llist) (ℓ : loc) (k : Z) :
    ll_keys (llpre ++ (ℓ, true, k) :: llsuf) = ls
    -> ll_keys (llpre ++ llsuf) = ls.
  Proof. rewrite !cons_middle !ll_keys_app. set_solver. Qed.

  Lemma ll_keys_mark (ℓ : loc) (ls : gset Z) (llpre llsuf : llist) (m : bool) (k : Z) :
    k ∉ ll_keys llpre -> k ∉ ll_keys llsuf
    -> ll_keys (llpre ++ (ℓ, m, k) :: llsuf) = ls
    -> ll_keys (llpre ++ (ℓ, true, k) :: llsuf) = ls ∖ {[k]}.
  Proof.
    intros Hninp Hnins.
    rewrite !cons_middle !ll_keys_app !ll_keys_singleton.
    destruct m; set_solver.
  Qed.

  (** Returns the set of all keys, including those that have been marked. *)
  Definition all_ll_keys (ll : llist) : gset Z :=
    list_to_set (map snd ll).

  Lemma in_all_ll_keys_cons (ℓ : loc) (b : bool) (k k' : Z) (ll : llist) :
    k ∈ all_ll_keys ((ℓ, b, k') :: ll) -> k = k' ∨ k ∈ all_ll_keys ll.
  Proof. set_solver. Qed.

  Lemma all_ll_keys_cons (ℓ : loc) (b : bool) (k : Z) (ll : llist) :
    all_ll_keys ((ℓ, b, k) :: ll) = all_ll_keys [(ℓ, b, k)] ∪ all_ll_keys ll.
  Proof.  rewrite /all_ll_keys. set_solver. Qed.

  Lemma ll_keys_subset (ll : llist) :
    ll_keys ll ⊆ all_ll_keys ll.
  Proof.
    induction ll as [|[[ℓ' b'] k'] ll']; first done.
    rewrite ll_keys_cons all_ll_keys_cons ll_keys_singleton /all_ll_keys.
    destruct b'; set_solver.
  Qed.

  (** *** Invariant ***********************************************************)

  (** We will now prove lemmas that make use of the invariant in some way.
      Since the proofs mostly consist of basic case distinctions and
      destructing + reassembling the invariant, we will not extensively comment
      on them. *)

  (** A brief note on the usage of iExists: Occasionally, iFrame struggles
      to correctly instantiate existentials. In those cases, we manually use
      iExists to help it out. *)

  (** Extracts the facts about the head and tail from the invariant. *)
  Lemma initial_facts (hℓ : loc) (γn γc γt : gname) :
    is_set hℓ γn γc γt
    ={↑N}=∗ ▷ (∃ (hℓℓₙ hℓₘ : loc) (hlk : val),
                  hℓ ↦□ SOMEV (extZ#NInf, #hℓℓₙ, #hℓₘ, hlk) ∗
                  ∃ (tℓ tℓℓₙ tℓₘ : loc) (tlk : val),
                    own γt (to_agree tℓ) ∗
                    ⌜ hℓ ≠ tℓ ⌝ ∗
                    tℓ ↦□ SOMEV (extZ#PInf, #tℓℓₙ, #tℓₘ, tlk) ∗
                    tail_node tℓ γn ∗
                    own γn (◯{[hℓ]})).
  Proof.
    iIntros "HIset".
    iInv "HIset" as "Hset" "Hclose".
    iDestruct "Hset" as
      (removed ls ll tℓ) "(Hnodes & Hγc● & #Hγt & Hlogi & Hphys & Hremp)".
    iDestruct "Hphys" as
      (hℓℓₙ hnℓ hℓₘ hlk hlkn)
        "(Ht & #H◯hℓ & #Hhℓ & Hhℓℓₙ & Hhnphys & H◯hnℓ & Hhℓₘ & Hhlk)".
    iDestruct "Hnodes" as "(H●γn & Hdisj & #Hneq)".
    iDestruct "Ht" as
      (tℓℓₙ tℓₘ tlk tlkn) "(#H◯tℓ & #Htℓ & #Htℓℓₙ & #Htℓₘ & #Hislk)".
    iFrame "Hhℓ Hγt Hneq Htℓ H◯hℓ H◯tℓ Htℓℓₙ Htℓₘ Hislk".
    iMod ("Hclose" with "[-]") as "_"; [|done].
    iFrame "H●γn Hdisj Hneq Hγc● Hγt Hlogi Hremp".
    (* Use iExists to help iFrame out *)
    iExists hℓℓₙ, hnℓ, hℓₘ, hlk, hlkn.
    iFrame "H◯tℓ Htℓ Htℓℓₙ Htℓₘ Hislk H◯hℓ Hhℓ Hhℓℓₙ Hhnphys H◯hnℓ Hhℓₘ
            Hhlk".
  Qed.

  (** A valid node is either a sentinel node, removed, or reachable from the
      head (i.e., [ℓ ∈ ll_locs ll]). *)
  Lemma node_cases (hℓ ℓ tℓ: loc) (ll : llist) (removed : gset loc) (γn : gname) :
    own γn (◯ {[ℓ]}) -∗ nodes hℓ removed ll tℓ γn -∗
     ⌜ ℓ = hℓ ∨ ℓ ∈ removed ∨ ℓ ∈ ll_locs ll ∨ ℓ = tℓ ⌝.
  Proof.
    iIntros "H◯ℓ Hnodes".
    iDestruct "Hnodes" as "[Hγn● Hdisj]".
    iCombine "Hγn● H◯ℓ"
      gives %[Hsub%gset_included _]%auth_both_valid_discrete.
    rewrite singleton_subseteq_l !elem_of_union in Hsub.
    rewrite !elem_of_singleton in Hsub. intuition.
  Qed.

  (** If a node is reachable from the head, we can access it successor,
      which is also a valid node that has a strictly larger key. *)
  Lemma phys_list_aux_node_perm (ℓ' ℓ ℓℓₙ ℓₘ tℓ : loc) (ll : llist) (lb k : extZ) (lk : val) (γn γt : gname) :
    ℓ ∈ ll_locs ll
    (** [phys_list_aux] is acquired by opening and destructing the invariant. *)
    -> phys_list_aux lb ℓ' ll tℓ γn
    -∗ own γt (to_agree tℓ)
    -∗ tail_node tℓ γn
    -∗ ℓ ↦□ SOMEV (extZ#k, #ℓℓₙ, #ℓₘ, lk)
    -∗ (∃ (nℓ nℓℓₙ nℓₘ : loc) (nk : extZ) (nlk : val),
          own γn (◯{[nℓ]}) ∗
          nℓ ↦□ SOMEV (extZ#nk, #nℓℓₙ, #nℓₘ, nlk) ∗
          ⌜ lt k nk ⌝ ∗
          ℓℓₙ ↦{#1/2} SOMEV #nℓ ∗
          (** Returning the permission restores [phys_list_aux], which is
              required to restore the invariant. *)
          (ℓℓₙ ↦{#1/2} SOMEV #nℓ -∗ phys_list_aux lb ℓ' ll tℓ γn)).
  Proof.
    iIntros (Hin) "Hphys Hγt Ht Hℓ".
    iInduction ll as [|[[ℓ'' b'] k'] ll'] "IH" forall (lb ℓ'); first done.
    iDestruct "Hphys" as
      (k'' ℓℓₙ' ℓₘ' lk' lkn)
        "(Hℓ' & <- & [-> %Hlt] & (%nℓ' & Hℓℓₙ' & Hnphys' & #H◯nℓ') & Hℓₘ' & #Hlk')".
    apply in_ll_locs_cons in Hin as [<- | Hin].
    - iCombine "Hℓ' Hℓ" gives "[_ %Hheq]". inversion Hheq as [Hk].
      subst. clear Hheq.
      apply extZ_inv_fin in Hk as ->.
      destruct ll'.
      + iDestruct "Hnphys'" as "->".
        iDestruct "Ht" as
          (tℓℓₙ tℓₘ tlk tlkn) "(H◯tℓ & Htℓ & Htℓℓₙ & Htℓₘ & Htlk)".
        iFrame "∗ #".
        iSplit; first done.
        iIntros "Hℓℓₙ".
        by iFrame "∗ #".
      + repeat destruct p.
        iDestruct "Hnphys'" as
          (nk' nℓℓₙ' nℓₘ' nlk' nlkn')
          "(#Hnℓ' & <- & [<- %Hltnk'] & (%nnℓ & Hnℓℓₙ' & Hnnphys & H◯nnℓ) &
            Hnℓₘ' & Hnlk')".
        iFrame "H◯nℓ' Hnℓ' Hℓℓₙ'".
        iSplit; first done.
        iIntros "Hℓℓₙ".
        by iFrame "∗ #".
    - iPoseProof ("IH" with "[] [$Hnphys'] Hγt Ht [$Hℓ]") as
        (nℓ nℓℓₙ nℓₘ nk nlk) "(H◯nℓ & Hnℓ & Hltnk & Hℓℓₙ & Hwd)"; first done.
      iFrame "H◯nℓ Hnℓ Hltnk Hℓℓₙ".
      iIntros "Hℓℓₙ".
      iPoseProof ("Hwd" with "Hℓℓₙ") as "Hnphys'".
      by iFrame "Hℓ' Hℓℓₙ' Hnphys' Hlk' Hℓₘ' H◯nℓ'".
  Qed.

  (** Similar to [phys_list_aux_node_perm], but uses [phys_list] instead of
      [phys_list_aux], which makes it easier to use in some situations. *)
  Lemma phys_list_node_perm (hℓ ℓ ℓℓₙ ℓₘ tℓ : loc) (ll : llist) (k : extZ) (lk : val) (γn γt : gname) :
    ℓ ∈ ll_locs ll
    -> phys_list hℓ ll tℓ γn
    -∗ own γt (to_agree tℓ)
    -∗ ℓ ↦□ SOMEV (extZ#k, #ℓℓₙ, #ℓₘ, lk)
    -∗ (∃ (nℓ nℓℓₙ nℓₘ : loc) (nk : extZ) (nlk : val),
          own γn (◯{[nℓ]}) ∗
          nℓ ↦□ SOMEV (extZ#nk, #nℓℓₙ, #nℓₘ, nlk) ∗
          ⌜ lt k nk ⌝ ∗
          ℓℓₙ ↦{#1/2} SOMEV #nℓ ∗
          (ℓℓₙ ↦{#1/2} SOMEV #nℓ -∗ phys_list hℓ ll tℓ γn)).
  Proof.
    iIntros (Hll) "Hphys #Hγt #Hℓ".
    iDestruct "Hphys" as
      (hℓℓₙ hnℓ hℓₘ hlk hlkn)
      "(#Ht & #H◯hℓ &#Hhℓ & Hhℓℓₙ & Hhnphys & #H◯hℓₙ & #Hhℓₘ & #Hhlk)".
    iPoseProof
      (phys_list_aux_node_perm _ _ _ _ _ _ _ _ _ _ _ Hll
        with "Hhnphys Hγt Ht Hℓ") as
      (nℓ nℓℓₙ nℓₘ nk nlk) "(#H◯nℓ & #Hnℓ & %Hltnk & Hℓℓₙ & Hwd)".
    iFrame "H◯nℓ Hnℓ Hℓℓₙ". iSplit; first done.
    iIntros "Hℓℓₙ".
    iPoseProof ("Hwd" with "Hℓℓₙ") as "Hhnphys".
    (* Use iExists to help iFrame out *)
    iExists hℓℓₙ, hnℓ, hℓₘ, hlk, hlkn.
    iFrame "Ht H◯hℓ Hhℓ Hhℓℓₙ Hhnphys H◯hℓₙ Hhℓₘ Hhlk".
  Qed.

  (** For every node that is not the tail, we can access it successor,
      which is also a valid node that has a strictly larger key. *)
  Lemma next_node (hℓ ℓ ℓℓₙ ℓₘ tℓ : loc) (k : extZ) (lk : val) (γn γc γt : gname) :
    set_inv hℓ γn γc γt
    -∗ own γn (◯{[ℓ]})
    -∗ ℓ ↦□ SOMEV (extZ#k, #ℓℓₙ, #ℓₘ, lk)
    -∗ own γt (to_agree tℓ)
    -∗ ⌜ ℓ ≠ tℓ ⌝
    -∗ (∃ (nℓ nℓℓₙ nℓₘ : loc) (nk : extZ) (nlk : val),
          ℓℓₙ ↦{#1/2} SOMEV #nℓ ∗
          own γn (◯{[nℓ]}) ∗
          nℓ ↦□ SOMEV (extZ#nk, #nℓℓₙ, #nℓₘ, nlk) ∗
          ⌜ lt k nk ⌝ ∗
          (ℓℓₙ ↦{#1/2} SOMEV #nℓ -∗ set_inv hℓ γn γc γt)).
  Proof.
    iIntros "Hset #H◯ℓ #Hℓ #Hγt %Hneq".
    iDestruct "Hset" as
      (removed ls ll tℓ') "(Hnodes & Hγc● & Hγt' & Hllk & Hphys & Hremp)".
    (* We do not push Hllk into pure context, is so that subst doesn't use it *)
    iCombine "Hγt Hγt'" gives %<-%to_agree_op_valid_L; iClear "Hγt'".
    iPoseProof (node_cases with "H◯ℓ Hnodes") as "%Hcases".
    destruct Hcases as [-> | [Hrem | [Hll | Htl]]].
    - (* Current: Head *)
      iDestruct "Hphys" as
        (hℓℓₙ hℓₙ hℓₘ hlk hlkn)
        "(#Ht & H◯hℓ & #Hhℓ & Hhℓℓₙ & Hhnphys & #H◯hℓₙ & #Hhℓₘ & #Hhlk)".
      iCombine "Hℓ Hhℓ" gives "[_ %Hheq]".
      inversion Hheq as [Hk]. subst. clear Hheq.
      destruct ll.
      + iDestruct "Hhnphys" as "->".
        iDestruct "Ht" as
          (tℓℓₙ tℓₘ tlk tlkn) "(H◯tℓ & Htℓ & Htℓℓₙ & Htℓₘ & Htlk)".
        iFrame "H◯hℓₙ Htℓ Hhℓℓₙ". iSplit.
        * iPureIntro. symmetry in Hk. apply extZ_inv_ninf in Hk. by rewrite Hk.
        * iIntros "Hhℓℓₙ".
          iFrame "Hnodes Hγc● Hγt Hllk Hremp".
          (* Use iExists to help iFrame out *)
          iExists hℓℓₙ, tℓ, hℓₘ, hlk, hlkn.
          by iFrame "Htℓ Htℓℓₙ Htℓₘ Htlk H◯hℓ Hhℓ Hhℓℓₙ H◯hℓₙ Hhℓₘ Hhlk".
      + repeat destruct p.
        iDestruct "Hhnphys" as
          (hnk hnℓℓₙ hnℓₘ hnlk hnlkn)
            "(#Hhℓₙ & <- & [<- Hlthnk] & (%hnnℓ & Hhnℓℓₙ & Hhnnphys & H◯hnnℓ) & Hhnℓₘ & Hhnlk)".
        iFrame "H◯hℓₙ Hhℓₙ Hhℓℓₙ". iSplit.
        * symmetry in Hk. apply extZ_inv_ninf in Hk. by rewrite Hk.
        * iIntros "Hhℓℓₙ".
          iFrame "Hnodes Hγc● Hγt Hllk Hremp".
          (* Use iExists to help iFrame out *)
          iExists hℓℓₙ, hℓₙ, hℓₘ, hlk, hlkn.
          iFrame "Ht H◯hℓ Hhℓ Hhℓℓₙ Hhℓₘ". iSplit.
          -- by iFrame "Hhℓₙ Hhnℓℓₙ Hhnnphys H◯hnnℓ Hhnlk Hhnℓₘ".
          -- iFrame "H◯hℓₙ Hhlk".
    - (* Current: removed *)
      iPoseProof (big_sepS_elem_of_acc _ _ _ Hrem  with "Hremp")
        as "[Hperm Hwand]".
      iDestruct "Hperm" as (key ℓℓₙ' ℓₘ' lk' lkn) "(Hℓ' & Hnℓ & Hℓₘ & #Hlk)".
      iCombine "Hℓ' Hℓ" gives "[_ %Heq]".
      inversion Heq as [Hk]. subst. clear Heq.
      iDestruct "Hnℓ" as (nℓ nℓℓₙ nℓₘ nk nlk) "(Hℓℓₙ & #H◯nℓ & #Hnℓ & %Hlt)".
      iFrame "H◯nℓ Hnℓ Hℓℓₙ". iSplit.
      + apply extZ_inv_fin in Hk. by rewrite Hk.
      + iIntros "Hℓℓₙ".
        iPoseProof ("Hwand" with "[Hℓ' Hℓₘ Hℓℓₙ H◯nℓ Hnℓ]") as "Hremp".
        { by iFrame "Hlk Hℓ' Hℓₘ H◯nℓ Hnℓ ∗". }
        iFrame "Hnodes Hγc● Hγt Hllk Hremp Hphys".
    - (* Current: in phys_list *)
      iDestruct (phys_list_node_perm _ _ _ _ _ _ _ _ _ _ Hll with "Hphys Hγt Hℓ")
        as (nℓ nℓℓₙ nℓₘ nk nlk) "(#H◯nℓ & #Hnℓ & %Hltnk & Hℓℓₙ & Hwd)".
      iFrame "∗ #". iSplit; first done.
      iIntros "Hℓℓₙ".
      iDestruct ("Hwd" with "Hℓℓₙ") as "Hphys".
      iFrame "Hnodes Hγc● Hγt Hllk Hremp Hphys".
    - (* tail does not have a next node *)
      done.
  Qed.

  (** All nodes except the tail point to some other node, i.e., they do not
      point to null. *)
  Lemma not_tail_has_next (hℓ ℓ ℓℓₙ ℓₘ tℓ : loc) (nℓo : lopt) (k : extZ) (lk : val) (γn γc γt : gname) :
    is_set hℓ γn γc γt
    -∗ own γt (to_agree tℓ)
    -∗ own γn (◯{[ℓ]})
    -∗ ℓ ↦□ SOMEV (extZ#k, #ℓℓₙ, #ℓₘ, lk)
    -∗ ⌜ ℓ ≠ tℓ ⌝
    -∗ ℓℓₙ ↦{#1 / 2} lopt#nℓo
    ={↑N}=∗ ∃ (nℓ : loc), ℓℓₙ ↦{#1 / 2} lopt#(Some nℓ).
  Proof.
    iIntros "HIset Hγt H◯ℓ Hℓ %Hneq Hℓℓₙ".
    iInv "HIset" as "Hset" "Hclose".
    iDestruct (next_node with "Hset [H◯ℓ //] [Hℓ //] [Hγt //] [//]") as
      (nℓ nℓℓₙ nℓₘ nk nlk) "(>Hℓℓₙ' & >#H◯nℓ & >#Hnℓ & >%Hlt & Hwd)".
    iDestruct (pointsto_agree with "Hℓℓₙ Hℓℓₙ'") as "->".
    iDestruct ("Hwd" with "[Hℓℓₙ' //]") as "HIset".
    iMod ("Hclose" with "[$]") as "_". eauto.
  Qed.

  (** Nodes reachable from the head contain half the permission to the next and
      marked field in a lock. *)
  Lemma phys_list_aux_lock (ℓ ℓ' ℓℓₙ ℓₘ tℓ : loc) (ll : llist) (lb k : extZ) (lk : val) (γn : gname) :
    ℓ ∈ ll_locs ll
    -> phys_list_aux lb ℓ' ll tℓ γn
    -∗ ℓ ↦□ SOMEV (extZ#k, #ℓℓₙ, #ℓₘ, lk)
    -∗ (phys_list_aux lb ℓ' ll tℓ γn ∗
        (∃ (lkn : lock_name),
            is_lock lkn lk (lock_content ℓℓₙ ℓₘ))).
  Proof.
    iIntros (Hin) "Hphys Hℓ".
    iInduction ll as [|[[ℓ'' b'] k'] ll'] "IH" forall (lb ℓ'); first done.
    simpl.
    iDestruct "Hphys" as
      (k'' ℓℓₙ' ℓₘ' lk' lkn)
        "(Hℓ' & <- & [-> %Hlt] & (%nℓ & Hℓℓₙ & Hnphys & #H◯nℓ) & Hℓₘ' & Hlkn)".
    apply in_ll_locs_cons in Hin as [<- | Hin].
    - iCombine "Hℓ' Hℓ" gives "[_ %Hheq]".
      inversion Hheq as [Hk]. subst. clear Hheq.
      iClear "Hℓ'". iSplit.
      + apply extZ_inv_fin in Hk as ->.
        (* Use iExists to help iFrame out *)
        iExists k', ℓℓₙ, ℓₘ, lk, lkn.
        iFrame "Hℓ Hℓₘ' H◯nℓ Hℓℓₙ". repeat iSplit; try done.
      + eauto.
    - iPoseProof ("IH" with "[] [$Hnphys] [$Hℓ]") as "[Hnphys [%lkn' Hlkn']]";
        first done.
      iSplit.
      + by iFrame "Hℓ' Hℓℓₙ Hnphys H◯nℓ Hℓₘ' Hlkn".
      + eauto.
  Qed.

  (** Similar to [phys_list_aux_lock], but uses [phys_list] instead of
      [phys_list_aux], which makes it easier to use in some situations. *)
  Lemma phys_list_lock (hℓ ℓ ℓℓₙ ℓₘ tℓ : loc) (ll : llist) (k : extZ) (lk : val) (γn : gname) :
    ℓ ∈ ll_locs ll
    -> phys_list hℓ ll tℓ γn
    -∗ ℓ ↦□ SOMEV (extZ#k, #ℓℓₙ, #ℓₘ, lk)
    -∗ (phys_list hℓ ll tℓ γn ∗
        (∃ (lkn : lock_name),
           is_lock lkn lk (lock_content ℓℓₙ ℓₘ))).
  Proof.
    iIntros (Hin) "Hphys Hℓ".
    destruct ll; first done.
    iDestruct "Hphys" as
      (hℓℓₙ hℓₙ hℓₘ hlk hlkn)
      "(#Ht & H◯hℓ &#Hhℓ & Hhℓℓₙ & Hhnphys & #H◯hℓₙ & #Hhℓₘ & #Hhlk)".
    iPoseProof
      (phys_list_aux_lock _ _ _ _ _ _ _ _ _ _ Hin
        with "Hhnphys Hℓ") as "[Hhnphys [%ℓlkn Hℓlk]]".
    iSplit.
    - iFrame "Ht Hhℓ Hhℓℓₙ Hhnphys H◯hℓₙ Hhℓₘ Hhlk H◯hℓ".
    - eauto.
  Qed.

  (** Every node contains half the permission to the next and marked field
      in a lock. *)
  Lemma get_is_lock (hℓ ℓ ℓℓₙ ℓₘ tℓ: loc) (k : extZ) (lk : val) (γn γc γt : gname):
    is_set hℓ γn γc γt
    -∗ own γt (to_agree tℓ)
    -∗ own γn (◯{[ℓ]})
    -∗ ℓ ↦□ SOMEV (extZ#k, #ℓℓₙ, #ℓₘ, lk)
    ={↑N}=∗ ▷ (∃ (lkn : lock_name),
                      is_lock lkn lk (lock_content ℓℓₙ ℓₘ)).
  Proof.
    iIntros "HIset Hγt H◯ℓ Hℓ".
    iInv "HIset" as "Hset" "Hclose".
    iDestruct "Hset" as
      (removed ls ll tℓ') "(>Hnodes & >Hγc● & >Hγt' & >Hllk & Hphys & Hremp)".
    iCombine "Hγt Hγt'" gives %<-%to_agree_op_valid_L; iClear "Hγt'".
    iPoseProof (node_cases with "H◯ℓ Hnodes") as "%Hcases".
    destruct Hcases as [-> | [Hrem | [Hll | ->]]].
    - iDestruct "Hphys" as
        (hℓℓₙ hnℓ hℓₘ hlk hlkn)
        "(Ht & #H◯hℓ & >#Hhℓ & Hhℓℓₙ & Hhnphys & H◯hnℓ & Hhℓₘ & #Hhlk)".
      iCombine "Hℓ Hhℓ" gives "[_ %Hheq]". inversion Hheq. subst. clear Hheq.
      iFrame "Hhlk".
      iMod ("Hclose" with "[-]") as "_"; [|done].
      iFrame "Hnodes Hγc● Hγt Hllk Hremp Ht Hhℓ Hhℓℓₙ Hhnphys H◯hnℓ H◯hℓ Hhℓₘ
              Hhlk".
    - iPoseProof (big_sepS_elem_of_acc _ _ _ Hrem  with "Hremp")
        as "[Hperm Hwand]".
      iDestruct "Hperm" as (key ℓℓₙ' ℓₘ' lk' lkn) "(>Hℓ' & Hℓₙ & Hℓₘ & #Hlk)".
      iCombine "Hℓ' Hℓ" gives "[_ %Heq]". inversion Heq. subst. clear Heq.
      iPoseProof ("Hwand" with "[$]") as "Hremp"; first iFrame "Hlk".
      by iMod ("Hclose" with "[$]") as "_".
    - iPoseProof (phys_list_lock _ _ _ _ _ _ _ _ _ Hll with "Hphys [>Hℓ //]") as
        "[Hphys [%lkn Hlk]]".
      iFrame "Hlk".
      by iMod ("Hclose" with "[$]") as "_".
    - iDestruct "Hphys" as
        (hℓℓₙ hnℓ hℓₘ hlk hlkn)
        "(Ht & #H◯hℓ & >#Hhℓ & Hhℓℓₙ & Hhnphys & H◯hnℓ & Hhℓₘ & #Hhlk)".
      iDestruct "Ht" as
        (tℓℓₙ tℓₘ tlk tlkn) "(H◯tℓ & >Htℓ & Htℓℓₙ & Htℓₘ & #Htlk)".
      iCombine "Hℓ Htℓ" gives "[_ %Hteq]". inversion Hteq. subst. clear Hteq.
      iFrame "Htlk".
      iMod ("Hclose" with "[-]") as "_"; [|done].
      iFrame "Hnodes Hγc● Hγt Hllk Hremp".
      (* Use iExists to help iFrame out *)
      iExists hℓℓₙ, hnℓ, hℓₘ, hlk, hlkn.
      iFrame "H◯tℓ Htℓ Htℓℓₙ Htℓₘ Htlk
              Hhℓ Hhℓℓₙ Hhnphys H◯hnℓ H◯hℓ Hhℓₘ Hhlk".
  Qed.

  (** A rewriting lemma for [phys_list_aux] for the case when the [llist] is
      of the form [(l, m, k)::ll]. *)
  Lemma phys_list_aux_cons (lb : extZ) (ℓ tℓ : loc) (ll : llist) (l : loc) (m : bool) (k : Z) (γn : gname) :
    (∃ (key : Z) (ℓℓₙ ℓₘ : loc) (lk : val) (lkn : lock_name),
       ℓ ↦□ SOMEV (extZ#(Fin key), #ℓℓₙ, #ℓₘ, lk) ∗ ⌜ℓ = l⌝ ∗ ⌜key = k⌝ ∗
       ⌜lt lb (Fin key)⌝ ∗
       (∃ nℓ : loc,
          ℓℓₙ ↦{#1 / 2} lopt#(Some nℓ) ∗
          phys_list_aux (Fin key) nℓ ll tℓ γn ∗
          own γn (◯ {[nℓ]})) ∗ ℓₘ ↦{#1 / 2} #m ∗
       is_lock lkn lk (lock_content ℓℓₙ ℓₘ))%I ⊣⊢
    phys_list_aux lb ℓ ((l, m, k)::ll) tℓ γn.
  Proof.
    iSplit.
    - iIntros "(%kz & %ℓℓₙ & %ℓₘ & %lk & %lkn & Hℓ & Hℓeq & %Hkeq & %Hlt &
               (%nℓ & Hℓℓₙ & Hphys & Hγn◯) & Hℓₘ & Hislk)".
      (* Use iExists to help iFrame out *)
      iExists kz, ℓℓₙ, ℓₘ, lk, lkn.
      iFrame "Hℓ". repeat iSplit; try done.
      iSplitR "Hℓₘ Hislk"; iFrame.
    - iIntros "(%kz & %ℓℓₙ & %ℓₘ & %lk & %lkn & Hℓ & %Hℓeq & [%Hkeq %Hlt] &
               (%nℓ & Hℓℓₙ & Hphys & Hγn◯) & Hℓₘ & Hislk)".
      (* Use iExists to help iFrame out *)
      iExists kz, ℓℓₙ, ℓₘ, lk, lkn.
      iFrame "Hℓ". repeat iSplit; try done.
      iSplitR "Hℓₘ Hislk"; iFrame.
  Qed.

  (** If a node is reachable from the head and is unmarked, then its key is
      in [ll_keys]. *)
  Lemma unmarked_fin_in_ll_locs_keys (ℓ' ℓ ℓℓₙ ℓₘ tℓ : loc) (lk : val) (lb : extZ) (kz : Z) (ll : llist) (γn : gname) :
    ⌜ ℓ ∈ ll_locs ll ⌝
    -∗ ℓ ↦□ SOMEV (extZ#(Fin kz), #ℓℓₙ, #ℓₘ, lk)
    -∗ ℓₘ ↦{#1/2} #false
    -∗ phys_list_aux lb ℓ' ll tℓ γn
    -∗ ⌜ kz ∈ ll_keys ll⌝.
  Proof.
    iIntros "%Hin #Hℓ Hℓₘ Hphys".
    iInduction ll as [|[[ℓ'' b'] k'] ll'] "IH" forall (lb ℓ'); first done.
    iDestruct "Hphys" as
      (k'' ℓℓₙ' ℓₘ' lk' lkn)
        "(Hℓ' & <- & [-> %Hlt] & (%nℓ' & Hℓℓₙ' & Hnphys' & #H◯nℓ') & Hℓₘ' & #Hlk')".
    apply in_ll_locs_cons in Hin as [<- | Hin].
    - iCombine "Hℓ' Hℓ" gives "[_ %Heq]". inversion Heq.
      iCombine "Hℓₘ' Hℓₘ" gives "[_ %Hmeq]". inversion Hmeq. iPureIntro.
      rewrite /ll_keys /unmarked. set_solver.
    - iDestruct ("IH" with "[//] Hℓₘ Hnphys'") as "%Hin'". iPureIntro.
      rewrite ll_keys_cons. set_solver.
  Qed.

  (** Any unmarked node that is not a sentinel node has its location in
      [ll_locs] and its key in [ll_keys]. *)
  Lemma unmarked_fin_in_ll_sets (hℓ ℓ ℓℓₙ ℓₘ tℓ : loc) (kz : Z) (removed : gset loc) (ll : llist) (lk : val) (γn : gname) :
    own γn (◯ {[ℓ]})
    (** Note that we require the key to be a finite integer, which excludes
        sentinel nodes. *)
    -∗ ℓ ↦□ SOMEV (extZ#(Fin kz), #ℓℓₙ, #ℓₘ, lk)
    -∗ ℓₘ ↦{#1/2} #false
    (** Parts of the invariant relevant for the proof. *)
    -∗ nodes hℓ removed ll tℓ γn
    -∗ phys_list hℓ ll tℓ γn
    -∗ removed_perm removed γn
    -∗ (** We manually frame here even though the conclusion is pure. This is
           because [phys_list hℓ ll tℓ γn] may be under a later that cannot be
           eliminated, resulting in the conclusion being under a later too.
           Trying to destruct the result then does not let us keep the
           hypotheses around. *)
       ℓₘ ↦{#1/2} #false ∗ nodes hℓ removed ll tℓ γn ∗
       phys_list hℓ ll tℓ γn ∗ removed_perm removed γn ∗
       (** The "actual" conclusion. *)
       ⌜ kz ∈ ll_keys ll ⌝ ∗ ⌜ ℓ ∈ ll_locs ll ⌝.
  Proof.
    iIntros "#H◯ℓ #Hℓ Hℓₘ Hnodes Hphys Hremp".
    iDestruct (node_cases with "H◯ℓ Hnodes") as "%Hcases".
    destruct Hcases as [-> | [Hrem | [Hll | ->]]].
    - (* Contradiction: head has negative infinity as key *)
      iDestruct "Hphys" as (hℓℓₙ hnℓ hℓₘ hlk hlkn) "(_ & _ & #Hhℓ & _)".
      iCombine "Hhℓ Hℓ" gives "[_ %Heq]". inversion Heq.
    - (* Contradiction: node ℓ is not removed/marked *)
      iPoseProof (big_sepS_elem_of_acc _ _ _ Hrem  with "Hremp")
        as "[Hperm Hwand]".
      iDestruct "Hperm" as (key ℓℓₙ' ℓₘ' lk' lkn) "(Hℓ' & _ & Hℓₘ' & _)".
      iCombine "Hℓ' Hℓ" gives "[_ %Heq]". inversion Heq.
      by iCombine "Hℓₘ' Hℓₘ" gives %[_ Hfalse].
    - (* ℓ is in the physical list *)
      iDestruct "Hphys" as (hℓℓₙ hnℓ hℓₘ hlk hlkn)
        "(Ht & H◯hℓ & Hhℓ & Hhℓℓₙ & Hphysa & H◯hnℓ & Hhℓₘ & Hislkh)".
      iDestruct
        (unmarked_fin_in_ll_locs_keys $! Hll with "Hℓ Hℓₘ Hphysa") as "%Hin".
      by iFrame "Hℓₘ Hnodes Hremp Ht ∗".
    - (* Contradiction: tail has positive infinity as key *)
      iDestruct "Hphys" as (hℓℓₙ hnℓ hℓₘ hlk hlkn) "[Ht _]".
      iDestruct "Ht" as (tℓℓₙ tℓₘ tlk tlkn) "(_ & Htℓ & _)".
      iCombine "Htℓ Hℓ" gives "[_ %Heq]". inversion Heq.
  Qed.

  (** An unmarked node is either a sentinel node, or reachable from the head. *)
  Lemma unmarked_cases (hℓ ℓ ℓℓₙ ℓₘ tℓ : loc) (ez : extZ) (removed : gset loc) (ll : llist) (lk : val) (γn : gname) :
    own γn (◯ {[ℓ]})
    -∗ ℓ ↦□ SOMEV (extZ#ez, #ℓℓₙ, #ℓₘ, lk)
    -∗ ℓₘ ↦{#1/2} #false
    -∗ nodes hℓ removed ll tℓ γn
    -∗ phys_list hℓ ll tℓ γn
    -∗ removed_perm removed γn
    -∗ (** Manually framing for the same reason in
           [unmarked_fin_in_ll_sets]. *)
       ℓₘ ↦{#1/2} #false ∗ nodes hℓ removed ll tℓ γn ∗
       phys_list hℓ ll tℓ γn ∗ removed_perm removed γn ∗
       (** The "actual" conclusion. *)
       ⌜ ℓ = hℓ ∨ ℓ ∈ ll_locs ll ∨ ℓ = tℓ ⌝.
  Proof.
    iIntros "#H◯ℓ #Hℓ Hℓₘ Hnodes Hphys Hremp".
    iDestruct (node_cases with "H◯ℓ Hnodes") as "%Hcases".
    destruct Hcases as [-> | [Hrem | [Hll | ->]]].
    - iFrame "Hℓₘ Hnodes Hphys Hremp". by iLeft.
    - (* Contradiction: node ℓ is not removed/marked *)
      iPoseProof (big_sepS_elem_of_acc _ _ _ Hrem  with "Hremp")
        as "[Hperm Hwand]".
      iDestruct "Hperm" as (key ℓℓₙ' ℓₘ' lk' lkn) "(Hℓ' & _ & Hℓₘ' & _)".
      iCombine "Hℓ' Hℓ" gives "[_ %Heq]". inversion Heq.
      by iCombine "Hℓₘ' Hℓₘ" gives %[_ Hfalse].
    - iFrame "Hℓₘ Hnodes Hphys Hremp". iRight. by iLeft.
    - iFrame "Hℓₘ Hnodes Hphys Hremp". iRight. by iRight.
  Qed.

  (** If a node is reachable from the head, it has a finite integer as a key,
      whose value is in [all_ll_keys]. *)
  Lemma in_locs_in_keys (ℓ' ℓ ℓℓₙ ℓₘ tℓ : loc) (ll : llist) (lb ez : extZ) (lk : val) (γn : gname) :
    ℓ ↦□ SOMEV (extZ#ez, #ℓℓₙ, #ℓₘ, lk)
    -∗ ⌜ ℓ ∈ ll_locs ll ⌝
    -∗ phys_list_aux lb ℓ' ll tℓ γn
    -∗ ⌜ ∃ (z : Z), ez = Fin z ∧ z ∈ all_ll_keys ll ⌝.
  Proof.
    iIntros "Hℓ %Hin Hphys".
    iInduction ll as [|[[ℓ'' b'] k'] ll'] "IH" forall (lb ℓ'); first done.
    iDestruct (phys_list_aux_cons with "Hphys") as
      (k'' ℓℓₙ' ℓₘ' lk' lkn')
      "(#Hℓ' & <- & -> & %Hlt & (%nℓ & Hℓℓₙ & Hphysr & H◯nℓ) & Hℓₘ & Hislk)".
    pose proof (in_ll_locs_cons _ _ _ _ _ Hin) as [<- | Hin'].
    - iCombine "Hℓ' Hℓ" gives "[_ %Heq]".
      inversion Heq as [Hk]. subst. clear Heq.
      apply extZ_inv_fin in Hk as ->.
      iPureIntro. rewrite all_ll_keys_cons /all_ll_keys. set_solver.
    - iDestruct ("IH" $! Hin' _ _ with "Hℓ Hphysr") as "%Hinak".
      destruct Hinak as (z & -> & Hinak).
      iPureIntro. set_solver.
  Qed.

  (** We can always weaken the lower bound of [phys_list_aux]. *)
  Lemma weaken_lb (ℓ tℓ : loc) (lb lb' : extZ) (ll : llist) (γn : gname) :
    ⌜ lt lb' lb ⌝
    -∗ phys_list_aux lb ℓ ll tℓ γn
    -∗ phys_list_aux lb' ℓ ll tℓ γn.
  Proof.
    iIntros "%Hltlb Hphys".
    destruct ll; first done.
    repeat destruct p.
    iDestruct (phys_list_aux_cons with "Hphys") as
      (k ℓℓₙ ℓₘ lk lkn)
      "(Hℓ & %Hℓeq & %Hkeq & %Hlt & (%nℓ & Hℓℓₙ & Hphys & H◯nℓ) & Hℓₘ & Hislk)".
    iApply (phys_list_aux_cons lb' ℓ tℓ ll l b z γn).
    iFrame "Hℓₘ Hislk ∗". iPureIntro.
    repeat split; try done.
    by apply (lt_trans lb' lb _).
  Qed.

  (** We can update the lower bound to something strictly less than the key
      of the first node in [llsuf]. *)
  Lemma update_lb (ℓ ℓℓₙ ℓₘ tℓ : loc) (lk : val) (llsuf : llist) (lb : extZ) (ez' ez : extZ) (γn : gname) :
    ℓ ↦□ SOMEV (extZ#ez, #ℓℓₙ, #ℓₘ, lk)
    -∗ ⌜ lt ez' ez ⌝
    -∗ phys_list_aux lb ℓ llsuf tℓ γn
    -∗ phys_list_aux ez' ℓ llsuf tℓ γn.
  Proof.
    iIntros "Hℓ %Hlt Hphys".
    destruct llsuf; first done.
    repeat destruct p.
    iDestruct (phys_list_aux_cons with "Hphys") as
      (k ℓℓₙ' ℓₘ' lk' lkn)
      "(Hℓ' & %Hℓeq & %Hkeq & %Hlt' & (%nℓ & Hℓℓₙ & Hphys & H◯nℓ) & Hℓₘ & Hislk)".
    iCombine "Hℓ' Hℓ" gives "[_ %Heq]".
    inversion Heq as [Hk]. subst.
    iApply (phys_list_aux_cons ez' l tℓ llsuf l b z γn).
    iFrame "Hislk Hℓₘ # ∗". iPureIntro.
    repeat split; try done.
    apply extZ_inv_fin in Hk. by rewrite Hk in Hlt.
  Qed.

  (** All keys in [ll] are (strictly) greater than the lower bound. *)
  Lemma gt_lb (ℓ tℓ : loc) (ll : llist) (lb : extZ) (k : Z) (γn : gname) :
    ⌜ k ∈ all_ll_keys ll ⌝
    -∗ phys_list_aux lb ℓ ll tℓ γn
    -∗ ⌜ lt lb (Fin k) ⌝.
  Proof.
    iIntros "%Hin Hphys".
    iInduction ll as [|[[ℓ' b'] k'] ll'] "IH" forall (lb ℓ); first done.
    iDestruct (phys_list_aux_cons with "Hphys") as
        (k'' ℓℓₙ ℓₘ lk lkn)
          "(#Hℓ & <- & -> & %Hlt & (%nℓ & Hℓℓₙ & Hphysr & H◯nℓ) & Hℓₘ & Hislk)".
    apply in_all_ll_keys_cons in Hin as [<- | Hin]; first done.
    iDestruct (weaken_lb _ _ (Fin k') lb with "[//] Hphysr") as "Hphysr".
    iApply ("IH" with "[//] Hphysr").
  Qed.

  (** There are no duplicate keys. In particular, if we find a key at the head
      of an [llist], then it cannot occur in the suffix. *)
  Lemma key_nin_suf (ℓ ℓ' tℓ : loc) (llsuf : llist) (lb : extZ) (m : bool) (k : Z) (γn : gname) :
    phys_list_aux lb ℓ ((ℓ', m, k) :: llsuf) tℓ γn
    -∗ phys_list_aux lb ℓ ((ℓ', m, k) :: llsuf) tℓ γn ∗  (** Manual framing. *)
       ⌜ k ∉ ll_keys llsuf ⌝. (** The "actual" conclusion. *)
  Proof.
    (** This follows from [gt_lb], the fact that keys are strictly increasing
        in [llist]. *)
    iIntros "Hphys".
    iSplit.
    - iFrame.
    - iDestruct (phys_list_aux_cons with "Hphys") as
        (k' ℓℓₙ ℓₘ lk lkn)
          "(#Hℓ & <- & -> & %Hlt & (%nℓ & Hℓℓₙ & Hphysr & H◯nℓ) & Hℓₘ & Hislk)".
      iIntros "%Hin".
      iDestruct (gt_lb _ _ _ _ k with "[] Hphysr") as "%Hbad".
      { iPureIntro. eapply elem_of_weaken. apply Hin. apply ll_keys_subset. }
      rewrite /lt in Hbad. lia.
  Qed.

  (** Nodes are not duplicated in an [llist]. *)
  Lemma loc_nin_suf (ℓ ℓℓₙ ℓₘ ℓ' tℓ : loc) (nℓo : lopt) (llsuf : llist) (ek lb : extZ) (m : bool) (k : Z) (lk : val) (γt γn : gname) :
    (** The first two permissions correspond to have ℓ locked, which makes it
        easier to prove the statement. *)
    ℓ ↦□ InjRV (extZ#ek, #ℓℓₙ, #ℓₘ, lk)
    -∗ ℓℓₙ ↦{#1 / 2} lopt#nℓo
    -∗ own γt (to_agree tℓ)
    -∗ tail_node tℓ γn
    (** Note that this implictly enforces ℓ = ℓ', i.e., ℓ is at the head of the
        list. *)
    -∗ phys_list_aux lb ℓ ((ℓ', m, k) :: llsuf) tℓ γn
    -∗ (** Manual framing. *)
       (phys_list_aux lb ℓ ((ℓ', m, k) :: llsuf) tℓ γn ∗
        ℓℓₙ ↦{#1 / 2} lopt#nℓo) ∗
       (** The "actual" conclusion. *)
       ⌜ ℓ ∉ ll_locs llsuf ⌝.
  Proof.
    (** Since we assume that the node is locked, and know that ℓ is at the
        head of the list, we can collect the full permission to ℓℓₙ. If ℓ
        occurred again in the suffix, we would be able to get another half
        permission, resulting in 1.5 permission to ℓℓₙ, which is a
        contradiction.*)
    rewrite <- phys_list_aux_cons.
    iIntros "Hℓ Hℓℓₙ Hγt Ht
             (%key & %ℓℓₙ' & %ℓₘ' & %lk' & %lkn & Hℓ' & <- & <- & %Hlt &
               (%nℓ & Hℓℓₙ' & Hphysr & H◯nℓ) & Hℓₘ & Hislk)".
    iCombine "Hℓ' Hℓ" gives "[_ %Hheq]". inversion Hheq. subst.
    iSplit.
    - iFrame "Hℓℓₙ Hℓ Hℓₘ Hislk". repeat iSplit; try done. iFrame.
    - iIntros "%Hin".
      iDestruct (phys_list_aux_node_perm _ _ _ _ _ _ _ _ _ _ _ Hin
                  with "Hphysr Hγt Ht Hℓ'") as
        (nℓ' nℓℓₙ' nℓₘ' nk' nlk') "(_ & _ & _ & Hℓℓₙ'' & _)".
      iCombine "Hℓℓₙ Hℓℓₙ' Hℓℓₙ''" gives "[_ [%Hfrac _]]".
      by rewrite dfrac_op_own dfrac_valid_own in Hfrac.
  Qed.

  (** If we know that ℓ is in [ll_locs], it is either at the head, or it is
      in the suffix and has a strictly larger key than the head. *)
  Lemma in_ll_keys_cons_2 (ℓ ℓ' ℓ'' ℓℓₙ ℓₘ tℓ: loc) (ll' : llist) (lb ez : extZ) (k' : Z) (lk : val) (b' : bool) (γn : gname) :
    ℓ ↦□ SOMEV (extZ#ez, #ℓℓₙ, #ℓₘ, lk)
    -∗ ⌜ ℓ ∈ ll_locs ((ℓ', b', k') :: ll') ⌝
    -∗ phys_list_aux lb ℓ'' ((ℓ', b', k') :: ll') tℓ γn
    -∗ ⌜ ℓ = ℓ' ∨ (ℓ ∈ ll_locs ll' ∧ lt (Fin k') ez) ⌝.
  Proof.
    iIntros "Hℓ %Hin Hphys".
    pose proof (in_ll_locs_cons _ _ _ _ _ Hin) as [<- | Hin'].
    - by iLeft.
    - iRight.
      iDestruct (phys_list_aux_cons with "Hphys") as
        (k'' ℓℓₙ' ℓₘ' lk' lkn')
        "(#Hℓ' & -> & -> & %Hlt' & (%nℓ' & Hℓℓₙ' & Hphys & #H◯nℓ') & Hℓₘ' & #Hislk')".
      iDestruct (in_locs_in_keys _ _ _ _ _ ll' with "Hℓ [//] Hphys") as "%Hink".
      destruct Hink as (z & -> & Hink).
      iDestruct (gt_lb _ _ _ _ z _ with "[//] Hphys") as "a".
      iSplit; done.
  Qed.

  (** Helper lemma for phys_list_split to factor out the induction. *)
  Lemma phys_list_split_aux (pℓ pℓℓₙ pℓₘ ℓ cℓ cℓℓₙ cℓₘ tℓ tℓℓₙ tℓₘ : loc) (lb pk ck : extZ) (ll : llist) (plk clk tlk : val) (γn : gname) :
    pℓ ↦□ SOMEV (extZ#pk, #pℓℓₙ, #pℓₘ, plk)
    -∗ pℓℓₙ ↦{#1/2} SOMEV #cℓ
    -∗ cℓ ↦□ SOMEV (extZ#ck, #cℓℓₙ, #cℓₘ, clk)
    -∗ ⌜ pℓ ∈ ll_locs ll ⌝
    -∗ ⌜ lt pk ck ⌝
    -∗ tℓ ↦□ SOMEV (extZ#PInf, #tℓℓₙ, #tℓₘ, tlk)
    -∗ phys_list_aux lb ℓ ll tℓ γn
    -∗ pℓℓₙ ↦ SOMEV #cℓ
       ∗ ∃ (llpre llsuf : llist),
         ⌜ ll = llpre ++ llsuf ⌝
         ∗ ⌜ ∀ (z : Z), z ∈ ll_keys llpre -> leq (Fin z) pk ⌝
         ∗ ⌜ cℓ ∉ ll_locs llpre ⌝
         ∗ phys_list_aux pk cℓ llsuf tℓ γn
         ∗ (∀ (llsuf' : llist) (ℓ' : loc),
             own γn (◯ {[ℓ']})
             -∗ pℓℓₙ ↦{#1/2} SOMEV #ℓ'
             -∗ phys_list_aux pk ℓ' llsuf' tℓ γn
             -∗ phys_list_aux lb ℓ (llpre ++ llsuf') tℓ γn).
  Proof.
    iIntros "#Hpℓ Hpℓℓₙ #Hcℓ %Hin %Hpltc #Htℓ Hphys".
    iInduction ll as [|[[ℓ' b'] k'] ll'] "IH" forall (lb ℓ); first done.
    iDestruct (in_ll_keys_cons_2 with "Hpℓ [//] Hphys") as "%Hcases". clear Hin.
    iDestruct (phys_list_aux_cons with "Hphys") as
      (k ℓℓₙ ℓₘ lk lkn)
      "(#Hℓ & <- & <- & %Hlt & (%nℓ & Hℓℓₙ & Hphys & #H◯nℓ) & Hℓₘ & #Hislk)".
    destruct Hcases as [<- | [Hin Hpltk]].
    - iCombine "Hℓ Hpℓ" gives "[_ %Heq]".
      inversion Heq as [Hk]. subst. clear Heq.
      apply extZ_inv_fin in Hk as ->.
      iCombine "Hℓℓₙ Hpℓℓₙ" gives "[_ %Heq]". inversion Heq. subst. clear Heq.
      iCombine "Hpℓℓₙ Hℓℓₙ" as "Hpℓℓₙ". iFrame "Hpℓℓₙ".
      (* Use iExists so we can use iSplit to have more manageable goals *)
      iExists [(pℓ, b', k)], ll'.
      repeat iSplit; first done.
      + iPureIntro. destruct b'; set_solver.
      + rewrite ll_locs_singleton not_elem_of_singleton.
        iIntros "%Heq". subst.
        iCombine "Hpℓ Hcℓ" gives "[_ %Heq]".
        inversion Heq as [Hk]. apply extZ_inv_fin in Hk as ->.
        rewrite /lt in Hpltc. lia.
      + iFrame "Hphys".
        iIntros "%llsuf' %ℓ' H◯ℓ' Hpℓℓₙ Hphys".
        rewrite <- cons_as_app.
        iApply (phys_list_aux_cons lb pℓ tℓ llsuf' pℓ b' k γn).
        iFrame "Hℓ Hℓₘ Hislk".
        repeat iSplit; try done.
        iFrame "∗ #".
    - iDestruct ("IH" $! Hin (Fin k) nℓ with "Hpℓℓₙ Hphys") as
        "(Hpℓℓₙ & %llpre & %llsuf & %Hll & %Hpleq & %Hnin & Hphys & Hwd)".
      iFrame "Hpℓℓₙ".
      (* Use iExists so we can use iSplit to have more manageable goals *)
      iExists ((ℓ, b', k) :: llpre), llsuf.
      repeat iSplit.
      + by rewrite Hll.
      + iPureIntro. intro z.
        rewrite ll_keys_cons elem_of_union.
        intros [Hsingleton | Hllpre].
        * rewrite ll_keys_singleton in Hsingleton.
          destruct b'; first done.
          rewrite elem_of_singleton in Hsingleton.
          rewrite /leq. rewrite /lt in Hpltk.
          destruct pk; lia.
        * by apply Hpleq.
      + rewrite cons_as_app ll_locs_app elem_of_union.
        iIntros "%Hcin".
        destruct Hcin as [Hsingleton | Hllpre].
        * rewrite ll_locs_singleton elem_of_singleton in Hsingleton.
          rewrite <- Hsingleton.
          iCombine "Hℓ Hcℓ" gives %[_ Heq].
          inversion Heq as [Hk]. apply extZ_inv_fin in Hk as ->.
          rewrite /lt in Hpltc Hpltk.
          destruct pk; lia.
        * done.
      + iFrame.
        iIntros "%llsuf' %ℓ' #H◯ℓ' Hpℓℓₙ Hphys".
        iDestruct ("Hwd" $! llsuf' ℓ' with "H◯ℓ' Hpℓℓₙ Hphys") as "Hphys".
        iApply (phys_list_aux_cons lb ℓ tℓ (llpre ++ llsuf') ℓ b' k γn).
        iFrame "Hℓ Hℓₘ Hislk". repeat iSplit; try done.
        by iFrame.
  Qed.

  (** One of the main lemmas in the formalization. If we have locked a node
      pℓ that points to some other node (i.e., we have locked the head, or
      an unmarked, non-sentinel node), we get the following:
      - full permission to update what the predecessor points to
      - a split of the physical list into a prefix and suffix
      - a wand that allows the reconstruction of the physical list. *)
  Lemma phys_list_split (hℓ pℓ pℓℓₙ pℓₘ cℓ cℓℓₙ cℓₘ tℓ tℓℓₙ tℓₘ : loc) (pk ck : extZ) (ll : llist) (plk clk tlk : val) (γn : gname) :
    pℓ ↦□ SOMEV (extZ#pk, #pℓℓₙ, #pℓₘ, plk)
    -∗ pℓℓₙ ↦{#1/2} SOMEV #cℓ
    -∗ cℓ ↦□ SOMEV (extZ#ck, #cℓℓₙ, #cℓₘ, clk)
    -∗ ⌜ pℓ = hℓ ∨ pℓ ∈ ll_locs ll⌝
    -∗ ⌜ lt pk ck ⌝
    -∗ tℓ ↦□ InjRV (extZ#PInf, #tℓℓₙ, #tℓₘ, tlk)
    -∗ phys_list hℓ ll tℓ γn
    -∗ pℓℓₙ ↦ SOMEV #cℓ ∗
       ∃ (llpre llsuf : llist),
         ⌜ ll = llpre ++ llsuf ⌝
        (** Note how these are all the constraints on [llpre] we tell users
            about. In particular, the latter cannot be derived from the former
            by the user, since we do not give them anything like [phys_list_aux]
            on [llpre] that links locations of nodes to keys. *)
         ∗ ⌜ ∀ (z : Z), z ∈ ll_keys llpre -> leq (Fin z) pk ⌝
         ∗ ⌜ cℓ ∉ ll_locs llpre ⌝
         (** Constrain the suffix using [phys_list_aux]. *)
         ∗ phys_list_aux pk cℓ llsuf tℓ γn ∗
         (** If [pℓ] is updated to a valid node representing a valid
             suffix (i.e., satisfies [phys_list_aux]), we can reconstruct
             a new [phys_list] with the same prefix and updated suffix. *)
         (∀ (llsuf' : llist) (ℓ : loc),
            own γn (◯ {[ℓ]})
            -∗ pℓℓₙ ↦{#1/2} SOMEV #ℓ
            -∗ phys_list_aux pk ℓ llsuf' tℓ γn
            -∗ phys_list hℓ (llpre ++ llsuf') tℓ γn).
  Proof.
    iIntros "#Hpℓ Hpℓℓₙ #Hcℓ %Hcases %Hlt #Htℓ Hphys".
    iDestruct "Hphys" as
      (hℓℓₙ hnℓ hℓₘ hlk hlkn)
        "(#Ht & #H◯hℓ & #Hhℓ & Hhℓℓₙ & Hphys & #H◯hnℓ & Hhℓₘ & #Hhlk)".
    destruct Hcases as [-> | Hin].
    - iCombine "Hhℓ Hpℓ" gives %[_ Heq].
      inversion Heq as [Hk]. subst. clear Heq.
      apply extZ_inv_ninf in Hk. subst.
      iCombine "Hpℓℓₙ Hhℓℓₙ" gives %[_ Heq].
      inversion Heq as [Hk]. subst. clear Heq.
      iCombine "Hpℓℓₙ Hhℓℓₙ" as "Hpℓℓₙ".
      iFrame "Hpℓℓₙ".
      (* Use iExists so we can use iSplit to finish trivial parts of the goal *)
      iExists [], ll.
      repeat iSplit; try done.
      iFrame "Hphys".
      iIntros "%llsuf %ℓ #H◯ℓ Hpℓℓₙ Hphys".
      iFrame "Ht # ∗".
    - iDestruct (phys_list_split_aux with "Hpℓ Hpℓℓₙ Hcℓ [//] [//] Htℓ Hphys") as
        "(Hpℓℓₙ & %llpre & %llsuf & %Hll & %Hpleq & %Hnin & Hphys & Hwd)".
      iFrame "Hpℓℓₙ".
      (* Use iExists so we can use iSplit to finish trivial parts of the goal *)
      iExists llpre, llsuf.
      repeat iSplit; try done.
      iFrame "Hphys".
      iIntros "%llsuf' %ℓ H◯ℓ Hpℓℓₙ Hphys".
      iDestruct ("Hwd" $! llsuf' ℓ with "H◯ℓ Hpℓℓₙ Hphys") as "Hphys".
      iFrame "Ht # ∗".
  Qed.

  (** Moves the permissions for a node into [removed_perm]. *)
  Lemma removed_add (ℓ ℓℓₙ ℓₘ nℓ nℓℓₙ nℓₘ : loc) (z : Z) (nk : extZ) (lk nlk : val) (lkn : lock_name) (removed : gset loc) (γn : gname) :
    ⌜ ℓ ∉ removed ⌝
    -∗ ℓ ↦□ InjRV (extZ#(Fin z), #ℓℓₙ, #ℓₘ, lk)
    -∗ is_lock lkn lk (lock_content ℓℓₙ ℓₘ)
    -∗ ℓℓₙ ↦{#1 / 2} lopt#(Some nℓ)
    -∗ ℓₘ ↦□ #true
    -∗ own γn (◯ {[nℓ]})
    -∗ nℓ ↦□ InjRV (extZ#nk, #nℓℓₙ, #nℓₘ, nlk)
    -∗ ⌜lt (Fin z) nk⌝
    -∗ removed_perm removed γn
    -∗ removed_perm ({[ℓ]} ∪ removed) γn.
  Proof.
    iIntros "%Hnin #Hℓ #Hislk Hℓℓₙ #Hℓₘ #H◯nℓ #Hnℓ %Hlt Hremp".
    rewrite /removed_perm big_sepS_insert; [|done].
    by iFrame "Hremp Hℓℓₙ H◯nℓ Hnℓ #".
  Qed.

  (** Logically removing a node does not have a larger effect on [nodes]. *)
  Lemma nodes_mark (hℓ ℓ tℓ : loc) (removed : gset loc) (llpre llsuf : llist) (m : bool) (k : Z) (γn : gname) :
    nodes hℓ removed (llpre ++ (ℓ, m, k) :: llsuf) tℓ γn
    -∗ nodes hℓ removed (llpre ++ (ℓ, true, k) :: llsuf) tℓ γn.
  Proof.
    iIntros "Hnodes".
    destruct m; first done.
    iDestruct "Hnodes" as "(H●γn & (%Hdsjrl & %Hdsjrt & %Hdsjls) & %Hneq)".
    rewrite /nodes !cons_middle !ll_locs_app !ll_locs_singleton.
    rewrite !cons_middle !ll_locs_app !ll_locs_singleton in Hdsjrl, Hdsjls.
    repeat iSplit; done.
  Qed.

  (** When physically removing a node, we need to move it into the [removed]
      set of [nodes]. *)
  Lemma nodes_remove (hℓ ℓ tℓ : loc) (removed : gset loc) (llpre llsuf : llist) (m : bool) (k : Z) (γn : gname) :
    ⌜ ℓ ∉ ll_locs llpre ⌝
    -∗ ⌜ ℓ ∉ ll_locs llsuf ⌝
    -∗ ⌜ ℓ ≠ tℓ ⌝
    -∗ nodes hℓ removed (llpre ++ (ℓ, m, k) :: llsuf) tℓ γn
    -∗ nodes hℓ ({[ℓ]} ∪ removed) (llpre ++ llsuf) tℓ γn.
  Proof.
    rewrite /nodes. rewrite cons_middle !ll_locs_app. rewrite ll_locs_singleton.
    iIntros "%Hninpre %Hninsuf %Hneqt (H●γn & (%Hdsjrl & %Hdsjrt & %Hdsjls) & %Hneq)".
    repeat iSplit.
    - replace (removed ∪ (ll_locs llpre ∪ ({[ℓ]} ∪ ll_locs llsuf)) ∪ {[hℓ; tℓ]})
        with ({[ℓ]} ∪ removed ∪ (ll_locs llpre ∪ ll_locs llsuf) ∪ {[hℓ; tℓ]})
        by set_solver.
      iFrame.
    - iPureIntro. rewrite disjoint_union_l. set_solver.
    - iPureIntro. rewrite disjoint_union_l. set_solver.
    - iPureIntro. rewrite !disjoint_union_l in Hdsjls. set_solver.
    - done.
  Qed.

  (** *** Helper Specifications ***********************************************)
  (** To make proving the specifications of the set operations easier,
      we prove a few helper specs first. *)

  (** [new_node] returns a node with all the right ghost state. *)
  Lemma new_node_spec (key : val) (next : lopt):
    {{{ True }}}
      new_node key lopt#next
    {{{ (node : loc) (ℓℓₙ : loc) (ℓℓₘ : loc) lock lock_name, RET #node;
        node ↦ SOMEV (key, #ℓℓₙ, #ℓℓₘ, lock) ∗
        ℓℓₙ ↦{#1/2} lopt#next ∗ ℓℓₘ ↦{#1/2} #false ∗
        is_lock lock_name lock (lock_content ℓℓₙ ℓℓₘ) }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_lam. wp_alloc next' as "[H₀ℓℓₙ H₁ℓℓₙ]". wp_alloc mark as "[H₀ℓℓₘ H₁ℓℓₘ]".
    wp_pures.
    wp_apply (newlock_spec (lock_content next' mark) with "[H₀ℓℓₙ H₀ℓℓₘ]").
    { iFrame. }
    iIntros (lk γ) "Hlock". wp_pures.
    wp_alloc node as "Hℓ".
    iApply ("HΦ" with "[$]").
  Qed.

  (** For any valid node [ℓ] that is not the tail, [deref (get_next #ℓ)] returns
      its next node, which is valid and has a strictly larger key. *)
  Lemma deref_get_next (hℓ ℓ ℓℓₙ ℓₘ tℓ : loc) (k : extZ) (lk : val) (γn γc γt : gname) :
    {{{ is_set hℓ γn γc γt ∗
        own γn (◯{[ℓ]}) ∗ ℓ ↦□ SOMEV (extZ#k, #ℓℓₙ, #ℓₘ, lk) ∗
        own γt (to_agree tℓ) ∗ ⌜ ℓ ≠ tℓ ⌝ }}}
      deref (get_next #ℓ)
    {{{ (nℓ nℓℓₙ nℓₘ : loc) (nk : extZ) (nlk : val),
        RET #nℓ;
        own γn (◯{[nℓ]}) ∗ nℓ ↦□ SOMEV (extZ#nk, #nℓℓₙ, #nℓₘ, nlk) ∗
        ⌜ lt k nk ⌝ }}}.
  Proof.
    iIntros (Φ) "(HIset & H◯ℓ & Hℓ & #Hγt & %Hneq) HΦ".
    repeat wp_lam. wp_load. wp_pures. wp_lam. wp_bind (! _)%E.
    iInv "HIset" as "Hset" "Hclose".
    iDestruct (next_node with "Hset [H◯ℓ //] [Hℓ //] [Hγt //] [//]") as
      (nℓ nℓℓₙ nℓₘ nk nlk) "(Hℓℓₙ & >#H◯nℓ & >#Hnℓ & >%Hlt & Hwd)".
    wp_load.
    iDestruct ("Hwd" with "Hℓℓₙ") as "Hset".
    iMod ("Hclose" with "Hset") as "_".
    iModIntro. wp_pures. iModIntro.
    iApply "HΦ". by iFrame "#".
  Qed.

  (** [get_lock] returns the lock. *)
  Lemma get_lock_spec (ℓ : loc) (k n m lk : val) :
    {{{ ℓ ↦□ SOMEV (k, n, m, lk) }}}
      get_lock #ℓ
    {{{ RET lk ; True }}}.
  Proof.
    iIntros (Φ) "Hℓ HΦ".
    wp_lam. wp_apply (deref_spec with "Hℓ") as "Hℓ". wp_pures.
    iApply ("HΦ" with "[$]").
  Qed.

  (** [lock_node] locks the node. *)
  Lemma lock_node_spec (ℓ: loc) (k n m lk : val) (lkn : lock_name) (lkc : iProp) :
    {{{ ℓ ↦□ SOMEV (k, n, m, lk) ∗ is_lock lkn lk lkc }}}
      lock_node #ℓ
    {{{ RET #() ; locked lkn ∗ lkc }}}.
  Proof.
    iIntros (Φ) "#(Hℓ & Hlk) HΦ".
    wp_lam. wp_apply get_lock_spec as "_"; first done.
    wp_apply acquire_spec; by iFrame.
  Qed.

  (** [unlock_node] unlocks the node. *)
  Lemma unlock_node_spec (ℓ ℓℓₙ ℓₘ: loc) (k lk : val) (lkn : lock_name) :
    {{{ ℓ ↦□ SOMEV (k, #ℓℓₙ, #ℓₘ, lk) ∗ is_lock lkn lk (lock_content ℓℓₙ ℓₘ) ∗
        (lock_content ℓℓₙ ℓₘ) ∗ locked lkn }}}
       unlock_node #ℓ
    {{{ RET #() ; True }}}.
  Proof.
    iIntros (Φ) "(#Hℓ & #Hlk & Hlkc & Hlkd) HΦ".
    wp_lam. wp_apply get_lock_spec as "_"; first done.
    wp_apply (release_spec _ _ (lock_content ℓℓₙ ℓₘ) with "[Hlkc Hlkd]");
      by iFrame.
  Qed.

  (** One of the main lemmas. The loop invariant of [walk2] can be described as
      - [pℓ] and [cℓ] are valid nodes
      - the key of [pℓ] is strictly less than the key of [cℓ]
      - the key we are looking for is strictly larger than the key of [pℓ]
      Once the loop has terminated, [cℓ] is larger or equal to the key we are
      looking for. *)
  Lemma walk2_spec (hℓ pℓℓ pℓ pℓℓₙ pℓₘ cℓℓ cℓ cℓℓₙ cℓₘ tℓ tℓℓₙ tℓₘ: loc)
    (γn γc γt : gname) (pk ck : extZ) (plk clk tlk : val) (key : Z) :
    {{{ is_set hℓ γn γc γt ∗
        own γt (to_agree tℓ) ∗ tℓ ↦□ SOMEV (extZ#PInf, #tℓℓₙ, #tℓₘ, tlk) ∗
        pℓℓ ↦ #pℓ ∗ cℓℓ ↦ #cℓ ∗
        own γn (◯{[pℓ]}) ∗ pℓ ↦□ SOMEV (extZ#pk, #pℓℓₙ, #pℓₘ, plk) ∗
        own γn (◯{[cℓ]}) ∗ cℓ ↦□ SOMEV (extZ#ck, #cℓℓₙ, #cℓₘ, clk) ∗
        ⌜ lt pk (Fin key) ⌝ ∧ ⌜ lt pk ck ⌝ }}}
      walk2 extZ#(Fin key) #pℓℓ #cℓℓ
    {{{ (p'ℓ p'ℓℓₙ p'ℓₘ c'ℓ c'ℓℓₙ c'ℓₘ : loc) (p'k c'k : extZ) (p'lk c'lk : val),
        RET #();
        pℓℓ ↦ #p'ℓ ∗ cℓℓ ↦ #c'ℓ ∗
        own γn (◯{[p'ℓ]}) ∗ p'ℓ ↦□ SOMEV (extZ#p'k, #p'ℓℓₙ, #p'ℓₘ, p'lk) ∗
        own γn (◯{[c'ℓ]}) ∗ c'ℓ ↦□ SOMEV (extZ#c'k, #c'ℓℓₙ, #c'ℓₘ, c'lk) ∗
        ⌜ lt p'k (Fin key) ⌝ ∧ ⌜ leq (Fin key) c'k ⌝ }}}.
  Proof.
    iIntros (Φ)
      "(#HIset & #Hγt & #Htℓ & Hpℓℓ & Hcℓℓ & H◯pℓ & Hpℓ & #H◯cℓ & #Hcℓ &
        Hltk & Hltc) HΦ".
    iLöb as "IH" forall (pℓ pk pℓℓₙ pℓₘ plk cℓ ck cℓℓₙ cℓₘ clk) "H◯cℓ Hcℓ".
    wp_lam. wp_pures. wp_load.
    repeat wp_lam. wp_load. wp_pures.
    destruct ck; (wp_lam; wp_pures).
    - destruct (decide (z < key)%Z) as [Hlt|Hgeq].
      + rewrite bool_decide_eq_true_2; [|done]. wp_pures.
        wp_load. wp_store. wp_load.
        destruct (decide (cℓ = tℓ)%Z) as [->|Hneq].
        * iCombine "Htℓ Hcℓ" gives "[_ %Hteq]". inversion Hteq.
        * wp_apply (deref_get_next with "[$HIset $Hγt $H◯cℓ $Hcℓ //]") as
            (cnℓ cnℓℓₙ cnℓₘ cnk cnlk) "(#H◯cnℓ & #Hcnℓ & Hltcnk)".
          wp_store.
          iApply ("IH" with "Hpℓℓ Hcℓℓ H◯cℓ Hcℓ [//] Hltcnk HΦ H◯cnℓ Hcnℓ").
      + rewrite bool_decide_eq_false_2; [|done]. wp_pures.
        iApply "HΦ". iFrame "Hpℓℓ Hcℓℓ H◯pℓ Hpℓ H◯cℓ Hcℓ Hltk".
        iPureIntro. simpl. lia.
    - iApply "HΦ". by iFrame "Hpℓℓ Hcℓℓ H◯pℓ Hpℓ H◯cℓ Hcℓ Hltk".
    - wp_load. wp_store. wp_load.
      destruct (decide (cℓ = tℓ)%Z) as [->|Hneq].
      * iCombine "Htℓ Hcℓ" gives "[_ %Hteq]". inversion Hteq.
      * wp_apply (deref_get_next with "[$HIset $Hγt $H◯cℓ $Hcℓ //]") as
            (cnℓ cnℓℓₙ cnℓₘ cnk cnlk) "(#H◯cnℓ & #Hcnℓ & Hltcnk)".
        wp_store.
        iApply ("IH" with "Hpℓℓ Hcℓℓ H◯cℓ Hcℓ [//] Hltcnk HΦ H◯cnℓ Hcnℓ").
  Qed.

  (** The spec for validate is surprisingly simple: It is the same as what is
      being tested (neither node is marked, and [pℓ] points to [cℓ]). *)
  Lemma validate_spec (hℓ pℓ pℓℓₙ pnℓ pℓₘ cℓ cℓℓₙ cℓₘ tℓ : loc) (pm cm : bool) (pk ck : extZ) (plk clk : val) (γn γc γt : gname) :
    {{{ is_set hℓ γn γc γt ∗ own γt (to_agree tℓ) ∗
        pℓ ↦□ SOMEV (extZ#pk, #pℓℓₙ, #pℓₘ, plk) ∗
        cℓ ↦□ SOMEV (extZ#ck, #cℓℓₙ, #cℓₘ, clk) ∗
        pℓℓₙ ↦{#1/2} lopt#(Some pnℓ) ∗ pℓₘ ↦{#1/2} #pm ∗ cℓₘ ↦{#1/2} #cm
    }}}
      validate #pℓ #cℓ
    {{{ (b : bool), RET #b ;
        if b
        then pℓℓₙ ↦{#1/2} SOMEV #cℓ ∗ pℓₘ ↦{#1/2} #false ∗ cℓₘ ↦{#1/2} #false
        else pℓℓₙ ↦{#1/2} lopt#(Some pnℓ) ∗ pℓₘ ↦{#1/2} #pm ∗ cℓₘ ↦{#1/2} #cm }}}.
  Proof.
    iIntros (Φ) "(HIset & Hγt & Hpℓ & Hcℓ & Hpℓℓₙ & Hpℓₘ & Hcℓₘ) HΦ".
    wp_lam. wp_pures. repeat wp_lam. repeat wp_load.
    destruct pm.
    - wp_pures. iApply "HΦ". by iFrame.
    - wp_pures. repeat wp_lam. repeat wp_load.
      destruct cm.
      + wp_pures. iApply "HΦ". by iFrame.
      + wp_pures. repeat wp_lam. wp_load. wp_pures. wp_lam. wp_load. wp_pures.
        destruct (decide (#pnℓ = #cℓ)) as [<-|Hneq].
        * rewrite bool_decide_eq_true_2; [|done].
          iApply "HΦ". by iFrame.
        * rewrite bool_decide_eq_false_2; [|done].
          iApply "HΦ". by iFrame.
  Qed.

  (** *** Set Operation Specifications ****************************************)

  (** We now have all the pieces in place to prove the specifications for
      creating a new set, adding a key to the set, and removing a key from the
      set. *)

  (** [new_set] returns a valid set. *)
  Lemma new_set_spec :
    {{{ True }}}
      new_set #()
    {{{ γn γc γt ℓ, RET #ℓ; is_set ℓ γn γc γt ∗ set_content γc ∅ }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_lam.
    (** Initialize the tail node. *)
    wp_lam. wp_pures.
    wp_alloc tℓℓₙ as "[Htℓℓₙ Htℓℓₙ'] ".
    iMod (pointsto_persist with "Htℓℓₙ") as "#Htℓℓₙ". wp_pures.
    wp_alloc tℓₘ as "[Htℓₘ Htℓₘ']".
    iMod (pointsto_persist with "Htℓₘ") as "#Htℓₘ". wp_pures.
    wp_apply (newlock_spec (lock_content tℓℓₙ tℓₘ) with "[Htℓℓₙ' Htℓₘ']")
      as (tlk tlkn) "Htlk".
    { (* iFrame cannot figure out that lopt#None is the same as InjLV #(), so
         we manually use iExists. *)
      iExists None, false. iFrame. }
    wp_pures. wp_alloc tℓ as "Htℓ". wp_pures.
    (** Initialize the head node. *)
    wp_lam. wp_pures.
    wp_alloc hℓℓₙ as "[Hhℓℓₙ Hhℓℓₙ']". wp_pures.
    wp_alloc hℓₘ as "[Hhℓₘ Hhℓₘ']".
    iMod (pointsto_persist with "Hhℓₘ") as "#Hhℓₘ". wp_pures.
    wp_apply (newlock_spec (lock_content hℓℓₙ hℓₘ) with "[Hhℓℓₙ' Hhℓₘ']")
      as (hlk hlkn) "Hhlk".
    { (* iFrame cannot figure out that lopt#(Some tℓ) is the same as InjLV #tℓ,
         so we manually use iExists. *)
      iExists (Some tℓ), false. iFrame. }
    wp_pures. wp_alloc hℓ as "Hhℓ".
    iMod (pointsto_persist with "Hhℓ") as "#Hhℓ". wp_pures.
    iMod (pointsto_persist with "Htℓ") as "#Htℓ".
    (** Initialize the ghost state. *)
    iMod (own_alloc (● {[hℓ;tℓ]} ⋅ ◯ {[hℓ;tℓ]})) as (γn) "[Hγn● Hγn◯]";
      first by apply auth_both_valid.
    replace (◯ {[hℓ; tℓ]}) with (◯ ({[hℓ]} ⋅  {[tℓ]})) by (by rewrite gset_op).
    iDestruct "Hγn◯" as "[#H◯hℓ #H◯tℓ]".
    iMod (own_alloc ((●E ∅) ⋅ (◯E ∅))) as (γc) "[Hγc● Hγc◯]";
      first by apply excl_auth_valid.
    iMod (own_alloc (to_agree tℓ)) as (γt) "Hγt"; first done.
    iMod (inv_alloc N _ (set_inv hℓ γn γc γt) with "[-Hγc◯ HΦ]") as "#HIset".
    { (* Use iExists so we can use iSplit to have more manageable goals *)
      iExists ∅, ∅, [], tℓ. iSplitL "Hγn●".
      - rewrite /nodes. rewrite /ll_locs. simpl.
        replace (∅ ∪ ∅ ∪ {[hℓ; tℓ]}) with ({[hℓ; tℓ]} : gset loc) by set_solver.
        repeat iSplit; try done.
        { iIntros "%Heq". subst.
          iCombine "Hhℓ Htℓ" gives "[_ %Hteq]". inversion Hteq. }
      - iFrame "Hγc● Hγt".
        unfold removed_perm. rewrite big_sepS_empty.
        repeat iSplit; try done.
        by iFrame "# ∗". }
    (** Prove the postcondition. *)
    iApply "HΦ". by iFrame "HIset ∗".
  Qed.

  (** During the execution of [add] there always exists (an atomic)
      point of time where a key is added to the set. It also returns whether
      a key was actually added to the set. *)
  Lemma add_spec (hℓ : loc) (γn : gname) (γc : gname) (γt : gname) (key : Z) :
    is_set hℓ γn γc γt -∗
    <<{ ∀∀ (ls : gset Z), set_content γc ls }>>
      add #hℓ extZ#(Fin key) @ ↑N
    <<{ set_content γc (ls ∪ {[ key ]}) | RET #(bool_decide (key ∉ ls)) }>>.
  Proof.
    iIntros "#HIset" (Φ) "AU". iLöb as "HIadd".
    iApply fupd_wp; iMod (fupd_mask_subseteq (↑N)) as "close"; first done.
    (** Grab the initial facts. *)
    iMod (initial_facts with "HIset") as
      "(%hℓℓₙ & %hℓₘ & %hlk & #Hhℓ &
         %tℓ & %tℓℓₙ & %tℓₘ & %tlk & #Hγt & >%Hhtneq & #Htℓ & #Ht & #H◯hℓ)".
    iMod "close" as "_"; iModIntro.
    wp_lam. wp_pures.
    wp_alloc pℓℓ as "Hpℓℓ". wp_pures.
    wp_apply (deref_get_next with "[]") as
      (hnℓ hnℓℓₙ hnℓₘ hnk hnlk) "(H◯hnℓ & Hhnℓ & Hlthn)".
    { by iFrame "HIset H◯hℓ Hhℓ Hγt". }
    wp_alloc cℓℓ as "Hcℓℓ". wp_pures.
    (** Walk the list to the expected position of the key. *)
    wp_apply (walk2_spec with "[-AU]") as
      (pℓ pℓℓₙ pℓₘ cℓ cℓℓₙ cℓₘ pk ck plk clk)
      "(Hpℓℓ & Hcℓℓ & #H◯pℓ & #Hpℓ & #H◯cℓ & #Hcℓ & %Hltk & %Hleqc)".
    { by iFrame "HIset Hpℓℓ Hcℓℓ Hγt Htℓ H◯hℓ Hhℓ H◯hnℓ Hhnℓ Hlthn". }
    iApply fupd_wp; iMod (fupd_mask_subseteq (↑N)) as "close"; first done.
    (** Lock the nodes. *)
    iMod (get_is_lock with "HIset Hγt H◯pℓ Hpℓ") as (plkn) "#Hpislk".
    iMod (get_is_lock with "HIset Hγt H◯cℓ Hcℓ") as (clkn) "#Hcislk".
    iMod "close" as "_"; iModIntro.
    wp_pures. wp_load.
    wp_apply (lock_node_spec with "[$Hpℓ $Hpislk]") as "[Hplkd Hplkc]".
    wp_pures. wp_load.
    wp_apply (lock_node_spec with "[$Hcℓ $Hcislk]") as "[Hclkd Hclkc]".
    wp_pures. repeat wp_load.
    (** The lock only tells us that next points to a possibly null reference. *)
    iDestruct "Hplkc" as (pnℓo pm) "[Hpℓℓₙ Hpℓₘ]".
    (** However, we know that the predecessor is never the tail... *)
    iAssert (⌜ pℓ ≠ tℓ ⌝ %I) as "%Hpℓnt".
    { iIntros "%Heqt". rewrite -> Heqt.
      iCombine "Htℓ Hpℓ" gives "[_ %Hteq]".
      inversion Hteq as [Hk].
      apply extZ_inv_pinf in Hk. by rewrite Hk in Hltk. }
    (** ...so it is pointing to some other node, i.e., is not null. *)
    iApply fupd_wp; iMod (fupd_mask_subseteq (↑N)) as "close"; first done.
    iDestruct (not_tail_has_next with "HIset Hγt H◯pℓ Hpℓ [//] Hpℓℓₙ") as ">[%pnℓ Hpℓℓₙ]".
    iMod "close" as "_"; iModIntro.
    iDestruct "Hclkc" as (cnℓo cm) "[Hcℓℓₙ Hcℓₘ]".
    (** Check whether we are in a valid state to perform the add. *)
    wp_apply (validate_spec with "[Hpℓℓₙ Hpℓₘ Hcℓₘ]") as (is_valid) "Hval".
    { iFrame "# ∗". }
    destruct is_valid; iDestruct "Hval" as "(Hpℓℓₙ & Hpℓₘ & Hcℓₘ)".
    - (** Validate was successful. *)
      wp_pures. wp_load. repeat wp_lam. wp_load. wp_pures.
      destruct (decide (ck = Fin key)) as [-> | Hneq].
      + (** Key is already in the set - we do not need to add anything.
            However, we still need to choose a linearization point. *)
        wp_pures. wp_lam. wp_pures.
        rewrite bool_decide_eq_true_2; [|done].
        wp_pures. wp_bind (!_)%E.
        (** We choose this as a linearization point, since we can bind the load
            to open the invariant and atomic update. *)
        iInv "HIset" as "Hset" "Hclose".
        iMod "AU" as (ls) "[Hγc◯ [_ Hclose']]".
        wp_load.  (* Getting rid of the laters to make our lifes easier *)
        iDestruct "Hset" as
          (removed ls' ll tℓ') "(Hnodes & Hγc● & Hγt' & %Hllk & Hphys & Hremp)".
        iCombine "Hγt Hγt'" gives %<-%to_agree_op_valid_L; iClear "Hγt'".
        iDestruct (eauth_agree with "Hγc● Hγc◯") as %->.
        (** Prove that the key is in the set. We know it must be, since we
            found it. *)
        iDestruct (unmarked_fin_in_ll_sets with
                    "H◯cℓ Hcℓ Hcℓₘ Hnodes Hphys Hremp") as
          "(Hcℓₘ & Hnodes & Hphys & Hremp & %Hkin & _)".
        (** Close the atomic update and the invariant. *)
        iMod ("Hclose'" with "[Hγc◯]") as "Hret".
        { by (replace (ls ∪ {[key]}) with ls by set_solver). }
        rewrite bool_decide_eq_false_2; [| set_solver]. iModIntro.
        iMod ("Hclose" with "[Hnodes Hγc● Hremp Hphys]") as "_".
        { iFrame "∗ # %". }
        iModIntro.
        (** Unlock the nodes and return false, since we did not add anything. *)
        wp_apply (unlock_node_spec with
                   "[$Hcℓ $Hcislk Hcℓℓₙ Hcℓₘ $Hclkd]") as "_".
        { iFrame "Hcℓℓₙ Hcℓₘ". }
        wp_pures. wp_load.
        wp_apply (unlock_node_spec with
                   "[$Hpℓ $Hpislk Hpℓℓₙ Hpℓₘ $Hplkd]") as "_".
        { (* iFrame cannot figure out that lopt#(Some cℓ) is the same as
             InjLV #cℓ, so we manually use iExists. *)
          iExists (Some cℓ), false. iFrame "Hpℓℓₙ Hpℓₘ". }
        wp_pures. iApply "Hret".
      + (** Key is not in the set. We need to add a new node. *)
        (** Since the current node is not the key we were looking for,
            and walk2 guarantees that the key is less than or equal than the
            current node, we know that the key must be strictly less than the
            current node. *)
        pose proof (leq_neq_lt (Fin key) ck Hleqc Hneq) as Hltc.
        wp_apply (eqv_neq_fin $! Hneq) as "_".
        wp_pures. wp_load. wp_pures.
        (** Create a new node with the key. *)
        wp_apply (new_node_spec _ (Some cℓ) with "[//]")
          as (eℓ eℓℓₙ eℓₘ elk elkn) "(Heℓ & Heℓℓₙ & Heℓₘ & #Heislk)".
        wp_pures. wp_load. wp_lam. wp_pures.
        repeat wp_lam. wp_load. wp_pures.
        (** Linearization Point: Hooking the new node in. *)
        wp_bind (_ <- _)%E.
        iInv "HIset" as "Hset" "Hclose".
        iMod "AU" as (ls) "[Hγc◯ [_ Hclose']]".
        iDestruct "Hset" as
          (removed ls' ll tℓ')
          "(Hnodes & Hγc● & >Hγt' & >%Hllk & Hphys & Hremp)".
        iCombine "Hγt Hγt'" gives %<-%to_agree_op_valid_L; iClear "Hγt'".
        (** Prepare some facts for the split: *)
        (** Predecessor is either the head or within the list *)
        iDestruct (unmarked_cases with "H◯pℓ Hpℓ Hpℓₘ Hnodes Hphys Hremp")
          as "(Hpℓₘ & Hnodes & Hphys & Hremp & Hpcases)".
        iDestruct "Hpcases" as ">%Hpcases".
        assert (pℓ = hℓ ∨ pℓ ∈ ll_locs ll) as Hpcases'.
        { destruct Hpcases as [Hph | [Hpl | Hpt]].
          - by left.
          - by right.
          - contradiction. }
        (** The predecessor key is strictly less than the current key. *)
        assert (lt pk ck) as Hlt.
        { eapply lt_leq_trans; done. }
        (** Split the list. *)
        iDestruct (phys_list_split with "Hpℓ Hpℓℓₙ [>Hcℓ //] [//] [//] Htℓ Hphys") as
          "(Hpℓℓₙ & %llpre & %llsuf & >%Hll & >%Hleqllp & >%Hcℓnin & Hphysr & Hwd)".
        (** Hook in the new node. *)
        wp_store.
        (** Since we opened the invariant, we can state that the key was not in
            the list/set. *)
        iAssert (⌜ key ∉ ll_keys ll ⌝%I) as "%Hnin".
        { iIntros "%Hin".
          rewrite Hll ll_keys_app elem_of_union in Hin.
          destruct Hin as [Hinpre|Hinpresuf].
          - (** Key is not in the prefix *)
            pose proof (Hleqllp key Hinpre) as Hleq.
            rewrite /leq in Hleq. rewrite /lt in Hltk.
            destruct pk; lia.
          - (** Key is not in the suffix *)
            iDestruct (update_lb _ _ _ _ _ _ _ (Fin key) with "Hcℓ [//] Hphysr") as "Hphysr".
            iDestruct (gt_lb with "[] Hphysr") as "%Hbad".
            { iPureIntro.
              eapply elem_of_weaken. apply Hinpresuf. apply ll_keys_subset. }
            rewrite /lt in Hbad. lia. }
        iDestruct "Hpℓℓₙ" as "[Hpℓℓₙ' Hpℓℓₙ]".
        (** Add the new node to the ghost state keeping track of all allocated
            nodes. *)
        iDestruct "Hnodes" as "(Hγn● & (%Hdsj_remll & %Hdsj_remtℓ & %Hdsj_llsen) & _)".
        iMod (auth_update _ _ (removed ∪ (ll_locs ll ∪ {[eℓ]}) ∪ {[hℓ; tℓ]})
               with "[] Hγn●") as "Hγn●".
        { iPureIntro. apply union_mono_r, union_mono_l, union_subseteq_l. }
        (** Preparing facts about the newly created node to reestablish the
            invariant. *)
        (** New node is valid. *)
        iMod (auth_frag _ {[eℓ]} _ with "Hγn●") as "[Hγn● H◯eℓ]".
        { set_solver. }
        (** New node is not removed *)
        iAssert (⌜ eℓ ∉ removed ⌝%I) as "%Heℓnrem".
        { iIntros "%Hin".
          iPoseProof (big_sepS_elem_of_acc _ _ _ Hin  with "Hremp")
            as "[Hperm Hwand]".
          iDestruct "Hperm" as (ek eℓℓₙ' eℓₘ' elk' elkn') "[Heℓ' _]".
          iCombine "Heℓ Heℓ'" gives %[Hperm _].
          by rewrite dfrac_valid_own_discarded in Hperm. }
        (** New node is not the head *)
        iAssert (⌜ eℓ ≠ hℓ ⌝ %I) as "%Heℓnh".
        { iIntros "%Heqh". rewrite -> Heqh.
          iCombine "Hhℓ Heℓ" gives "[_ %Hteq]". inversion Hteq. }
        (** New node is not the tail *)
        iAssert (⌜ eℓ ≠ tℓ ⌝ %I) as "%Heℓnt".
        { iIntros "%Heqt". rewrite -> Heqt.
          iCombine "Htℓ Heℓ" gives "[_ %Hteq]". inversion Hteq. }
        iMod (pointsto_persist with "Heℓ") as "#Heℓ".
        iDestruct ("Hwd" $! ((eℓ, false, key) :: llsuf)
                    with "H◯eℓ Hpℓℓₙ' [Heℓℓₙ Heℓₘ Hphysr]") as "Hphys".
        { iApply (phys_list_aux_cons pk eℓ tℓ llsuf eℓ false key γn).
          iFrame "Heℓ Heℓₘ Heislk". repeat iSplit; try done.
          iFrame "# ∗".
          by iDestruct (update_lb _ _ _ _ _ _ _ (Fin key)
                 with "Hcℓ [//] Hphysr") as "Hphysr". }
        (** Add the key to the ghost state representing the set content. *)
        iDestruct (eauth_agree with "Hγc● Hγc◯") as "->".
        iMod (eauth_update γc (ls ∪ {[key]}) with "Hγc● Hγc◯") as "[Hγc● Hγc◯]".
        (** Close the atomic update and the invariant. *)
        iMod ("Hclose'" with "Hγc◯") as "Hret".
        rewrite bool_decide_eq_true_2; [| set_solver]. iModIntro.
        iMod ("Hclose" with "[Hγn● Hγc● Hremp Hphys]") as "_".
        { iFrame "Hγc● Hγt Hphys Hremp".
          rewrite /nodes !(ll_locs_add ll _ _ _ _ _ Hll).
          iSplitL.
          * repeat iSplit; try done; iPureIntro.
            -- rewrite disjoint_union_r. set_solver.
            -- rewrite disjoint_union_l. set_solver.
          * iPureIntro.
            rewrite !cons_middle ll_keys_com12 ll_keys_app.
            rewrite <-Hll. rewrite Hllk.
            rewrite /ll_keys. set_solver. }
        iModIntro.
        wp_pures. wp_load.
        (** Unlock the nodes and return true, since we added the key. *)
        wp_apply (unlock_node_spec with "[$Hcℓ $Hcislk Hcℓℓₙ Hcℓₘ $Hclkd]") as "_".
        { iFrame "Hcℓℓₙ Hcℓₘ". }
        wp_pures. wp_load.
        wp_apply (unlock_node_spec with "[Hplkd Hpℓₘ Hpℓℓₙ]") as "_".
        { iFrame "Hpℓ Hpislk Hplkd".
          (* iFrame cannot figure out that lopt#(Some eℓ) is the same as
             InjLV #eℓ, so we manually use iExists. *)
          iExists (Some eℓ), false. iFrame. }
        wp_pures. iApply "Hret".
    - (** Validate was unsuccessful; unlock the nodes and retry *)
      wp_pures. wp_load.
      wp_apply (unlock_node_spec with "[$Hcℓ $Hcislk Hcℓℓₙ Hcℓₘ $Hclkd]") as "_".
      { iFrame "Hcℓℓₙ Hcℓₘ". }
      wp_pures. wp_load.
      wp_apply (unlock_node_spec with "[$Hpℓ $Hpislk Hpℓℓₙ Hpℓₘ $Hplkd]") as "_".
      { iFrame "Hpℓℓₙ Hpℓₘ". }
      wp_pures. iApply ("HIadd" with "AU").
  Qed.

  (** During the execution of [remove] there always exists (an atomic)
      point of time where the key is removed from the set.
      It also returns whether a key was actually added to the set. *)
  Lemma remove_spec (hℓ : loc) (γn : gname) (γc : gname) (γt : gname) (key : Z) :
    is_set hℓ γn γc γt -∗
    <<{ ∀∀ (ls : gset Z), set_content γc ls }>>
      remove #hℓ extZ#(Fin key) @ ↑N
    <<{ set_content γc (ls ∖ {[ key ]}) | RET #(bool_decide (key ∈ ls))}>>.
  Proof.
    iIntros "#HIset" (Φ) "AU". iLöb as "HIadd".
    iApply fupd_wp; iMod (fupd_mask_subseteq (↑N)) as "close"; first done.
    (** Grab the initial facts. *)
    iMod (initial_facts with "HIset") as
      "(%hℓℓₙ & %hℓₘ & %hlk & #Hhℓ &
         %tℓ & %tℓℓₙ & %tℓₘ & %tlk & #Hγt & >%Hhtneq & #Htℓ & #Ht & #H◯hℓ)".
    iMod "close" as "_"; iModIntro.
    wp_lam. wp_pures.
    wp_alloc pℓℓ as "Hpℓℓ". wp_pures.
    wp_apply (deref_get_next with "[]") as
      (hnℓ hnℓℓₙ hnℓₘ hnk hnlk) "(H◯hnℓ & Hhnℓ & Hlthn)".
    { by iFrame "HIset H◯hℓ Hhℓ Hγt". }
    wp_alloc cℓℓ as "Hcℓℓ". wp_pures.
    (** Walk the list to the expected position of the key. *)
    wp_apply (walk2_spec with "[-AU]") as
      (pℓ pℓℓₙ pℓₘ cℓ cℓℓₙ cℓₘ pk ck plk clk)
      "(Hpℓℓ & Hcℓℓ & #H◯pℓ & #Hpℓ & #H◯cℓ & #Hcℓ & %Hltk & %Hleqc)".
    { by iFrame "HIset Hpℓℓ Hcℓℓ Hγt Htℓ H◯hℓ Hhℓ H◯hnℓ Hhnℓ Hlthn". }
    iApply fupd_wp; iMod (fupd_mask_subseteq (↑N)) as "close"; first done.
    (** Lock the nodes. *)
    iMod (get_is_lock with "HIset Hγt H◯pℓ Hpℓ") as (plkn) "#Hpislk".
    iMod (get_is_lock with "HIset Hγt H◯cℓ Hcℓ") as (clkn) "#Hcislk".
    iMod "close" as "_"; iModIntro.
    wp_pures. wp_load.
    wp_apply (lock_node_spec with "[$Hpℓ $Hpislk]") as "[Hplkd Hplkc]".
    wp_pures. wp_load.
    wp_apply (lock_node_spec with "[$Hcℓ $Hcislk]") as "[Hclkd Hclkc]".
    wp_pures. repeat wp_load.
    (** The lock only tells us that next points to a possibly null reference. *)
    iDestruct "Hplkc" as (pnℓo pm) "[Hpℓℓₙ Hpℓₘ]".
    (** However, we know that the predecessor is never the tail... *)
    iAssert (⌜ pℓ ≠ tℓ ⌝ %I) as "%Hpℓnt".
    { iIntros "%Heqt". rewrite -> Heqt.
      iCombine "Htℓ Hpℓ" gives "[_ %Hteq]".
      inversion Hteq as [Hk].
      apply extZ_inv_pinf in Hk. by rewrite Hk in Hltk. }
    (** ...so it is pointing to some other node, i.e., is not null. *)
    iApply fupd_wp; iMod (fupd_mask_subseteq (↑N)) as "close"; first done.
    iDestruct (not_tail_has_next with "HIset Hγt H◯pℓ Hpℓ [//] Hpℓℓₙ") as
      ">[%pnℓ Hpℓℓₙ]".
    iMod "close" as "_"; iModIntro.
    iDestruct "Hclkc" as (cnℓo cm) "[Hcℓℓₙ Hcℓₘ]".
    (** Check whether we are in a valid state to perform the remove. *)
    wp_apply (validate_spec with "[Hpℓℓₙ Hpℓₘ Hcℓₘ]") as (is_valid) "Hval".
    { iFrame "# ∗". }
    destruct is_valid; iDestruct "Hval" as "(Hpℓℓₙ & Hpℓₘ & Hcℓₘ)".
    - (** Validate was successful. *)
      wp_pures. wp_load. repeat wp_lam. wp_load. wp_pures.
      destruct (decide (ck = Fin key)) as [-> | Hneq].
      + (** Key is in the set - we need to remove it.*)
        wp_pures. wp_lam. wp_pures.
        rewrite bool_decide_eq_true_2; [|done]. wp_pures.
        wp_load. repeat wp_lam. wp_load. wp_pures.
        (** We will later need that the current node is not the tail. *)
        iAssert (⌜ cℓ ≠ tℓ ⌝ %I) as "%Hcℓnt".
        { iIntros "%Heqt". rewrite -> Heqt.
          iCombine "Htℓ Hcℓ" gives "[_ %Hteq]". inversion Hteq. }
        (** Linearization Point: Logically removing the node *)
        wp_bind (_ <- _)%E.
        iInv "HIset" as "Hset" "Hclose".
        iMod "AU" as (ls) "[Hγc◯ [_ Hclose']]".
        iDestruct "Hset" as
          (removed ls' ll tℓ')
            "(Hnodes & Hγc● & >Hγt' & >%Hllk & Hphys & Hremp)".
        (** Prove that the key is in the set. We know it must be, since we
            found it. *)
        iDestruct (unmarked_fin_in_ll_sets with
                    "H◯cℓ Hcℓ Hcℓₘ Hnodes Hphys Hremp") as
          "(Hcℓₘ & Hnodes & Hphys & Hremp & >%Hkin & _)".
        iCombine "Hγt Hγt'" gives %<-%to_agree_op_valid_L; iClear "Hγt'".
        iDestruct "Hγc●" as ">Hγc●".
        iDestruct (eauth_agree with "Hγc● Hγc◯") as %->.
        (** Prepare some facts for the split: *)
        (** Predecessor is either the head or within the list *)
        iDestruct (unmarked_cases with "H◯pℓ Hpℓ Hpℓₘ Hnodes Hphys Hremp")
          as "(Hpℓₘ & Hnodes & Hphys & Hremp & Hpcases)".
        iDestruct "Hpcases" as ">%Hpcases".
        assert (pℓ = hℓ ∨ pℓ ∈ ll_locs ll) as Hpcases'.
        { destruct Hpcases as [Hph | [Hpl | Hpt]].
          - by left.
          - by right.
          - contradiction. }
        iDestruct (phys_list_split with "Hpℓ Hpℓℓₙ [>Hcℓ //] [//] [//] Htℓ Hphys") as
          "(Hpℓℓₙ & %llpre & %llsuf & >%Hll & >%Hleqllp & >%Hcℓnin & Hphysr & Hwd)".
        (** The keys in the prefix cannot be larger than the key at the
            predecessor, which is where we do the split. As the key is larger
            than the key of the predecessor, the key is not in the prefix. *)
        iAssert (⌜ key ∉ ll_keys llpre ⌝%I) as "%Hninp".
        { iIntros "%Hinp".
          pose proof (Hleqllp key Hinp) as Hltc.
          rewrite /leq in Hltk Hltc. rewrite /lt in Hltk.
          destruct pk; lia. }
        (** Grabbing the rest of the permission for ℓₘ to mark the node. *)
        destruct llsuf as [|[[cℓ' cm'] ck'] llsuf'].
        (** Since we found the key at the current node, which follows the
            predecessor, we know that the suffix cannot be empty. Instead,
            the head of the suffix must be the current node. *)
        { iDestruct "Hphysr" as ">->".
          iCombine "Htℓ Hcℓ" gives "[_ %Hheq]". inversion Hheq. }
        iDestruct (key_nin_suf with "Hphysr") as "[Hphysr >%Hnins]".
        iDestruct (phys_list_aux_cons with "Hphysr") as
          (key' ℓℓₙ' ℓₘ' lk' lkn')
          "(>Hcℓ' & ><- & ><- & >%Hltk' &
           (%cnℓ & Hcℓℓₙ' & Hnphysr & H◯cnℓ) & Hcℓₘ' & Hcislk')".
        iCombine "Hcℓ' Hcℓ" gives "[_ %Heq]". inversion Heq as [Hk].
        iClear "Hcℓ' Hcislk'".
        iCombine "Hcℓₘ Hcℓₘ'" as "Hcℓₘ". rewrite dfrac_op_own Qp.half_half.
        (** We (finally) have the permission, so we can logically delete the
            node by marking it. *)
        wp_store.
        (* This will save us a case distinction when we want to physically
           delete the node later on *)
        iDestruct (pointsto_agree with "Hcℓℓₙ Hcℓℓₙ'") as "->".
        (** Closing the atomic update. *)
        iMod (eauth_update γc (ls ∖ {[key]}) with "Hγc● Hγc◯")
          as "[Hγc● Hγc◯]".
        iMod ("Hclose'" with "Hγc◯") as "Hret".
        rewrite bool_decide_eq_true_2; [| set_solver]. iModIntro.
        (** Getting ready to close the invariant *)
        iDestruct "Hpℓℓₙ" as "[Hpℓℓₙ Hpℓℓₙ']".
        iDestruct "Hcℓₘ" as "[Hcℓₘ Hcℓₘ']".
        iDestruct ("Hwd" $! ((cℓ, true, key) :: llsuf') with
                    "H◯cℓ Hpℓℓₙ' [Hnphysr Hcℓₘ' Hcℓℓₙ' H◯cnℓ]") as "Hphys".
        { iApply (phys_list_aux_cons pk cℓ tℓ llsuf' cℓ true key γn).
          iFrame "Hcℓ Hcℓₘ' Hcislk". repeat iSplit; try done. iFrame. }
        (** Closing the invariant *)
        iMod ("Hclose" with "[Hnodes Hγc● Hremp Hphys]") as "_".
        { iFrame "Hγt Hγc● Hremp Hphys". iSplit.
          * rewrite Hll Hk. by iApply nodes_mark.
          * rewrite Hk in Hll Hnins. rewrite Hll in Hllk. iPureIntro.
            apply (ll_keys_mark cℓ ls llpre llsuf' cm' key); auto. }
        iModIntro.
        (** Since we closed the invariant, many facts have become outdated, so
            we clean up our context a bit. This also allows us to reuse some
            variable names when we open the invariant again. *)
        clear Hll Hleqc Hltk' Hllk Hkin Heq Hcℓnin Hninp Hnins Hleqllp Hpcases'
          Hpcases Hk H H0 H1 key' cm' lk' lkn' ℓℓₙ' ℓₘ' ll ls removed llpre
          llsuf' pm cm pnℓo cnℓo.
        (** We are not done yet, since we still need to
            physically remove the node. *)
        wp_pures. wp_load. repeat wp_lam. wp_load. wp_pures.
        wp_lam. repeat wp_load. wp_lam. wp_pures. repeat wp_lam. wp_load.
        wp_pures.
        (** Open the invariant once more. *)
        wp_bind (_ <- _)%E.
        iInv "HIset" as "Hset" "Hclose".
        (** Get information about the successor of the current node, since this
            is where the predecessor will be updated to point to. *)
        iDestruct (next_node with "Hset [H◯cℓ //] [Hcℓ //] [Hγt //] [//]") as
          (cnℓ' cnℓℓₙ cnℓₘ cnk cnlk) "(>Hcℓℓₙ' & >#H◯cnℓ & >#Hcnℓ & >%Hltcnk & Hwd)".
        iDestruct (pointsto_agree with "Hcℓℓₙ Hcℓℓₙ'") as "%Hcnℓeq".
        inversion Hcnℓeq as [Hk]. rewrite <- Hk. clear Hk Hcnℓeq cnℓ'.
        iDestruct ("Hwd" with "[Hcℓℓₙ' //]") as "Hset".
        iDestruct "Hset" as
          (removed ls ll tℓ')
            "(Hnodes & Hγc● & >Hγt' & >%Hllk & Hphys & Hremp)".
        iCombine "Hγt Hγt'" gives %<-%to_agree_op_valid_L; iClear "Hγt'".
        (** Prepare some facts for the split: *)
        (** Predecessor is either the head or within the list *)
        iDestruct (unmarked_cases with "H◯pℓ Hpℓ Hpℓₘ Hnodes Hphys Hremp")
          as "(Hpℓₘ & Hnodes & Hphys & Hremp & Hpcases)".
        iDestruct "Hpcases" as ">%Hpcases".
        assert (pℓ = hℓ ∨ pℓ ∈ ll_locs ll) as Hpcases'.
        { destruct Hpcases as [Hph | [Hpl | Hpt]].
          - by left.
          - by right.
          - contradiction. }
        iDestruct (phys_list_split with "Hpℓ Hpℓℓₙ [>Hcℓ //] [//] [//] Htℓ Hphys") as
          "(Hpℓℓₙ & %llpre & %llsuf & >%Hll & >%Hleqllp & >%Hcℓnin & Hphysr & Hwd)".
        destruct llsuf as [|[[cℓ' cm'] ck'] llsuf'].
        (** Since we did not physically delete the key yet + hold locks, we
            know that the suffix must still start with the current node. *)
        { iDestruct "Hphysr" as ">->".
          iCombine "Htℓ Hcℓ" gives "[_ %Hheq]". inversion Hheq. }
        iDestruct (loc_nin_suf with "Hcℓ Hcℓℓₙ Hγt Ht Hphysr") as "[[Hphysr Hcℓℓₙ] >%Hnins]".
        wp_store.
        (** Prepare to close the invariant again. *)
        iDestruct "Hpℓℓₙ" as "[Hpℓℓₙ' Hpℓℓₙ]".
        iDestruct (phys_list_aux_cons with "Hphysr") as
          (key' ℓℓₙ' ℓₘ' lk' lkn')
          "(Hcℓ' & <- & <- & %Hltk' &
           (%cnℓ' & Hcℓℓₙ' & Hnphysr & _) & Hcℓₘ' & Hcislk')".
        iCombine "Hcℓ' Hcℓ" gives "[_ %Heq]". inversion Heq.
        iClear "Hcℓ' Hcislk'".
        iDestruct (pointsto_agree with "Hcℓℓₙ Hcℓℓₙ'") as "%Hcnℓeq".
        iCombine "Hcℓℓₙ Hcℓℓₙ'" as "Hcℓℓₙ". rewrite dfrac_op_own Qp.half_half.
        (** cℓ cannot be in removed, otherwise we would have a fraction > 1 *)
        iAssert (⌜ cℓ ∉ removed ⌝%I) as "%Hcℓnrem".
        { iIntros "%Hin".
          iPoseProof (big_sepS_elem_of_acc _ _ _ Hin  with "Hremp")
            as "[Hperm Hwand]".
          iDestruct "Hperm" as
            (ck' cℓℓₙ' cℓₘ' clk' clkn')
            "[Hcℓ' ((%nℓ & %nℓℓₙ & %nℓₘ & %nk & %nlk & Hcℓℓₙ' & _) & _ & _)]".
          iCombine "Hcℓ' Hcℓ" gives "[_ %Hceq]". inversion Hceq.
          iCombine "Hcℓℓₙ Hcℓℓₙ'" gives %[Hperm _].
          by rewrite dfrac_op_own dfrac_valid_own in Hperm. }
        iDestruct "Hcℓℓₙ" as "[Hcℓℓₙ' Hcℓℓₙ]".
        inversion Hcnℓeq as [Heqcnℓ]. rewrite <- Heqcnℓ.
        iDestruct (pointsto_agree with "Hcℓₘ Hcℓₘ'") as "%Hcmeq".
        inversion Hcmeq as [Heqcm]. rewrite <- Heqcm in Hll.
        iDestruct (weaken_lb _ _ _ _ _ _$! Hltk with "Hnphysr") as "Hnphysr".
        iDestruct ("Hwd" $! llsuf' cnℓ with "H◯cnℓ Hpℓℓₙ' Hnphysr") as "Hphys".
        (** Move node to removed set *)
        iMod (pointsto_persist with "Hcℓₘ'") as "Hcℓₘ'".
        iDestruct (removed_add with "[//] Hcℓ Hcislk Hcℓℓₙ' Hcℓₘ' H◯cnℓ Hcnℓ [//] Hremp") as "Hremp".
        rewrite Hll.
        iDestruct (nodes_remove with "[] [] [//] Hnodes") as "Hnodes".
        1, 2 : done.
        (** Close the invariant again *)
        iMod ("Hclose" with "[Hnodes Hγc● Hremp Hphys]") as "_".
        { iFrame "Hnodes Hγc● Hγt Hphys Hremp".
          iPureIntro. rewrite Hll in Hllk.
          by apply (ll_keys_remove _ _ _ cℓ key'). }
        iModIntro.
        wp_pures. wp_load.
        (** Unlock the nodes and return true, since we removed the key. *)
        wp_apply (unlock_node_spec with "[$Hcℓ $Hcislk Hcℓℓₙ Hcℓₘ $Hclkd]") as "_".
        { iFrame "Hcℓℓₙ Hcℓₘ". }
        wp_pures. wp_load.
        wp_apply (unlock_node_spec with "[$Hpℓ $Hpislk Hpℓℓₙ Hpℓₘ $Hplkd]") as "_".
        { (* iFrame cannot figure out that lopt#(Some cnℓ) is the same as
             InjLV #cnℓ, so we manually use iExists. *)
          iExists (Some cnℓ), false. iFrame "Hpℓℓₙ Hpℓₘ". }
        wp_pures. iApply "Hret".
      + (** Key is not in the set - we do not need to remove anything.
            However, we still need to choose a linearization point. *)
        (** Since the current node is not the key we were looking for,
            and walk2 guarantees that the key is less than or equal than the
            current node, we know that the key must be strictly less than the
            current node. *)
        pose proof (leq_neq_lt (Fin key) ck Hleqc Hneq) as Hltc.
        wp_apply (eqv_neq_fin $! Hneq) as "_".
        wp_pures. wp_bind (!_)%E.
        (** We choose this as a linearization point, since we can bind the load
            to open the invariant and atomic update. *)
        iInv "HIset" as "Hset" "Hclose".
        (** We split the list so we can more easily prove that the key is
            not in the list. *)
        iDestruct "Hset" as
          (removed ls' ll tℓ')
            "(Hnodes & Hγc● & >Hγt' & >%Hllk & Hphys & Hremp)".
        iCombine "Hγt Hγt'" gives %<-%to_agree_op_valid_L; iClear "Hγt'".
        (** Prepare some facts for the split: *)
        (** Predecessor is either the head or within the list *)
        iDestruct (unmarked_cases with "H◯pℓ Hpℓ Hpℓₘ Hnodes Hphys Hremp")
          as "(Hpℓₘ & Hnodes & Hphys & Hremp & Hpcases)".
        iDestruct "Hpcases" as ">%Hpcases".
        assert (pℓ = hℓ ∨ pℓ ∈ ll_locs ll) as Hpcases'.
        { destruct Hpcases as [Hph | [Hpl | Hpt]].
          - by left.
          - by right.
          - contradiction. }
        (** The predecessor key is strictly less than the current key. *)
        assert (lt pk ck) as Hlt.
        { eapply lt_leq_trans; done. }
        iDestruct (phys_list_split with "Hpℓ Hpℓℓₙ [>Hcℓ //] [//] [//] Htℓ Hphys") as
          "(Hpℓℓₙ & %llpre & %llsuf & >%Hll & >%Hleqllp & >%Hcℓnin & Hphysr & Hwd)".
        (** Open the atomic update. *)
        iMod "AU" as (ls) "[Hγc◯ [_ Hclose']]".
        wp_load.  (* Getting rid of the laters to make our lifes easier *)
        iDestruct (eauth_agree with "Hγc● Hγc◯") as %->.
        (** Since we opened the invariant, we can state that the key was not in
            the list/set. *)
        iAssert (⌜ key ∉ ll_keys ll ⌝%I) as "%Hnin".
        { iIntros "%Hin".
          rewrite Hll ll_keys_app elem_of_union in Hin.
          destruct Hin as [Hinpre|Hinpresuf].
          - (** Key is not in the prefix *)
            pose proof (Hleqllp key Hinpre) as Hleq.
            rewrite /leq in Hleq. rewrite /lt in Hltk.
            destruct pk; lia.
          - (** Key is not in the suffix *)
            iDestruct (update_lb _ _ _ _ _ _ _ (Fin key) with "Hcℓ [//] Hphysr") as "Hphysr".
            iDestruct (gt_lb with "[] Hphysr") as "%Hbad".
            { iPureIntro.
              eapply elem_of_weaken. apply Hinpresuf. apply ll_keys_subset. }
            rewrite /lt in Hbad. lia. }
        (** Restore Hphys *)
        iDestruct "Hpℓℓₙ" as "[Hpℓℓₙ' Hpℓℓₙ]".
        iDestruct ("Hwd" $! llsuf cℓ with "H◯cℓ Hpℓℓₙ Hphysr") as "Hphys".
        rewrite <- Hll.
        (** Close the atomic update and the invariant. *)
        iMod ("Hclose'" with "[Hγc◯]") as "Hret".
        { by (replace (ls ∖ {[key]}) with ls by set_solver). }
        rewrite bool_decide_eq_false_2; [| set_solver]. iModIntro.
        iMod ("Hclose" with "[Hnodes Hγc● Hremp Hphys]") as "_".
        { iFrame "∗ # %". }
        iModIntro.
        (** Unlock the nodes and return false, since we did not remove
            anything. *)
        wp_apply (unlock_node_spec with
                   "[$Hcℓ $Hcislk Hcℓℓₙ Hcℓₘ $Hclkd]") as "_".
        { iFrame "Hcℓℓₙ Hcℓₘ". }
        wp_pures. wp_load.
        wp_apply (unlock_node_spec with
                   "[$Hpℓ $Hpislk Hpℓℓₙ' Hpℓₘ $Hplkd]") as "_".
        { (* iFrame cannot figure out that lopt#(Some cℓ) is the same as
             InjLV #cℓ, so we manually use iExists. *)
          iExists (Some cℓ), false. iFrame "Hpℓℓₙ' Hpℓₘ". }
        wp_pures. iApply "Hret".
    - (** Validate was unsuccessful; unlock the nodes and retry *)
      wp_pures. wp_load.
      wp_apply (unlock_node_spec with "[$Hcℓ $Hcislk Hcℓℓₙ Hcℓₘ $Hclkd]") as "_".
      { iFrame "Hcℓℓₙ Hcℓₘ". }
      wp_pures. wp_load.
      wp_apply (unlock_node_spec with "[$Hpℓ $Hpislk Hpℓℓₙ Hpℓₘ $Hplkd]") as "_".
      { iFrame "Hpℓℓₙ Hpℓₘ". }
      wp_pures. iApply ("HIadd" with "AU").
  Qed.

  Lemma contains_spec (hℓ : loc) (γn : gname) (γc : gname) (γt : gname) (key : Z) :
    is_set hℓ γn γc γt -∗
    <<{ ∀∀ (ls : gset Z), set_content γc ls }>>
      contains #hℓ extZ#(Fin key) @ ↑N
    <<{ set_content γc ls | RET #(bool_decide (key ∈ ls)) }>>.
  Proof.
  (** According to the paper, an unsuccessful [contains] call is linearized
      either at the point where a removed entry is found, or right before a new
      matching entry is added to the list - whichever occurs earlier.

      Since Iris does support "helping", meaning one thread executes the
      linearization point of another thread, it is probably possible to modify
      the invariant somehow and prove contains correct. However, it is out of
      scope for this project. *)
  Admitted.

End hllbs.

(** * Conclusion **************************************************************)

(** We have implemented the data structure in
    "A Lazy Concurrent List-Based Set Algorithm" by Heller et al.,
    and its methods in HeapLang, defined logically atomic specifications for
    adding a key, removing a key, and checking whether a key is contained in the
    set, and proved that the implementations of add, and remove, satisfy those
    specifications.

    For future work, we see two interesting directions:

    1. Proving the correctness of contains

       As mentioned before, the linearization point of an unsuccessful contains
       call is not trivial, and would likely require changes to the invariant
       to support "helping". An example of "helping" can be found in the Iris
       examples repository in the context of the Herlihy & Wing Queue.

    2. Maintaining less global information

       Our invariant contains a set of all allocated nodes, and conceptually
       splits them up in different groups (e.g., removed or reachable from the
       head). In particular, we have some kind of indirection: instead of
       directly being able to do a case distinction on the state of the node,
       we need to use the helper lemma [node_cases]. This makes it a bit tedious
       to work with.

       It may be possible to simplify the proofs by instead maintaining more
       "local" information. It is not immediately clear how this would work
       though; initial attempts to nest invariants, where an invariant on the
       entire data structure would mention invariants on the node, did not work
       out, as they essentially constrained the data structure to
       be read-only. *)

(** * Acknowledgements ********************************************************)

(** I would like to thank Isaac van Bakel and Prof. Dr. Ralf Jung for
    selecting and supervising the project. While the formalization ended up
    being more tricky than we expected, I ended up learning a lot, which would
    not have been possible with out their support.

    I would also like to thank my friend Rudy Peterson, who was always open
    to discussions regarding Coq, Iris and this data structure.

    Last, but not least, I would like to thank everyone on the Iris Mattermost
    who answered my questions and helped me understand a bit more Iris :) *)
