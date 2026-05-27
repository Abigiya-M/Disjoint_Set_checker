;; ============================================================================
;; MeTTa Disjoint Set & Conjunction Checker
;; ============================================================================
;;
;; How Union-Find Maps to MeTTa's Rewrite Model
;; ---------------------------------------------
;; In imperative Union-Find, mutable parent arrays track which component each
;; element belongs to. In MeTTa, we have no mutable state — instead we use
;; pure-functional group merging driven by rewrite rules:
;;
;;   1. INITIALIZATION: Each tuple becomes its own singleton group.
;;      A list of tuples (A B C) becomes a list of groups (A B C),
;;      where each group is a list containing one tuple.
;;
;;   2. UNION (union-step): Process each tuple against the existing groups.
;;      For each group, we flatten it and check for shared elements with
;;      the new tuple. If found, merge by prepending the tuple to that group.
;;      If no match, add a new singleton group.
;;
;;   3. FIXPOINT (merge-groups): After the initial fold, some groups that were
;;      created separately may now be transitively connected. We run merge-pass
;;      repeatedly, comparing the result to the input via structural equality.
;;      When old == new, we've reached a fixpoint — no more merges possible.
;;      This is pure functional: no mutable state, just recursion and comparison.
;;
;;   4. VERDICT: Count the groups. More than one group means disjoint (True).
;;      Exactly one group means fully connected (False).
;;
;; Each predicate below does exactly one thing. Recursion replaces loops.
;; car-atom/cdr-atom/cons-atom provide list deconstruction/construction.
;; Rewrite rules (=) define each predicate.
;;


;; ============================================================================
;; PART 1 — Disjoint Set Checker (raw elements)
;; ============================================================================

;; ----------------------------------------------------------------------------
;; elem: Check if element $x exists in a list.
;; Named 'elem' to avoid conflict with Prolog's built-in 'member'.
;; Walks the list via car-atom/cdr-atom until found or empty.
;; ----------------------------------------------------------------------------
(= (elem $x $list)
   (if (== $list ())
       False
       (if (== $x (car-atom $list))
           True
           (elem $x (cdr-atom $list)))))

;; ----------------------------------------------------------------------------
;; has-common: Check if two lists share at least one element.
;; Walks the first list, calling elem on each element against the second.
;; Returns True as soon as a shared element is found.
;; ----------------------------------------------------------------------------
(= (has-common $list1 $list2)
   (if (== $list1 ())
       False
       (if (== (elem (car-atom $list1) $list2) True)
           True
           (has-common (cdr-atom $list1) $list2))))

;; ----------------------------------------------------------------------------
;; join: Concatenate two lists into one.
;; Walks the first list, prepending each element onto the result of
;; joining the remainder with the second list.
;; ----------------------------------------------------------------------------
(= (join $xs $ys)
   (if (== $xs ())
       $ys
       (cons-atom (car-atom $xs) (join (cdr-atom $xs) $ys))))

;; ----------------------------------------------------------------------------
;; flatten-group: Flatten a group (list of tuples) into a single flat list
;; of all elements. Used to check if two groups share elements.
;; ----------------------------------------------------------------------------
(= (flatten-group $group)
   (if (== $group ())
       ()
       (join (car-atom $group) (flatten-group (cdr-atom $group)))))

;; ----------------------------------------------------------------------------
;; union-step: Insert a tuple into the group list.
;; Scans groups left-to-right. If the tuple shares an element with a group
;; (checked via flattening), merge by prepending the tuple into that group.
;; Otherwise, recurse to the next group. If no group matches, create new.
;; ----------------------------------------------------------------------------
(= (union-step $tuple $groups)
   (if (== $groups ())
       (cons-atom (cons-atom $tuple ()) ())
       (if (== (has-common $tuple (flatten-group (car-atom $groups))) True)
           (cons-atom (cons-atom $tuple (car-atom $groups)) (cdr-atom $groups))
           (cons-atom (car-atom $groups) (union-step $tuple (cdr-atom $groups))))))

;; ----------------------------------------------------------------------------
;; union-all: Fold all tuples into groups using union-step.
;; Processes tuples one at a time, building the group list.
;; ----------------------------------------------------------------------------
(= (union-all $tuples $groups)
   (if (== $tuples ())
       $groups
       (union-all (cdr-atom $tuples) (union-step (car-atom $tuples) $groups))))

;; ----------------------------------------------------------------------------
;; groups-share: Check if two groups (lists of tuples) share any element.
;; Flattens both groups and checks for common elements.
;; ----------------------------------------------------------------------------
(= (groups-share $g1 $g2)
   (has-common (flatten-group $g1) (flatten-group $g2)))

;; ----------------------------------------------------------------------------
;; merge-into: Merge a single group into a list of groups.
;; If it shares elements with an existing group, combine them via join.
;; Otherwise, join as a separate group at the end.
;; ----------------------------------------------------------------------------
(= (merge-into $group $groups)
   (if (== $groups ())
       (cons-atom $group ())
       (if (== (groups-share $group (car-atom $groups)) True)
           (cons-atom (join $group (car-atom $groups)) (cdr-atom $groups))
           (cons-atom (car-atom $groups) (merge-into $group (cdr-atom $groups))))))

;; ----------------------------------------------------------------------------
;; merge-pass: One pass over the group list, attempting to merge each group
;; into the accumulator. Returns the resulting group list.
;; ----------------------------------------------------------------------------
(= (merge-pass $groups $acc)
   (if (== $groups ())
       $acc
       (merge-pass (cdr-atom $groups) (merge-into (car-atom $groups) $acc))))

;; ----------------------------------------------------------------------------
;; merge-groups: Pure-functional fixpoint.
;; Runs merge-pass, then compares old vs new via structural equality.
;; If identical, the fixpoint is reached — return. If different, recurse.
;; No mutable state — convergence is detected by structural equality.
;; ----------------------------------------------------------------------------
(= (merge-groups $groups)
   (let $new (merge-pass $groups ())
     (if (== $new $groups)
         $groups
         (merge-groups $new))))

;; ----------------------------------------------------------------------------
;; count: Count the number of elements in a list.
;; ----------------------------------------------------------------------------
(= (count $list)
   (if (== $list ())
       0
       (+ 1 (count (cdr-atom $list)))))

;; ----------------------------------------------------------------------------
;; is-disjoint: Final verdict for Part 1.
;; Builds groups from tuples, merges to fixpoint, then checks count.
;; True  = disjoint (isolated islands exist)
;; False = fully connected (one single component)
;; ----------------------------------------------------------------------------
(= (is-disjoint $tuples)
   (let $groups (merge-groups (union-all $tuples ()))
     (if (> (count $groups) 1)
         True
         False)))


;; ============================================================================
;; PART 2 — Disjoint Conjunction Checker (logical conjuncts)
;; ============================================================================
;;
;; Design Decision: Conjunct Representation
;; -----------------------------------------
;; MeTTa treats State=NY as a single opaque symbol — there is no built-in
;; way to split on the '=' character. We also cannot use (= Var Val) because
;; MeTTa/PeTTa interprets '=' as a rewrite rule definition, not data.
;; Instead, we use the inert symbol 'eq' to represent conjuncts:
;;
;;   (eq State NY)    instead of    State=NY
;;
;; This makes variable extraction trivial: get-var returns the second
;; element of the (eq Var Val) structure via car-atom/cdr-atom.
;;
;; A conjunction tuple like (Age=25 State=NY) becomes:
;;   ((eq Age 25) (eq State NY))
;;

;; ----------------------------------------------------------------------------
;; get-var: Extract the variable name from a structured conjunct (eq Var Val).
;; Uses car-atom on cdr-atom to skip past 'eq' and get the variable name.
;; ----------------------------------------------------------------------------
(= (get-var $conjunct)
   (car-atom (cdr-atom $conjunct)))

;; ----------------------------------------------------------------------------
;; get-vars: Collect all variable names from a conjunction tuple.
;; Maps get-var over each conjunct in the tuple.
;; ----------------------------------------------------------------------------
(= (get-vars $tuple)
   (if (== $tuple ())
       ()
       (cons-atom (get-var (car-atom $tuple)) (get-vars (cdr-atom $tuple)))))

;; ----------------------------------------------------------------------------
;; has-common-var: Check if two conjunction tuples share a variable name.
;; Extracts variables from both, then checks for common elements.
;; ----------------------------------------------------------------------------
(= (has-common-var $t1 $t2)
   (has-common (get-vars $t1) (get-vars $t2)))

;; ----------------------------------------------------------------------------
;; flatten-group-conj: Flatten a group of conjunction tuples into one list
;; of all conjuncts. Used to check variable overlap between groups.
;; ----------------------------------------------------------------------------
(= (flatten-group-conj $group)
   (if (== $group ())
       ()
       (join (car-atom $group) (flatten-group-conj (cdr-atom $group)))))

;; ----------------------------------------------------------------------------
;; groups-share-var: Check if two groups of conjunction tuples share any
;; variable. Flattens both groups and checks for common variables.
;; ----------------------------------------------------------------------------
(= (groups-share-var $g1 $g2)
   (has-common-var (flatten-group-conj $g1) (flatten-group-conj $g2)))

;; ----------------------------------------------------------------------------
;; union-step-conj: Insert a conjunction tuple into the group list.
;; Same logic as union-step, but uses has-common-var for connectivity.
;; ----------------------------------------------------------------------------
(= (union-step-conj $tuple $groups)
   (if (== $groups ())
       (cons-atom (cons-atom $tuple ()) ())
       (if (== (has-common-var $tuple (flatten-group-conj (car-atom $groups))) True)
           (cons-atom (cons-atom $tuple (car-atom $groups)) (cdr-atom $groups))
           (cons-atom (car-atom $groups) (union-step-conj $tuple (cdr-atom $groups))))))

;; ----------------------------------------------------------------------------
;; union-all-conj: Fold all conjunction tuples into groups.
;; ----------------------------------------------------------------------------
(= (union-all-conj $tuples $groups)
   (if (== $tuples ())
       $groups
       (union-all-conj (cdr-atom $tuples) (union-step-conj (car-atom $tuples) $groups))))

;; ----------------------------------------------------------------------------
;; merge-into-conj: Merge a single group into a list of groups using
;; variable-based connectivity.
;; ----------------------------------------------------------------------------
(= (merge-into-conj $group $groups)
   (if (== $groups ())
       (cons-atom $group ())
       (if (== (groups-share-var $group (car-atom $groups)) True)
           (cons-atom (join $group (car-atom $groups)) (cdr-atom $groups))
           (cons-atom (car-atom $groups) (merge-into-conj $group (cdr-atom $groups))))))

;; ----------------------------------------------------------------------------
;; merge-pass-conj: One pass over conjunction groups, merging where possible.
;; ----------------------------------------------------------------------------
(= (merge-pass-conj $groups $acc)
   (if (== $groups ())
       $acc
       (merge-pass-conj (cdr-atom $groups) (merge-into-conj (car-atom $groups) $acc))))

;; ----------------------------------------------------------------------------
;; merge-groups-conj: Pure-functional fixpoint for conjunction groups.
;; Compares before and after each pass. Stops when no change occurs.
;; ----------------------------------------------------------------------------
(= (merge-groups-conj $groups)
   (let $new (merge-pass-conj $groups ())
     (if (== $new $groups)
         $groups
         (merge-groups-conj $new))))

;; ----------------------------------------------------------------------------
;; is-disjoint-conjuncts: Final verdict for Part 2.
;; True  = disjoint (isolated conjunction groups exist)
;; False = fully connected (all conjunctions share variables transitively)
;; ----------------------------------------------------------------------------
(= (is-disjoint-conjuncts $tuples)
   (let $groups (merge-groups-conj (union-all-conj $tuples ()))
     (if (> (count $groups) 1)
         True
         False)))


;; ============================================================================
;; TEST CASES
;; ============================================================================

;; --- Part 1: Disjoint Set Checker ---

;; Test 1: Disjoint — (11 12 13 14) is an isolated island
;; Expected: True
!(is-disjoint ((2 3 4) (1 2) (11 12 13 14) (2 1 5) (5 6 7)))

;; Test 2: Connected — all tuples share elements transitively
;; Expected: False
!(is-disjoint ((1 2) (2 3) (3 4)))

;; Test 3: Single tuple — trivially one group
;; Expected: False
!(is-disjoint ((1 2 3)))

;; --- Part 2: Disjoint Conjunction Checker ---

;; Test 4: Disjoint — (eq Color Red) shares no variable with others
;; Expected: True
!(is-disjoint-conjuncts (((eq Age 25) (eq State NY)) ((eq State NY) (eq Income 50k)) ((eq Color Red))))

;; Test 5: Connected — all conjunctions share variables transitively (A-B-C-A)
;; Expected: False
!(is-disjoint-conjuncts (((eq A 1) (eq B 2)) ((eq B 3) (eq C 4)) ((eq C 5) (eq A 6))))
