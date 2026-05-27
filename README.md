# MeTTa Disjoint Set & Conjunction Checker

A **Union-Find (DSU)** implementation in MeTTa using pure-functional rewrite rules and pattern matching.

## What It Does

### Part 1 — Disjoint Set Checker
Given a collection of tuples, determines if the collection is **disjoint** (has isolated islands) or **fully connected** (every tuple is reachable from every other through shared elements).

### Part 2 — Disjoint Conjunction Checker
Same logic applied to logical conjuncts represented as `(= Var Val)` tuples. Connectivity is determined by shared **variable names**.

## Running

```bash
# With MeTTa interpreter
metta disjoint_set_checker.metta

# With PeTTa (Prolog-based MeTTa compiler)
# Follow your PeTTa setup instructions to load the file
```

## Expected Output

```
true     ; ((11 12 13 14) is isolated)
false    ; (all connected: 1-2, 2-3, 3-4)
false    ; (single tuple)
true     ; ((eq Color Red) shares no variable)
false    ; (all connected via shared vars A, B, C)
```

## Structure

Each predicate does exactly one thing:

| Predicate | Role |
|---|---|
| `member` | Element existence check |
| `has-common` | Shared element check between tuples |
| `union-step` | Insert tuple into group list |
| `union-all` | Fold all tuples into groups |
| `merge-groups` | Pure-functional fixpoint merge |
| `is-disjoint` | Final verdict (Part 1) |
| `get-var` / `get-vars` | Variable extraction from `(= Var Val)` |
| `is-disjoint-conjuncts` | Final verdict (Part 2) |
