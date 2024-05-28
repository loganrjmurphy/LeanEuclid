## Semantic Evaluation of Autoformalized Theorem Statements

`E3` (Euclidean Equivalence Engine) is a tool for rigorously analyzing autoformalized theorem statements targeting LeanEuclid. It is built on top of the same SMT-based reasoners as LeanEuclid's proof automation. 

While `E3` can be used in an *ad hoc* manner, we also provide a Python wrapper for feeding batches of autoformalized theorem statements directly into `E3` for processing. See [here](https://github.com/loganrjmurphy/LeanEuclid/tree/master/AutoFormalization) for more usage details.

### Setup

From the root directory of LeanEuclid, run `lake build E3`.

### Overview 

In general, `E3` takes two Lean expressions as input: the autoformalized theorem statement (`test`) and the ground truth theorem statement (`ground`). The formula `test` must be a well-formed statement in the formal system E (see paper for details).

E3 will return an object of type `E3Result`, which has the following fields:

 - `bvars` : A summary of any differences in the number and types of bound variables (points, lines, circles) between `test` and `ground`.
 - `binary_check` : The result of the standard (binary) equivalence checker, which will be one of four results: 
    - `equiv`, meaning `test` and `ground` were proven equivalent
    - `ground_imp_test`, meaning the autoformalized proposition was found to weaker than the ground truth (i.e., `ground ==> test` was proven but `test ==> ground` could not be proven)
    - `test_imp_ground`, which is the reverse of `ground_imp_test`,
    - `no_conclusion`, which means neither direction of the `iff` could be proven.
 - `approx_check` : The result of the approximate equivalence checking. This will be a list of unifications of the bound variables in `test` and `ground`, as well as the number of proof obligations that could be solved under each unification. In the approximate equivalence checker, we compare the preconditions (LHS) and postconditions (RHS) of the formulae seperately, and there are two directions of the `iff` ("fwd" and "bwd") so these results are split between four locations (i.e., `fwdLHS`, `fwdRHS`, `bwdLHS`, `bwdRHS`).

#### Bound Variable Delta's
An entry in `bvars` for which each field is zero, such as 

```
   "bvars" : {"uPoints": 0, "uLines": 0,"uCircles": 0, "ePoints": 0,"eLines": 0, "eCircles": 0} 
```
means that the quantity and types of the bound variables in `test` and `ground` are the same. This is required for approximate equivalence checking to be applicable to a formalization instance.

A nonzero entry in `bvars` indicates a disagreement about bound variables. Positive numbers mean "`test` has too many of these", and negative numbers mean "`test` has too few of these" relative to `ground`.

For instance, a result like
```
   "bvars" : {"uPoints": 2, "uLines": 0,"uCircles": 0, "ePoints": 0,"eLines": -1, "eCircles": 0}
```
means that `test` has two more points under a universal quantifier, and one fewer lines under an existential quantifier, relative to `ground`.

#### Approximate Equivalence Results 

Consider the following instances of `ground` and `test` (Euclid, Prop.13):

```lean
def ground : Prop := ∀ (a b c d : Point) (AB CD : Line), AB ≠ CD ∧ distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ between d b c → ∠ c:b:a + ∠ a:b:d = ∟ + ∟

def test : Prop := ∀ (a b c d : Point) (AB CD : Line), distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ b.onLine CD → (∠ c:b:a + ∠ a:b:d = ∟ + ∟)
```
The formalization is close, but not quite correct. In this case, the names of all bound variables match, so it is easy to compare the two formulae by associating each bound variable in `ground` with a unique partner in `test`, and under this reading `ground` looks stronger. But can we quantify how much stronger it is? Are there other possible unifications of bound variables that might be better? And what about more complex propositions? 

To systematize this kind of evaluation, we can use `E3`'s approximate equivalence checker. When executed on this instance, it will produce something like the following: 
```
 "approx_check" : 
   [
      {"permutation_1" : {"bvar_map" : ["c ↦ c", "f ↦ f", "b ↦ b", "AB ↦ AB", "a ↦ a", "AC ↦ AC"], 
         "fwdLHS" : {"solved" : 7, "total" : 7}, "bwdLHS" : {"solved" : 7, "total" : 7}, 
         "fwdRHS" : {"solved" : 2, "total" : 2}, "bwdRHS" : {"solved" : 2, "total" : 2}}} 
      
      {"permutation_2" : {"bvar_map" : ["c ↦ c", "f ↦ f", "b ↦ b", "AB ↦ AC", "a ↦ a", "AC ↦ AB"], 
         "fwdLHS" : {"solved" : 5, "total" : 7}, "bwdLHS" : {"solved" : 5, "total" : 7}, 
         "fwdRHS" : {"solved" : 2, "total" : 2}, "bwdRHS" : {"solved" : 2, "total" : 2}}}, 

    ]
```
This result shows two different unifications of bound variables in `test` and `ground`: the natural one (`permutation_1`) and one in which `AC` and `BC` are swapped (`permutation_2`). For each unification, we extract the corresponding instantiations of the preconditions (LHS) and postconditions (RHS) of both formulae, allowing us to get rid of the quantifiers and focus on the propositional clauses themselves. We then perform four rounds of solving:

1. `fwdLHS` : do the preconditions of `ground` imply the preconditions of `test`?
2. `bwdLHS` : do the preconditions of `test` imply the preconditions of `ground`?
3. `fwdRHS` : do the postconditions of `ground` imply the preconditions of `test`?
4. `bwdRHS` : do the preconditions of `test` imply the preconditions of `ground`?

For each of these rounds, we record the number of proof obligations which are actually proven; these are the numbers shown in the result. In this particular example, we can see that `permutation_2` is a strictly worse choice than the natural unification. However, this is not always the case!

#### Choosing unifications of bound variables

As part of approximate equivalence checking, we choose a particular unification of bound variables with which we can instantiate the quantifiers. Obviously, the number of possible unifications is factorial in the number of variables, so it's infeasible to check each candidate. Instead, we choose the best `N` unifications, as measured by a string similarity heuristic. That is, let `p` be a mapping of bound variables in `test` to bound variables in `ground`. We say that candidate unification `p` is "better" than another candidate `p'` if `sim(test[p], ground) > sim(test[p'], ground)`, where `dist` is a string similarity metric (default is the Levenshtein ratio). So `E3` will only check the best `N` unifications as chosen by this heuristic. This is obviously not guaranteed to be optimal, but in our experience it is a useful compromise.

For many of the formalizations in LeanEuclid, there are few enough bound variables that we can enumerate all the possible candidate unifications and find the best `N`. However, there are also some cases where there are so many candidates (e.g., several hundred million) that this process becomes too time-consuming for some use cases. By default, we provide a builtin ceiling on the number of candidates we will sample before choosing the best `N`. This is configured by the following parameters in `choosePerms.py`:

```python
SHORTCIRCUIT_THRESHOLD = 4000000
SHORTCIRCUIT_SAMPLE_THRESHOLD = 0.88
SHORTCIRCUIT_SAMPLE_CUTOFF = 50
```
Which is interpeted as follows: if there are more than `SHORTCIRCUIT_THRESHOLD` candidates, we will only search the candidate space until we have seen at least `SHORTCIRCUIT_SAMPLE_CUTOFF` whose similarity metric is at least `SHORTCIRCUIT_SAMPLE_THRESHOLD`. In our experience, these parameters seem to be a reasonable compromise, but mileage may vary. Note that none of the instances of approximate equivalence checking mentioned in the paper required short-circuiting the heuristic. 


### Running `E3` by hand 

Usually we invoke `E3` using the Python wrapper as explained See [here](https://github.com/loganrjmurphy/LeanEuclid/tree/master/AutoFormalization), but it can also be invoked direclty.

To invoke `E3` manually, create a fill `foo.lean` with the following format: 

```lean
def ground_expr : Expr := q({ground})
def test_expr : Expr := q({test})

def main (args : List String) : IO Unit := do 
    let xs ← parseArgs args
    runE3fromIO groundE testE xs
```
Where `{ground}` and `{test}` are the formulae being compared, e.g.,

For example: 
```lean
def groundE : Expr := q(∀ (a b : Point) (AB : Line), distinctPointsOnLine a b AB → ∃ c : Point, |(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)|)
def testE : Expr := q(∀ (a b : Point) (AB : Line), distinctPointsOnLine a b AB → ∃ (c : Point) (AC BC : Line), distinctPointsOnLine a c AC ∧ distinctPointsOnLine b c BC ∧ |(a─b)| = |(a─c)| ∧ |(a─c)| = |(b─c)|)
```

The checker can then be run from CLI as

```
lake env lean --run path/to/file.lean <name> <mode> <nPerms> <equivTime> <approxTime> <writeResult> <outputDir> 
```

Alternatively, you can run the same thing from within the `.lean` file itself by running the command `#eval main [<arg1>, <arg2>, ... <argn>]`

The configuration options are as follows; 

 - `name : String`, an identifier for the evaluation instance, used for filenames etc.
 - `mode : String`, one of the following: 
     - "bvars"      => only check whether the bound variables of the two formulae match
     - "skipApprox" => only run the standard equivalence checking (default)
     - "onlyApprox" => only run the approximate equivalence checking
     - "full"       => run both analyses
 - `nPerms : Nat`, the number of distinct unifications (i.e., permutations) of bound variables to attempt during approximate equivalence checking (default=3).
 - `equivTime : Nat`, the number of seconds given to the solvers to prove each direction of the `iff` during standard equivalence checking  (default=15).
 - `approxTime : Nat`, the number of seconds given to the solvers to prove each *clause* during approximate equivalence checking (default=5).
 - `writeResult : bool`, whether or not to write the output to a file. When `E3` is invoked manually from within Lean, if `writeResult=false` then the output will be traced to `stdout`. 
 - `outputDir : String` (optional), name of file in which to write the output.
