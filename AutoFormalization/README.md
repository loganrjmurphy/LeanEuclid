## AutoFormalization with LeanEuclid

This folder contains a Python wrapper to autoformalize theorem statements and proofs from LeanEuclid, and the automatically evaluate the results. For details on how the equivalence checker works and how to interpret its results, please see [here](https://github.com/loganrjmurphy/LeanEuclid/tree/master/E3).

We currently use the OpenAI API for autoformalization, but it should be straightforward to plug any LLM into the wrapper.

### Setup 
Make sure that your OpenAI API key is registered as an environment variable, or you can supply it explicitly in `AutoFormalization/utils.py`. Also make sure that LeanEuclid is in your Python path.

### Choosing a Dataset 
We will provide some usage examples targeting the *Elements* dataset. To target UniGeo instead, replace any instances of the arguments `--dataset Book --category ""` with `--dataset UniGeo --category <cat>`, where `<cat>` is one of `{"Parallel","Triangle","Quadrilateral","Congruent","Similarity"}`.

### Autoformalizing Theorem Statements


To autoformalize theorem statements from *Elements*, go to the root directory of LeanEuclid and run 

```
python3 AutoFormalization/statement/autoformalize.py --dataset Book --category "" --reasoning text-only --num_query 1 --num_examples 3
```

The arguments `--dataset Book` and `--category ""` indicate that we are formalizing all 43 propositions in the test set of *Elements*. The argument `--num_query` indicates the number of chances the model is given to produce a well-formed Lean expression (of course, specifying `num_query=1` means that some propositions may not be formalized this round). The argument `num-examples` indicates the number of "shots" to be included in the prompt.

Autoformalizing the 43 propositions in the testing set of *Elements* as above should take roughly 6 minutes and ~100K tokens. 

The results can be found from the root directory under `results`, under the subdirectories associated with the round's configuration options (in this case, `result/statement/Book/text-only/3shot`). The result for Proposition 1 may look something like: 

```
{"prediction": "∀ (a b : Point) (AB : Line), distinctPointsOnLine a b AB → ∃ (c : Point) (AC BC : Line), distinctPointsOnLine a c AC ∧ distinctPointsOnLine b c BC ∧ |(a─b)| = |(a─c)| ∧ |(a─c)| = |(b─c)|", 
 "groud_truth": "∀ (a b : Point) (AB : Line), distinctPointsOnLine a b AB → ∃ c : Point, |(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)|"}
```

### Evaluating Autoformalized Theorem Statements 

Before you run any evaluation scripts for theorem statements, make sure you run `lake build E3` to build the equivalence checker.

#### Standard Equivalence Checking
Once you've formalized a set of theoerem statements, you can use our equivalence checker `E3` to logically evaluate them in batch against the ground truth theorems in LeanEuclid. 

For instance, to evaluate the theorems formalized from the previous example, go to the root directory of LeanEuclid and run: 

```
python3 AutoFormalization/statement/evaluate.py --dataset Book --category "" --reasoning text-only --num_examples 3
```

The default configuration of the script uses the standard equivalence checking procedure (skipping the more expensive approximate equivalence checking) and allocates 15 seconds to prove each direction of the equivalence. In the experiments reported in the paper, we used 60 second timeouts. For the 43 theorems in *Elements*, using 15-second timeouts takes about 15 minutes on a standard laptop.

The results will, in this case, reside in `result/equivalence/Book/text-only/3shot`. 

#### Approximate Equivalence Checking 

The approximate equivalence checker tries to quantify how "close" an autoformalized theorem statement is to some ground truth formalization. It is slower than the ordinary equivalence checker, so it is not enabled by default. 

To enable the approximate equivalence checker, you can provide an additional argument `mode` to the checker. Providing the argument "onlyApprox" will skip the standard equivalence checking and only execute the approximate analysis. Providing the argument "full" will execute both analyses. E.g., 

```
python3 AutoFormalization/statement/evaluate.py --dataset Book --category "" --reasoning text-only --num_examples 3 --mode "skipApprox"
```

Note that the approximate equivalence checker will only run on target propositions whose number and type of bound variables matches those of the ground truth formalizations. This is usually only a minority (e.g., 33%) of the autoformalized theorem statements in a given batch. The time this will take depends on the quality of the predictions and configuration options, in our experience a typical batch from *Elements* will run for about 20-25 minutes on a standard laptop.

### Autoformalizing Proofs

To autoformalize proofs in Elements, go to the root directory of LeanEuclid and run 

```
python3 AutoFormalization/proof/autoformalize.py --dataset Book --category "" --reasoning text-only --num_query 1 --num_examples 3
```

Autoformalizing the 43 propositions in the testing set of *Elements* as above should take roughly 6 minutes and ~250K tokens. The results, in this example, can be found in the subdirectory `result/proof/Book/text-only/3shot/`.

Unlike theorem statements, Lean does not need any assistance in evaluating proofs (aside, of course, from LeanEuclid's proof automation). You can get Lean to check all of the proofs produced in the previous steps by running 

```
python3 AutoFormalization/proof/evaluate.py --dataset Book --category "" --reasoning text-only --num_examples 3
```

After the proofs are checked, the aggregate results will be displayed akin to the following:

```
cnt: 1, tot: 43, acc: 2.33%
```

Which indicates that one proof was formalized correctly. In practice, it is rare for a proof in *Elements* to be correct out-of-the-box, as most require a small degree of manual repair (for now).

## Cleanup

As a side-effect of the autoformalization-evaluation pipeline, autoformalization and evaluation instances are stored in the `tmp` subdirectory of the LeanEuclid repository. When you are **done** with these files, you can empty this folder by running `lake script run cleanup`. 
