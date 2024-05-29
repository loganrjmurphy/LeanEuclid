Autoformalizing Euclidean Geometry
==================================


![LeanEuclid](https://github.com/loganrjmurphy/LeanEuclid/blob/master/images/LeanEuclid.jpg)


Code for the paper:  

[Autoformalizing Euclidean Geometry](https://arxiv.org/abs/2405.17216)  
International Conference on Machine Learning (ICML), 2024  
[Logan Murphy](https://www.cs.toronto.edu/~lmurphy/)\*, [Kaiyu Yang](https://yangky11.github.io/)\* (\* equal contribution), [Jialiang Sun](https://www.linkedin.com/in/jack-sun-2741711b5/?originalSubdomain=ca), [Zhaoyu Li](https://www.zhaoyu-li.com/), [Anima Anandkumar](http://tensorlab.cms.caltech.edu/users/anima/), and [Xujie Si](https://www.cs.toronto.edu/~six/)

```bibtex
@inproceedings{murphy2024leaneuclid,
  title={Autoformalizing {Euclidean} Geometry},
  author={Murphy, Logan and Yang, Kaiyu and Sun, Jialiang and Li, Zhaoyu and Anandkumar, Anima and Si, Xujie},
  booktitle={International Conference on Machine Learning (ICML)},
  year={2024}
}
```


[![GitHub license](https://img.shields.io/github/license/loganrjmurphy/LeanEuclid)](https://github.com/loganrjmurphy/LeanEuclid/blob/master/LICENSE)

______________________________________________________________________


## Quick Links

1. [Requirements](#requirements)  
1. [Building](#building)
1. [The Formal System E](#the-formal-system-e)
1. [LeanEuclid](#leaneuclid)
    1. [Euclid's *Elements*](#euclids-elements)
    1. [UniGeo](#unigeo)
1. [Evaluating Autoformalized Theorem Statements](#evaluating-autoformalized-theorem-statements)
1. [Experiments](#experiments)
1. [Acknowledgements](#acknowledgements)



## Requirements

* A working setup of [Lean 4](https://lean-lang.org/), including [elan](https://github.com/leanprover/elan) and [Lean's VSCode extension](https://lean-lang.org/lean4/doc/quickstart.html)
* Install the latest version of [Z3](https://github.com/Z3Prover/z3) and [CVC5](https://cvc5.github.io/) and make sure they can be accessed from the command line
* Install Python dependencies: `pip install smt-portfolio openai`
* Find out the location of `smt-portfolio` and make sure Lean's VSCode extension can also access it. For example, if `which smt-portfolio` outputs `/Users/yangky/miniconda3/envs/lean/bin/smt-portfolio`, you should set `Server Env Paths` in Lean's VSCode extension as below:
<img width="938" alt="image" src="https://github.com/loganrjmurphy/LeanEuclid/assets/5431913/abfc6d25-e2e4-462e-934d-a10b4cb4e96c">



## Building

Take the following steps to build the Lean project:

1. Run `lake script run check` to check if the requirements are satisfied.
2. Run `lake exe cache get` to download the [mathlib](https://github.com/leanprover-community/mathlib4) cache
3. Run `lake build` to compile the formal system E
4. Open a file for Euclid's *Elements* in VS Code, e.g., [Book/Prop01.lean](Book/Prop01.lean). You should expect to see:

![Elements Prop1](https://github.com/loganrjmurphy/LeanEuclid/blob/master/images/Elements_prop1.png)


Optionally, you can:

1. Run `lake -R -Kenv=dev build SystemE:docs` to build the documentation
1. View the auto-generated documentation locally at ./lake/build/doc, e.g., using `python -mhttp.server`


## The Formal System E

E is a formal system introduced by [Avigad et al., 2009](https://arxiv.org/abs/0810.4315) for faithfully formalizing the proofs in Euclid’s *Elements*, including the use of diagrammatic reasoning. It defines a language for expressing basic objects in 2D Euclidean geometry (points, lines, circles, etc.), as well as the form of theorems and proofs. We implement the formal system E in Lean and use SMT solvers to perform diagrammatic reasoning automatically and implicitly. Details of our implementation can be found [here](https://github.com/loganrjmurphy/LeanEuclid/tree/master/SystemE) and in the auto-generated documentation.



## LeanEuclid

LeanEuclid is a benchmark for testing autoformalization. It consists of 173 Euclidean geometry problems manually formalized into Lean. The theorems and proofs are in the format prescribed by the formal system E. Among the 173 problems, 48 are from Euclid's Elements, and 125 are adapted from the UniGeo dataset ([Chen et al., 2022](https://arxiv.org/abs/2212.02746)).


### Euclid's *Elements*

We manually formalized the first book of Euclid's *Elements*, using an [open-source LaTex version](https://github.com/rfitzp/Elements). The formalized theorems and proofs can be found [here](./Book). Thanks to E and automatic diagrammatic reasoning, our formalized proofs are "faithful" in the sense that they correspond very closely to Euclid's original proofs. To our knowledge, this is the first time Euclid's *Elements* has been faithfully formalized in a proof assistant such as Lean, and our formalization has uncovered errors in Euclid's proofs (Appendix B of our paper).

For example, below is our formalization of Euclid's first proposition in Book I, which states you can construct an equilateral triangle given two distinct points:

<img width="444" alt="image" src="https://github.com/loganrjmurphy/LeanEuclid/blob/master/images/Elements_prop1_Euclid.png">

Our formalized theorem and proof in [Book/Prop01.lean](https://github.com/loganrjmurphy/LeanEuclid/blob/master/Book/Prop01.lean):

```lean
theorem proposition_1 :
∀ (a b : Point) (AB : Line),
  distinctPointsOnLine a b AB →
    ∃ c : Point, |(c─a)| = |(a─b)| ∧ |(c─b)| = |(a─b)| := by
    euclid_intros
    euclid_apply circle_from_points a b as BCD
    euclid_apply circle_from_points b a as ACE
    euclid_apply intersection_circles BCD ACE as c
    euclid_apply point_on_circle_onlyif a b c BCD
    euclid_apply point_on_circle_onlyif b a c ACE
    use c
    euclid_finish
```



### UniGeo

Problems from UniGeo are generally easier than those from *Elements*. Unlike *Elements*, UniGeo's problem text does not include complete information about the problem, so we manually provide missing diagrammatic details to the text. For example:

Diagram in [UniGeo/Congruent/diagrams/1.png](https://github.com/loganrjmurphy/LeanEuclid/blob/master/UniGeo/Congruent/diagrams/1.png):

![UniGeo Congruent Theorem 1](https://github.com/loganrjmurphy/LeanEuclid/blob/master/images/UniGeo_congruent_1.png)

UniGeo's theorem statement in [UniGeo/Congruent/texts/1.txt](https://github.com/loganrjmurphy/LeanEuclid/blob/master/UniGeo/Congruent/texts/1.txt).

```
Given T U ≅ R S. R S ∥ T U. Complete the proof that △ R T U ≅ △ T R S.
```

UniGeo's proof in [UniGeo/Congruent/proofs/1.txt](https://github.com/loganrjmurphy/LeanEuclid/blob/master/UniGeo/Congruent/proofs/1.txt):
```
RS ∥ TU
TU ≅ RS
∠RTU ≅ ∠SRT
RT ≅ RT
△RTU ≅ △TRS
```

Diagrammatic details we provide:
```
There is a quadrilateral RSUT with vertices R, S, U, and T. There is a diagonal line segment RT drawn inside the quadrilateral, connecting vertices R and T. 
```

Our formalized theorem and proof in [UniGeo/Congruent/Thm01.lean](https://github.com/loganrjmurphy/LeanEuclid/blob/master/UniGeo/Congruent/Thm01.lean):

```lean
theorem theorem_1 : ∀ (R S T U : Point) (RS ST RT TU RU : Line),
  formTriangle R S T RS ST RT ∧
  formTriangle R T U RT TU RU ∧
  S.opposingSides U RT ∧
  |(T─U)| = |(R─S)| ∧
  ¬ RS.intersectsLine TU →
  (△ R:T:U).congruent (△ T:R:S) :=
by
  euclid_intros
  euclid_apply Elements.Book1.proposition_29''' S U R T RS TU RT
  euclid_finish
```


## Evaluating Autoformalized Theorem Statements

In addition to proof automation, our symbolic reasoning engine can be used to check the equivalence of autoformalized theorem statements against ground-truth theorem statements. We have built a wrapper `E3` which performs two forms of equivalence checking: 

1. Standard equivalence checking, i.e., check if the two theorem statements are logically equivalent or not. It may also be that one is strictly stronger than the other.
2. *Approximate* equivalence checking, where we try to quantify how close the two statements are to one another. 

Typically, the latter is only done if the statements are not proven equivalent, but you'd like to see how "close" the prediction was to the ground truth. More details on `E3` can be found [here](https://github.com/loganrjmurphy/LeanEuclid/tree/master/E3).

## Experiments

In our paper, we used LeanEuclid to test state-of-the-art LLMs on theorem statements and proof autoformalization. We provide a Python wrapper which can be used to replicate our experiment procedure. More details and usage examples can be found [here](https://github.com/loganrjmurphy/LeanEuclid/tree/master/AutoFormalization).

## Acknowledgements

* We use ([our own fork](https://github.com/yangky11/lean-smt) of) [lean-smt](https://github.com/ufmg-smite/lean-smt) for running SMT solvers from Lean.
* There are concurrent efforts on formalizing Euclidean geometry in Lean (e.g., [EG](https://github.com/jjdishere/EG) and [Hernandez-Espiet's work](https://github.com/leanprover-community/mathlib4/pull/7300)). To our knowledge, none of them performs diagrammatic reasoning automatically.
