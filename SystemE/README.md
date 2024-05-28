## The Formal System E

E is a formal system introduced by [Avigad et al., 2009] for faithfully formalizing the proofs in Euclid’s Elements, including the use of diagrammatic reasoning. It defines a language for expressing basic objects in 2D Euclidean geometry (points, lines, circles, etc.), as well as the form of theorems and proofs. We provide an implementation of the formal system E in Lean.

> Avigad, Jeremy, Edward Dean, and John Mumma. "A formal system for Euclid’s Elements." The Review of Symbolic Logic 2.4 (2009): 700-768.

### Geometic Objects

E is six-sorted, with sorts for points, lines, circles, segments, angles, and triangles (areas).

#### [Primitive Sorts](Theory/Sorts/Primitives.lean)

The primitive sorts `Point`, `Line`, and `Circle` are simply opaque types. These could be replaced with analytic definitions (e.g., points can be defined as pairs of real numbers), in which case our various inference rules could be proved as theorems, but for our purposes this is sufficient.
```lean
axiom Point : Type

axiom Line : Type

axiom Circle : Type
```


### Composite Sorts

#### [Segments](Theory/Sorts/Segments.lean)

A segment is defined by two endpoints.
```lean
inductive Segment
| endpoints (a b : Point)
```

We also define syntactic sugar to represent `Segment.endpoints a b` as `(a-b)` and its length as `|(a-b)|`.


#### [Angles](Theory/Sorts/Angles.lean)

An angle is either a right angle or defined by three points.
```lean
inductive Angle
| right
| ofPoints (A B C : Point)

```


#### [Triangles](Theory/Sorts/Triangles.lean)

Triangles are called "areas" in [Avigad et al., 2009]. Their definition is similar to angles, and a triangle can be written as `△a:b:c`.
```lean
inductive Triangle
| ofPoints (a b c : Point)
```


### Relations and Functions

E also defines the following relations between geometry objects and functions from objects to real numbers. We currently implement these as opaque functions as well.

```lean
onLine : Point → Line → Prop
sameSide : Point → Point → Line → Prop
between : Point → Point → Point → Prop
onCircle : Point → Circle → Prop
insideCircle : Point → Circle → Prop
isCentre : Point → Circle → Prop

intersectsLine : Line → Line → Prop
Line.intersectsCircle : Line → Circle → Prop
Circle.intersectsCircle : Circle → Circle → Prop

length : Segment → ℝ
degree : Angle → ℝ
size : Triangle → ℝ
```
We define syntactic sugar to represent the *degree* of `Angle.ofPoints a b c` as `∠a:b:c`.

We also define the following syntactic sugar based on the basic relations:
```lean
opposingSides : Point → Point → Line → Prop
outsideCircle : Point → Circle → Prop
formTriangle : Point → Point → Point → Line → Line → Line → Prop
formRectilinearAngle : Point → Point → Point → Line → Line → Prop
formParallelogram : Point → Point → Point → Point → Line → Line → Line → Line → Prop
```

### [Construction Rules](Theory/Constructions)

### [Diagrammatic Inferences](Theory/Inferences/Diagrammatic.lean)

### [Metric Inferences](Theory/Inferences/Metric.lean)

### [Transfer Inferences](Theory/Inferences/Transfer.lean)

### [Superposition Inferences](Theory/Inferences/Superposition.lean)

### Tactics

* [euclid_intros](Meta/Tactics/Intros.lean): Similar to `intros`, with some simple desugaring.
* [euclid_apply](Meta/Tactics/Solve.lean): Apply a leema in the forward direction. When some premises are not available, it tries to fill in small reasoning gaps automatically using SMT solvers or other proof automation techniques. This is related to the notion of "direct consequences" in [Avigad et al., 2009].
* [euclid_finish](Meta/Tactics/Solve.lean): Proves the current goal using proof automation if it is "simple enough," i.e., a direct consequence of the hypotheses. 

### Options 

We currently support the following options to configure the use of SMT solvers: `systemE.trace : Bool` will allow you to inspect the SMT query generated from the proof context (default := false), and `systemE.solverTime` will allow you to specify the number of seconds by which the solvers have to fill reasoning gaps (default := 300).

Usage: 
```
set_option systemE.trace true
set_option systemE.solverTime 10
```
