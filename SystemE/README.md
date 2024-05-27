## The Formal System E

E is a formal system introduced by [Avigad et al., 2009] for faithfully formalizing the proofs in Euclid’s Elements, including the use of diagrammatic reasoning. It defines a language for expressing basic objects in 2D Euclidean geometry (points, lines, circles, etc.), as well as the form of theorems and proofs. We provide an implementation of the formal system E in the Lean proof assistant.

> Avigad, Jeremy, Edward Dean, and John Mumma. "A formal system for Euclid’s Elements." The Review of Symbolic Logic 2.4 (2009): 700-768.

### Geometry Objects

E is six-sorted, with sorts for points, lines, circles, segments, angles, and triangles (areas).

#### [Points](SystemE/Sorts/Points.lean)

Points in E are just opaque symbols. We define a point to be a pair of real numbers. However, we mark the definition by `@[irreducible]`, which means the definition will not be unfolded unless explicitly instructed by the user. Therefore, points in our system also behave like opaque symbols most of the time. We use this definition of points to define other sorts (lines, circles, etc.), so all definitions are ultimately based on real numbers. This differs from [Avigad et al., 2009], though the difference may not be important in practice, as we almost never unfold these definitions.
```lean
@[irreducible]
structure Point where
coords ::
  x : ℝ
  y : ℝ

```

#### [Lines](SystemE/Sorts/Lines.lean)

A line is defined by the equation `a * x + b * y = c`, where `a` and `b` cannot be 0 simultaneously. It extends infinitely to both directions.
```lean
structure Line where
  a : ℝ
  b : ℝ
  c : ℝ
  nzero : a ≠ 0 ∨ b ≠ 0
```

#### [Circles](SystemE/Sorts/Circles.lean)

A circle has a centre and a positive radius.
```lean
structure Circle where
  centre : Point
  radius : ℝ
  ndegen : radius > 0
```

#### [Segments](SystemE/Sorts/Segments.lean)

A segment is defined by two endpoints.
```lean
inductive Segment
| endpoints (a b : Point)
```

We also define syntactic sugar to represent `Segment.endpoints a b` as `(a-b)` and its length as `|(a-b)|`.


#### [Angles](SystemE/Sorts/Angles.lean)

An angle is either a right angle or defined by three points.
```lean
inductive Angle
| right
| ofPoints (A B C : Point)

```

We define syntactic sugar to represent `Angle.ofPoints a b c` as `∠a:b:c`.

#### [Triangles](SystemE/Sorts/Triangles.lean)

Triangles are called "areas" in [Avigad et al., 2009]. Their definition is similar to angles, and a triangle can be written as `△a:b:c`.
```lean
inductive Triangle
| ofPoints (a b c : Point)
```


### Relations and Functions

E also defines the following relations between geometry objects and functions from objects to real numbers.

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

We also define the following syntactic sugar based on the basic relations:
```lean
opposingSides : Point → Point → Line → Prop
outsideCircle : Point → Circle → Prop
formTriangle : Point → Point → Point → Line → Line → Line → Prop
formRectilinearAngle : Point → Point → Point → Line → Line → Prop
formParallelogram : Point → Point → Point → Point → Line → Line → Line → Line → Prop
```

### [Construction Rules](SystemE/Constructions)

### [Diagrammatic Inferences](SystemE/Inferences/Diagrammatic.lean)

### [Metric Inferences](SystemE/Inferences/Metric.lean)

### [Transfer Inferences](SystemE/Inferences/Transfer.lean)

### [Superposition Inferences](SystemE/Inferences/Superposition.lean)

### Tactics

* [euclid_intros](SystemE/Tactics/Intros.lean): Similar to `intros`, with some simple desugaring.
* [euclid_apply](SystemE/Tactics/Solve.lean): Apply a leema in the forward direction. When some premises are not available, it tries to fill in small reasoning gaps automatically using SMT solvers or other proof automation techniques. This is related to the notion of "direct consequences" in [Avigad et al., 2009].
* [euclid_finish](SystemE/Tactics/Solve.lean): Proves the current goal using proof automation if it is "simple enough," i.e., a direct consequence of the hypotheses. 

### Options 

We currently support the following options to configure the use of SMT solvers: `systemE.trace : Bool` will allow you to inspect the SMT query generated from the proof context (default := false), and `systemE.solverTime` will allow you to specify the number of seconds by which the solvers have to fill reasoning gaps (default := 180).

Usage: 
```
set_option systemE.trace true
set_option systemE.solverTime 10
```