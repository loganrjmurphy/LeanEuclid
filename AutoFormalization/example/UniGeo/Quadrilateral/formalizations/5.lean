import SystemE
import Book
import UniGeo.Relations

open Elements.Book1

namespace UniGeo.Quadrilateral

theorem theorem_5 : ∀ (V W X Y Z: Point) (VW XZ WX WY VX VY VZ: Line),
  formQuadrilateral W V X Y VW XY WX VY ∧
  distinctPointsOnLine W Y WY ∧
  distinctPointsOnLine V X VX ∧
  distinctPointsOnLine V Z VZ ∧
  distinctPointsOnLine Y Z XZ ∧
  X.opposingSides Z VY ∧
  ¬ XY.intersectsLine VW ∧
  ¬ VZ.intersectsLine WY ∧
  ¬ XZ.intersectsLine VW ∧
  |(V─X)| = |(Y─W)| →
  |(V─Y)|=|(X─W)| :=
by
  euclid_intros
  have :|(W─Y)| = |(V─Z)| := by
    euclid_apply proposition_34' W Y V Z WY VZ VW XZ
    euclid_finish
  have :|(V─X)| = |(V─Z)| := by euclid_finish
  have : ∠ V:X:Z = ∠ V:Z:X := by
    euclid_apply proposition_5' V X Z VX XZ VZ
    euclid_finish
  have : ∠ W:Y:X = ∠ V:Z:X := by
    euclid_apply proposition_29'''' W V X Y Z WY VZ XZ
    euclid_finish
  have : ∠ W:Y:X = ∠ V:X:Z := by euclid_finish
  have : △V:X:Y ≅ △W:Y:X := by euclid_finish
  have : |(V─Y)|=|(X─W)| := by
    euclid_apply (△V:X:Y).congruent_if △W:Y:X
    euclid_finish
  euclid_finish

end UniGeo.Quadrilateral
