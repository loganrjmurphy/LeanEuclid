import Lean.Meta
import SystemE.Theory
open Lean

/- A few handcoded translations for UniGeo-specific constructs and abbreviations, not required for formalizing *Elements* -/


def mkAngleExpr (a b c : Expr) : Expr := mkApp3 (.const `Angle.ofPoints []) a b c
def mkSegmentLengthExpr (a b : Expr) : Expr := .app (.const `Segment.length []) (mkApp2 (.const (`Segment.endpoints) []) a b)
def mkDisj (a b : Expr) : Expr := mkApp2 (.const `Or []) a b
def mkConj (a b : Expr) : Expr := mkApp2 (.const `And []) a b
def mkEq (a b : Expr) : Expr := mkApp3 (.const `Eq []) (.const `Real []) a b

def handleCongruentTriangle (tr1 tr2 : Expr) : Option Expr :=
  match tr1.getAppFnArgs with
  | (``Triangle.ofPoints, #[A,B,C]) =>
    match tr2.getAppFnArgs with
    | (``Triangle.ofPoints, #[D, E, F]) =>
      let ab_eq_de := mkEq (mkSegmentLengthExpr A B) (mkSegmentLengthExpr D E)
      let bc_eq_ef := mkEq (mkSegmentLengthExpr B C) (mkSegmentLengthExpr E F)
      let ca_eq_fd := mkEq (mkSegmentLengthExpr C A) (mkSegmentLengthExpr F D)
      let abc_eq_def := mkEq (mkAngleExpr A B C) (mkAngleExpr D E F)
      let bca_eq_efd := mkEq (mkAngleExpr B C A) (mkAngleExpr E F D)
      let cab_eq_fde := mkEq (mkAngleExpr C A B) (mkAngleExpr F D E)

      let SSS : Expr := mkConj ab_eq_de (mkConj bc_eq_ef ca_eq_fd)

      let SAS1 :=mkConj ab_eq_de (mkConj abc_eq_def bc_eq_ef)
      let SAS2 := mkConj bc_eq_ef (mkConj bca_eq_efd ca_eq_fd)
      let SAS3 := mkConj ca_eq_fd (mkConj cab_eq_fde ab_eq_de)

      let ASA1 := mkConj abc_eq_def (mkConj ab_eq_de (bca_eq_efd))
      let ASA2 := mkConj bca_eq_efd (mkConj bc_eq_ef cab_eq_fde)
      let ASA3 := mkConj cab_eq_fde (mkConj ca_eq_fd abc_eq_def)
      let AAS1 := mkConj abc_eq_def (mkConj bca_eq_efd bc_eq_ef)
      let AAS2 := mkConj bca_eq_efd (mkConj cab_eq_fde ca_eq_fd)
      let AAS3 := mkConj cab_eq_fde (mkConj abc_eq_def ab_eq_de)
      let AAS4 := mkConj cab_eq_fde (mkConj bca_eq_efd ab_eq_de)
      let AAS5 := mkConj abc_eq_def (mkConj bca_eq_efd ca_eq_fd)
      let AAS6 := mkConj abc_eq_def (mkConj bc_eq_ef cab_eq_fde)
      some
        (mkDisj SSS
          (mkDisj SAS1 (mkDisj SAS2 (mkDisj SAS3 (mkDisj ASA1 (mkDisj ASA2 (mkDisj ASA3 (mkDisj AAS1 (mkDisj AAS2 (mkDisj AAS3 (mkDisj AAS4 (mkDisj AAS5 AAS6))))))))))))
    | _ => none
  | _ => none



def mkDiv (e1 e2 : Expr) : Expr :=
  mkApp6 (.const `HDiv.hDiv [.zero,.zero,.zero]) (.const `Real []) (.const `Real []) (.const `Real []) (mkApp2 (.const `LinearOrderedField.toDiv [.zero]) (.const `Real []) (.const `Real.instLinearOrderedFieldReal [])) e1 e2

def handleSimilarTriangle (tr1 tr2 : Expr) : Option Expr :=
 match tr1.getAppFnArgs with
  | (``Triangle.ofPoints, #[A,B,C]) =>
    match tr2.getAppFnArgs with
    | (``Triangle.ofPoints, #[D, E, F]) =>
      let abc_eq_def := mkEq (mkAngleExpr A B C) (mkAngleExpr D E F)
      let bca_eq_efd := mkEq (mkAngleExpr B C A) (mkAngleExpr E F D)
      let cab_eq_fde := mkEq (mkAngleExpr C A B) (mkAngleExpr F D E)
      let AA1 := mkConj abc_eq_def bca_eq_efd
      let AA2 := mkConj bca_eq_efd cab_eq_fde
      let AA3 := mkConj cab_eq_fde abc_eq_def
      let AA := mkDisj AA1 (mkDisj AA2 AA3)

      let AB_div_DE := mkDiv (mkSegmentLengthExpr A B) (mkSegmentLengthExpr D E)
      let BC_div_EF := mkDiv (mkSegmentLengthExpr B C) (mkSegmentLengthExpr E F)
      let CA_div_FD := mkDiv (mkSegmentLengthExpr C A) (mkSegmentLengthExpr F D)

      let SAS1 := mkConj (mkEq AB_div_DE BC_div_EF) abc_eq_def
      let SAS2 := mkConj (mkEq BC_div_EF CA_div_FD) bca_eq_efd
      let SAS3 := mkConj (mkEq CA_div_FD AB_div_DE) cab_eq_fde
      let SAS := mkDisj SAS1 (mkDisj SAS2 SAS3)
      let SSS := mkConj (mkEq AB_div_DE BC_div_EF) (mkEq BC_div_EF CA_div_FD)
      some (mkDisj AA (mkDisj SAS SSS))
    | _ => none
  | _ => none
