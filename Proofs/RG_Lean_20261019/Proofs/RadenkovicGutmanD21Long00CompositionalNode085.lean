/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode073
import Proofs.RadenkovicGutmanD21Long00CompositionalNode084
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e085 : NestedArithmetic.Expr 3 := .plus e073 e084
noncomputable def p085 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,-1512,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-13608,-108864,0],[-108864,-29358,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1933470,-1538838,0],[-1538838,-185388,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-29299158,-9296532,0],[-9296532,-555534,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-206462592,-31733730,0],[-31733730,-901740,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-871215198,-68385156,0],[-68385156,-843864,0],[0,0]],[[0,0,0],[0,0],[0]],[[-2453689938,-98653170,0],[-98653170,-465108],[0]],[[0,0,0],[0,0],[0]],[[-4895936724,-98538552,0],[-98538552,-148638],[0]],[[0,0,0],[0,0],[0]],[[-7179458496,-69390804,0],[-69390804,-25452],[0]],[[0,0,0],[0,0],[0]],[[-7920881682,-34646808,0],[-34646808,-1806],[0]],[[0,0,0],[0,0],[0]],[[-6672185268,-12180378,0],[-12180378,0],[0]],[[0,0],[0]],[[-4326044100,-2945460],[-2945460]],[[0,0],[0]],[[-2164053528,-466074],[-466074]],[[0,0],[0]],[[-832384770,-43428],[-43428]],[[0,0],[0]],[[-243708906,-1806],[-1806]],[[0,0],[0]],[[-53286660,0],[0]],[[0]],[[-8419320]],[[0]],[[-907494]],[[0]],[[-59682]],[[0]],[[-1806]],[[0]],[[0]]]
theorem step085 : p085=NestedHorner.add p073 p084 := by decide +kernel
#print axioms step085
theorem h085 : NestedArithmetic.compile e085=p085 := StagedExprCompile.compile_plus e085 e073 e084 p073 p084 p085 rfl h073 h084 step085
#print axioms h085
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
