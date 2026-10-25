/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode045
import Proofs.RadenkovicGutmanD25Long00CompositionalNode048
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e049 : NestedArithmetic.Expr 3 := .plus e045 e048
noncomputable def p049 : NestedHorner.Poly 3 := [[[0],[0,25]],[[0,0],[0,0]],[[-225,375],[375,2]],[[0,0],[0]],[[2757,1268],[1268]],[[0,0],[0]],[[23081,1398],[1398]],[[0,0],[0]],[[65384,594],[594]],[[0,0],[0]],[[95628,91],[91]],[[0,0],[0]],[[81012,2],[2]],[[0]],[[41147]],[[0]],[[12388]],[[0]],[[2063]],[[0]],[[155]],[[0]],[[2]]]
theorem step049 : p049=NestedHorner.add p045 p048 := by decide +kernel
#print axioms step049
theorem h049 : NestedArithmetic.compile e049=p049 := StagedExprCompile.compile_plus e049 e045 e048 p045 p048 p049 rfl h045 h048 step049
#print axioms h049
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
