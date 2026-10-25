/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode041
import Proofs.RadenkovicGutmanD45Long00CompositionalNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e041 e042
noncomputable def p043 : NestedHorner.Poly 3 := [[[0],[0]],[[0,135],[135,-86]],[[0,0],[0]],[[3276,-189],[-189]],[[0,0],[0]],[[17376,-1344],[-1344]],[[0,0],[0]],[[34738,-1577],[-1577]],[[0,0],[0]],[[27590,-643],[-643]],[[0,0],[0]],[[-4224,-86],[-86]],[[0]],[[-23986]],[[0]],[[-18326]],[[0]],[[-6622]],[[0]],[[-1192]],[[0]],[[-86]]]
theorem step043 : p043=NestedHorner.add p041 p042 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := StagedExprCompile.compile_plus e043 e041 e042 p041 p042 p043 rfl h041 h042 step043
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
