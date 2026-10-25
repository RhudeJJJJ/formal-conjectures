/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode191
import Proofs.RadenkovicGutmanD25Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e202 : NestedArithmetic.Expr 3 := .times e191 e176
noncomputable def p202 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[59,0],[0,0]],[[0,0],[0,0]],[[669,0],[0,0]],[[0,0],[0,0]],[[4012,0],[0,0]],[[0,0],[0,0]],[[14297,0],[0,0]],[[0,0],[0,0]],[[31688,2],[2,0]],[[0,0],[0,0]],[[43960,41],[41,0]],[[0,0],[0,0]],[[37144,244],[244,0]],[[0,0],[0,0]],[[17743,598],[598,0]],[[0,0],[0,0]],[[3993,618],[618,0]],[[0,0],[0,0]],[[225,225],[225,2]],[[0],[0,0]],[[0],[0,25]]]
theorem step202 : p202=NestedArithmetic.mul p191 p176 := by decide +kernel
#print axioms step202
theorem h202 : NestedArithmetic.compile e202=p202 := StagedExprCompile.compile_times e202 e191 e176 p191 p176 p202 rfl h191 h176 step202
#print axioms h202
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
