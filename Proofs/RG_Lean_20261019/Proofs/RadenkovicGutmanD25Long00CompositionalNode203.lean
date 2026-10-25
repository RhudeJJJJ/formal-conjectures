/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode202
import Proofs.RadenkovicGutmanD25Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e203 : NestedArithmetic.Expr 3 := .times e202 e122
noncomputable def p203 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[59,0],[0,0]],[[0,0],[0,0]],[[669,0],[0,0]],[[0,0],[0,0]],[[4012,0],[0,0]],[[0,0],[0,0]],[[14297,0],[0,0]],[[0,0],[0,0]],[[31688,2],[2,0]],[[0,0],[0,0]],[[43960,41],[41,0]],[[0,0],[0,0]],[[37144,244],[244,0]],[[0,0],[0,0]],[[17743,598],[598,0]],[[0,0],[0,0]],[[3993,618],[618,0]],[[0,0],[0,0]],[[225,225],[225,2]],[[0],[0,0]],[[0],[0,25]]]
theorem step203 : p203=NestedArithmetic.mul p202 p122 := by decide +kernel
#print axioms step203
theorem h203 : NestedArithmetic.compile e203=p203 := StagedExprCompile.compile_times e203 e202 e122 p202 p122 p203 rfl h202 h122 step203
#print axioms h203
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
