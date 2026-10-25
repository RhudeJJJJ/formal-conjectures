/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode044
import Proofs.RadenkovicGutmanD25Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e062 : NestedArithmetic.Expr 3 := .times e044 e052
noncomputable def p062 : NestedHorner.Poly 3 := [[[0],[0,25]],[[0,0],[0,0]],[[225,225],[225,2]],[[0,0],[0]],[[3993,618],[618]],[[0,0],[0]],[[17743,598],[598]],[[0,0],[0]],[[37144,244],[244]],[[0,0],[0]],[[43960,41],[41]],[[0,0],[0]],[[31688,2],[2]],[[0]],[[14297]],[[0]],[[4012]],[[0]],[[669]],[[0]],[[59]],[[0]],[[2]]]
theorem step062 : p062=NestedArithmetic.mul p044 p052 := by decide +kernel
#print axioms step062
theorem h062 : NestedArithmetic.compile e062=p062 := StagedExprCompile.compile_times e062 e044 e052 p044 p052 p062 rfl h044 h052 step062
#print axioms h062
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
