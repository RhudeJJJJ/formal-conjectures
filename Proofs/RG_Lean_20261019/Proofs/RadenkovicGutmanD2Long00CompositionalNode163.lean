/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode162
import Proofs.RadenkovicGutmanD2Long00CompositionalNode120
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e163 : NestedArithmetic.Expr 3 := .times e162 e120
noncomputable def p163 : NestedHorner.Poly 3 := [[[0],[0]],[[0,0],[0]],[[8,0],[0,0]],[[0,0],[0,0]],[[112,0],[0,0]],[[0,0],[0,0]],[[648,0],[0,0]],[[0,0],[0,0]],[[2000,0],[0,0]],[[0,0],[0,0]],[[3552,0],[0,0]],[[0,0],[0,0]],[[3664,0],[0,0]],[[0,0],[0,0]],[[2120,0],[0,0]],[[0,0],[0,0]],[[624,0],[0,0]],[[0,0],[0,0]],[[72,0],[0,0]],[[0],[0,0]],[[0],[0,0]]]
theorem step163 : p163=NestedArithmetic.mul p162 p120 := by decide +kernel
#print axioms step163
theorem h163 : NestedArithmetic.compile e163=p163 := StagedExprCompile.compile_times e163 e162 e120 p162 p120 p163 rfl h162 h120 step163
#print axioms h163
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
