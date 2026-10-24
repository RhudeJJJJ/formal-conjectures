/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode030
import Proofs.RadenkovicGutmanD5Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e213 : NestedArithmetic.Expr 3 := .times e030 e158
noncomputable def p213 : NestedHorner.Poly 3 := [[[5],[0]],[[0,0],[0]],[[75,0],[0,0]],[[0,0],[0,0]],[[470,0],[0,0]],[[0,0],[0,0]],[[1595,0],[0,0]],[[0,0],[0,0]],[[3180,0],[0,0]],[[0,0],[0,0]],[[3780,5],[5,0]],[[0,0],[0,0]],[[2570,40],[40,0]],[[0,0],[0,0]],[[835,110],[110,0]],[[0,0],[0,0]],[[15,120],[120,0]],[[0,0],[0,0]],[[-45,45],[45,0]],[[0],[0,0]],[[0],[0,5]]]
theorem step213 : p213=NestedArithmetic.mul p030 p158 := by decide +kernel
#print axioms step213
theorem h213 : NestedArithmetic.compile e213=p213 := StagedExprCompile.compile_times e213 e030 e158 p030 p158 p213 rfl h030 h158 step213
#print axioms h213
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
