/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode030
import Proofs.RadenkovicGutmanD10Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e213 : NestedArithmetic.Expr 3 := .times e030 e158
noncomputable def p213 : NestedHorner.Poly 3 := [[[10],[0]],[[0,0],[0]],[[150,0],[0,0]],[[0,0],[0,0]],[[940,0],[0,0]],[[0,0],[0,0]],[[3190,0],[0,0]],[[0,0],[0,0]],[[6360,0],[0,0]],[[0,0],[0,0]],[[7560,10],[10,0]],[[0,0],[0,0]],[[5140,80],[80,0]],[[0,0],[0,0]],[[1670,220],[220,0]],[[0,0],[0,0]],[[30,240],[240,0]],[[0,0],[0,0]],[[-90,90],[90,0]],[[0],[0,0]],[[0],[0,10]]]
theorem step213 : p213=NestedArithmetic.mul p030 p158 := by decide +kernel
#print axioms step213
theorem h213 : NestedArithmetic.compile e213=p213 := StagedExprCompile.compile_times e213 e030 e158 p030 p158 p213 rfl h030 h158 step213
#print axioms h213
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
