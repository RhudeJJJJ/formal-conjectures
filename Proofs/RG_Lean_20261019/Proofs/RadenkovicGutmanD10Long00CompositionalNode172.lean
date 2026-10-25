/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode171
import Proofs.RadenkovicGutmanD10Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e172 : NestedArithmetic.Expr 3 := .times e171 e003
noncomputable def p172 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[20,0],[0]],[[0,0],[0]],[[300,0],[0]],[[0,0],[0]],[[1880,0],[0]],[[0,0],[0]],[[6380,0],[0]],[[0,0],[0]],[[12720,0],[0]],[[0,0],[0]],[[15140,10],[10]],[[0,0],[0]],[[10440,70],[70]],[[0,0],[0]],[[3780,160],[160]],[[0,0],[0]],[[540,130],[130]],[[0,0],[0]],[[0,30],[30]]]
theorem step172 : p172=NestedArithmetic.mul p171 p003 := by decide +kernel
#print axioms step172
theorem h172 : NestedArithmetic.compile e172=p172 := StagedExprCompile.compile_times e172 e171 e003 p171 p003 p172 rfl h171 h003 step172
#print axioms h172
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
