/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode191
import Proofs.RadenkovicGutmanD14Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e202 : NestedArithmetic.Expr 3 := .times e191 e176
noncomputable def p202 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[48,0],[0,0]],[[0,0],[0,0]],[[482,0],[0,0]],[[0,0],[0,0]],[[2670,0],[0,0]],[[0,0],[0,0]],[[9006,0],[0,0]],[[0,0],[0,0]],[[19192,2],[2,0]],[[0,0],[0,0]],[[25876,30],[30,0]],[[0,0],[0,0]],[[21414,156],[156,0]],[[0,0],[0,0]],[[10076,356],[356,0]],[[0,0],[0,0]],[[2244,354],[354,0]],[[0,0],[0,0]],[[126,126],[126,2]],[[0],[0,0]],[[0],[0,14]]]
theorem step202 : p202=NestedArithmetic.mul p191 p176 := by decide +kernel
#print axioms step202
theorem h202 : NestedArithmetic.compile e202=p202 := StagedExprCompile.compile_times e202 e191 e176 p191 p176 p202 rfl h191 h176 step202
#print axioms h202
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
