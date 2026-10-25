/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode202
import Proofs.RadenkovicGutmanD14Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e203 : NestedArithmetic.Expr 3 := .times e202 e122
noncomputable def p203 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[48,0],[0,0]],[[0,0],[0,0]],[[482,0],[0,0]],[[0,0],[0,0]],[[2670,0],[0,0]],[[0,0],[0,0]],[[9006,0],[0,0]],[[0,0],[0,0]],[[19192,2],[2,0]],[[0,0],[0,0]],[[25876,30],[30,0]],[[0,0],[0,0]],[[21414,156],[156,0]],[[0,0],[0,0]],[[10076,356],[356,0]],[[0,0],[0,0]],[[2244,354],[354,0]],[[0,0],[0,0]],[[126,126],[126,2]],[[0],[0,0]],[[0],[0,14]]]
theorem step203 : p203=NestedArithmetic.mul p202 p122 := by decide +kernel
#print axioms step203
theorem h203 : NestedArithmetic.compile e203=p203 := StagedExprCompile.compile_times e203 e202 e122 p202 p122 p203 rfl h202 h122 step203
#print axioms h203
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
