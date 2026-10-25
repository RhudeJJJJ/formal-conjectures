/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode044
import Proofs.RadenkovicGutmanD14Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e062 : NestedArithmetic.Expr 3 := .times e044 e052
noncomputable def p062 : NestedHorner.Poly 3 := [[[0],[0,14]],[[0,0],[0,0]],[[126,126],[126,2]],[[0,0],[0]],[[2244,354],[354]],[[0,0],[0]],[[10076,356],[356]],[[0,0],[0]],[[21414,156],[156]],[[0,0],[0]],[[25876,30],[30]],[[0,0],[0]],[[19192,2],[2]],[[0]],[[9006]],[[0]],[[2670]],[[0]],[[482]],[[0]],[[48]],[[0]],[[2]]]
theorem step062 : p062=NestedArithmetic.mul p044 p052 := by decide +kernel
#print axioms step062
theorem h062 : NestedArithmetic.compile e062=p062 := StagedExprCompile.compile_times e062 e044 e052 p044 p052 p062 rfl h044 h052 step062
#print axioms h062
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
