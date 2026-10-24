/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode047
import Proofs.RadenkovicGutmanD2Long00CompositionalNode048
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e049 : NestedArithmetic.Expr 3 := .plus e047 e048
noncomputable def p049 : NestedHorner.Poly 3 := [[[0],[0,2]],[[0,0],[0,0]],[[-18,30],[30,2]],[[0,0],[0]],[[240,118],[118]],[[0,0],[0]],[[2164,156],[156]],[[0,0],[0]],[[6598,88],[88]],[[0,0],[0]],[[10428,22],[22]],[[0,0],[0]],[[9648,2],[2]],[[0]],[[5462]],[[0]],[[1902]],[[0]],[[394]],[[0]],[[44]],[[0]],[[2]]]
theorem step049 : p049=NestedHorner.add p047 p048 := by decide +kernel
#print axioms step049
theorem h049 : NestedArithmetic.compile e049=p049 := StagedExprCompile.compile_plus e049 e047 e048 p047 p048 p049 rfl h047 h048 step049
#print axioms h049
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
