/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode044
import Proofs.RadenkovicGutmanD39Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e062 : NestedArithmetic.Expr 3 := .times e044 e052
noncomputable def p062 : NestedHorner.Poly 3 := [[[0],[0,39]],[[0,0],[0,0]],[[351,351],[351,2]],[[0,0],[0]],[[6219,954],[954]],[[0,0],[0]],[[27501,906],[906]],[[0,0],[0]],[[57164,356],[356]],[[0,0],[0]],[[66976,55],[55]],[[0,0],[0]],[[47592,2],[2]],[[0]],[[21031]],[[0]],[[5720]],[[0]],[[907]],[[0]],[[73]],[[0]],[[2]]]
theorem step062 : p062=NestedArithmetic.mul p044 p052 := by decide +kernel
#print axioms step062
theorem h062 : NestedArithmetic.compile e062=p062 := StagedExprCompile.compile_times e062 e044 e052 p044 p052 p062 rfl h044 h052 step062
#print axioms h062
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
