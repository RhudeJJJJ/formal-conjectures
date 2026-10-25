/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode202
import Proofs.RadenkovicGutmanD39Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e203 : NestedArithmetic.Expr 3 := .times e202 e122
noncomputable def p203 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[73,0],[0,0]],[[0,0],[0,0]],[[907,0],[0,0]],[[0,0],[0,0]],[[5720,0],[0,0]],[[0,0],[0,0]],[[21031,0],[0,0]],[[0,0],[0,0]],[[47592,2],[2,0]],[[0,0],[0,0]],[[66976,55],[55,0]],[[0,0],[0,0]],[[57164,356],[356,0]],[[0,0],[0,0]],[[27501,906],[906,0]],[[0,0],[0,0]],[[6219,954],[954,0]],[[0,0],[0,0]],[[351,351],[351,2]],[[0],[0,0]],[[0],[0,39]]]
theorem step203 : p203=NestedArithmetic.mul p202 p122 := by decide +kernel
#print axioms step203
theorem h203 : NestedArithmetic.compile e203=p203 := StagedExprCompile.compile_times e203 e202 e122 p202 p122 p203 rfl h202 h122 step203
#print axioms h203
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
