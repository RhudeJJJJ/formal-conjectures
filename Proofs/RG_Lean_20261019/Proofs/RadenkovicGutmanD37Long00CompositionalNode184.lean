/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode030
import Proofs.RadenkovicGutmanD37Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e184 : NestedArithmetic.Expr 3 := .times e030 e183
noncomputable def p184 : NestedHorner.Poly 3 := [[[37],[0]],[[0,0],[0]],[[592,0],[0]],[[0,0],[0]],[[3959,0],[0]],[[0,0],[0]],[[14356,0],[0]],[[0,0],[0]],[[30636,0],[0]],[[0,0],[0]],[[39072,37],[37]],[[0,0],[0]],[[28823,259],[259]],[[0,0],[0]],[[11100,592],[592]],[[0,0],[0]],[[1665,481],[481]],[[0,0],[0]],[[0,111],[111]]]
theorem step184 : p184=NestedArithmetic.mul p030 p183 := by decide +kernel
#print axioms step184
theorem h184 : NestedArithmetic.compile e184=p184 := StagedExprCompile.compile_times e184 e030 e183 p030 p183 p184 rfl h030 h183 step184
#print axioms h184
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
