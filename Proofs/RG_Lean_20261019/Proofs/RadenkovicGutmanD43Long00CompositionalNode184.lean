/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode030
import Proofs.RadenkovicGutmanD43Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e184 : NestedArithmetic.Expr 3 := .times e030 e183
noncomputable def p184 : NestedHorner.Poly 3 := [[[43],[0]],[[0,0],[0]],[[688,0],[0]],[[0,0],[0]],[[4601,0],[0]],[[0,0],[0]],[[16684,0],[0]],[[0,0],[0]],[[35604,0],[0]],[[0,0],[0]],[[45408,43],[43]],[[0,0],[0]],[[33497,301],[301]],[[0,0],[0]],[[12900,688],[688]],[[0,0],[0]],[[1935,559],[559]],[[0,0],[0]],[[0,129],[129]]]
theorem step184 : p184=NestedArithmetic.mul p030 p183 := by decide +kernel
#print axioms step184
theorem h184 : NestedArithmetic.compile e184=p184 := StagedExprCompile.compile_times e184 e030 e183 p030 p183 p184 rfl h030 h183 step184
#print axioms h184
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
