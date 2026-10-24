/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode183
import Proofs.RadenkovicGutmanD4Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e184 : NestedArithmetic.Expr 3 := .times e183 e003
noncomputable def p184 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[4,0],[0]],[[0,0],[0]],[[64,0],[0]],[[0,0],[0]],[[428,0],[0]],[[0,0],[0]],[[1552,0],[0]],[[0,0],[0]],[[3312,0],[0]],[[0,0],[0]],[[4224,4],[4]],[[0,0],[0]],[[3116,28],[28]],[[0,0],[0]],[[1200,64],[64]],[[0,0],[0]],[[180,52],[52]],[[0,0],[0]],[[0,12],[12]]]
theorem step184 : p184=NestedArithmetic.mul p183 p003 := by decide +kernel
#print axioms step184
theorem h184 : NestedArithmetic.compile e184=p184 := StagedExprCompile.compile_times e184 e183 e003 p183 p003 p184 rfl h183 h003 step184
#print axioms h184
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
