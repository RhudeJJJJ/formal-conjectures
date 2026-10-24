/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode009
import Proofs.RadenkovicGutmanD4Long00CompositionalNode055
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e059 : NestedArithmetic.Expr 3 := .times e009 e055
noncomputable def p059 : NestedHorner.Poly 3 := [[[0],[0]],[[0,12],[12]],[[0,0],[0]],[[180,52],[52]],[[0,0],[0]],[[1200,64],[64]],[[0,0],[0]],[[3116,28],[28]],[[0,0],[0]],[[4224,4],[4]],[[0]],[[3312]],[[0]],[[1552]],[[0]],[[428]],[[0]],[[64]],[[0]],[[4]]]
theorem step059 : p059=NestedArithmetic.mul p009 p055 := by decide +kernel
#print axioms step059
theorem h059 : NestedArithmetic.compile e059=p059 := StagedExprCompile.compile_times e059 e009 e055 p009 p055 p059 rfl h009 h055 step059
#print axioms h059
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
