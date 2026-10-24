/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode064
import Proofs.RadenkovicGutmanD4Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e073 : NestedArithmetic.Expr 3 := .times e064 e056
noncomputable def p073 : NestedHorner.Poly 3 := [[[0],[0]],[[0,12],[12]],[[0,0],[0]],[[180,52],[52]],[[0,0],[0]],[[1200,64],[64]],[[0,0],[0]],[[3116,28],[28]],[[0,0],[0]],[[4224,4],[4]],[[0]],[[3312]],[[0]],[[1552]],[[0]],[[428]],[[0]],[[64]],[[0]],[[4]]]
theorem step073 : p073=NestedArithmetic.mul p064 p056 := by decide +kernel
#print axioms step073
theorem h073 : NestedArithmetic.compile e073=p073 := StagedExprCompile.compile_times e073 e064 e056 p064 p056 p073 rfl h064 h056 step073
#print axioms h073
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
