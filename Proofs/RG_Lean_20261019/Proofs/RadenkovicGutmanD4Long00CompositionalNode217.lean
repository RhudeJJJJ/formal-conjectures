/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode064
import Proofs.RadenkovicGutmanD4Long00CompositionalNode216
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e217 : NestedArithmetic.Expr 3 := .times e064 e216
noncomputable def p217 : NestedHorner.Poly 3 := [[[4],[0]],[[0,0],[0]],[[64,0],[0]],[[0,0],[0]],[[428,0],[0]],[[0,0],[0]],[[1552,0],[0]],[[0,0],[0]],[[3312,0],[0]],[[0,0],[0]],[[4224,4],[4]],[[0,0],[0]],[[3116,28],[28]],[[0,0],[0]],[[1200,64],[64]],[[0,0],[0]],[[180,52],[52]],[[0,0],[0]],[[0,12],[12]]]
theorem step217 : p217=NestedArithmetic.mul p064 p216 := by decide +kernel
#print axioms step217
theorem h217 : NestedArithmetic.compile e217=p217 := StagedExprCompile.compile_times e217 e064 e216 p064 p216 p217 rfl h064 h216 step217
#print axioms h217
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
