/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode009
import Proofs.RadenkovicGutmanD4Long00CompositionalNode182
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e183 : NestedArithmetic.Expr 3 := .times e009 e182
noncomputable def p183 : NestedHorner.Poly 3 := [[[4],[0]],[[0,0],[0]],[[64,0],[0]],[[0,0],[0]],[[428,0],[0]],[[0,0],[0]],[[1552,0],[0]],[[0,0],[0]],[[3312,0],[0]],[[0,0],[0]],[[4224,4],[4]],[[0,0],[0]],[[3116,28],[28]],[[0,0],[0]],[[1200,64],[64]],[[0,0],[0]],[[180,52],[52]],[[0,0],[0]],[[0,12],[12]]]
theorem step183 : p183=NestedArithmetic.mul p009 p182 := by decide +kernel
#print axioms step183
theorem h183 : NestedArithmetic.compile e183=p183 := StagedExprCompile.compile_times e183 e009 e182 p009 p182 p183 rfl h009 h182 step183
#print axioms h183
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
