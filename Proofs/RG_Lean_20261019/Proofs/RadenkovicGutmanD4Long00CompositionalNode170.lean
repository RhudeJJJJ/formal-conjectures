/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode009
import Proofs.RadenkovicGutmanD4Long00CompositionalNode169
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e170 : NestedArithmetic.Expr 3 := .times e009 e169
noncomputable def p170 : NestedHorner.Poly 3 := [[[8],[0]],[[0,0],[0]],[[120,0],[0]],[[0,0],[0]],[[752,0],[0]],[[0,0],[0]],[[2552,0],[0]],[[0,0],[0]],[[5088,0],[0]],[[0,0],[0]],[[6056,4],[4]],[[0,0],[0]],[[4176,28],[28]],[[0,0],[0]],[[1512,64],[64]],[[0,0],[0]],[[216,52],[52]],[[0,0],[0]],[[0,12],[12]]]
theorem step170 : p170=NestedArithmetic.mul p009 p169 := by decide +kernel
#print axioms step170
theorem h170 : NestedArithmetic.compile e170=p170 := StagedExprCompile.compile_times e170 e009 e169 p009 p169 p170 rfl h009 h169 step170
#print axioms h170
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
