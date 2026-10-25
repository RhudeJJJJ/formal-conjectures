/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode204
import Proofs.RadenkovicGutmanD22Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e205 : NestedArithmetic.Expr 3 := .times e204 e003
noncomputable def p205 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[44,0],[0]],[[0,0],[0]],[[704,0],[0]],[[0,0],[0]],[[4708,0],[0]],[[0,0],[0]],[[17072,0],[0]],[[0,0],[0]],[[36432,0],[0]],[[0,0],[0]],[[46464,44],[44]],[[0,0],[0]],[[34276,308],[308]],[[0,0],[0]],[[13200,704],[704]],[[0,0],[0]],[[1980,572],[572]],[[0,0],[0]],[[0,132],[132]]]
theorem step205 : p205=NestedArithmetic.mul p204 p003 := by decide +kernel
#print axioms step205
theorem h205 : NestedArithmetic.compile e205=p205 := StagedExprCompile.compile_times e205 e204 e003 p204 p003 p205 rfl h204 h003 step205
#print axioms h205
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
