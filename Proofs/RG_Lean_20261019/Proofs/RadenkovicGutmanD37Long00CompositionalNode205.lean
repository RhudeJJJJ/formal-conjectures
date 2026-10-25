/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode204
import Proofs.RadenkovicGutmanD37Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e205 : NestedArithmetic.Expr 3 := .times e204 e003
noncomputable def p205 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[74,0],[0]],[[0,0],[0]],[[1184,0],[0]],[[0,0],[0]],[[7918,0],[0]],[[0,0],[0]],[[28712,0],[0]],[[0,0],[0]],[[61272,0],[0]],[[0,0],[0]],[[78144,74],[74]],[[0,0],[0]],[[57646,518],[518]],[[0,0],[0]],[[22200,1184],[1184]],[[0,0],[0]],[[3330,962],[962]],[[0,0],[0]],[[0,222],[222]]]
theorem step205 : p205=NestedArithmetic.mul p204 p003 := by decide +kernel
#print axioms step205
theorem h205 : NestedArithmetic.compile e205=p205 := StagedExprCompile.compile_times e205 e204 e003 p204 p003 p205 rfl h204 h003 step205
#print axioms h205
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
