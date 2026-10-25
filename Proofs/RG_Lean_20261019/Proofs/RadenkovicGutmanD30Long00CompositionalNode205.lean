/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode204
import Proofs.RadenkovicGutmanD30Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e205 : NestedArithmetic.Expr 3 := .times e204 e003
noncomputable def p205 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[60,0],[0]],[[0,0],[0]],[[960,0],[0]],[[0,0],[0]],[[6420,0],[0]],[[0,0],[0]],[[23280,0],[0]],[[0,0],[0]],[[49680,0],[0]],[[0,0],[0]],[[63360,60],[60]],[[0,0],[0]],[[46740,420],[420]],[[0,0],[0]],[[18000,960],[960]],[[0,0],[0]],[[2700,780],[780]],[[0,0],[0]],[[0,180],[180]]]
theorem step205 : p205=NestedArithmetic.mul p204 p003 := by decide +kernel
#print axioms step205
theorem h205 : NestedArithmetic.compile e205=p205 := StagedExprCompile.compile_times e205 e204 e003 p204 p003 p205 rfl h204 h003 step205
#print axioms h205
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
