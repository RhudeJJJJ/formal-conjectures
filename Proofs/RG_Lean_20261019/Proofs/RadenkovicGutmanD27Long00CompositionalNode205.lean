/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode204
import Proofs.RadenkovicGutmanD27Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e205 : NestedArithmetic.Expr 3 := .times e204 e003
noncomputable def p205 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[54,0],[0]],[[0,0],[0]],[[864,0],[0]],[[0,0],[0]],[[5778,0],[0]],[[0,0],[0]],[[20952,0],[0]],[[0,0],[0]],[[44712,0],[0]],[[0,0],[0]],[[57024,54],[54]],[[0,0],[0]],[[42066,378],[378]],[[0,0],[0]],[[16200,864],[864]],[[0,0],[0]],[[2430,702],[702]],[[0,0],[0]],[[0,162],[162]]]
theorem step205 : p205=NestedArithmetic.mul p204 p003 := by decide +kernel
#print axioms step205
theorem h205 : NestedArithmetic.compile e205=p205 := StagedExprCompile.compile_times e205 e204 e003 p204 p003 p205 rfl h204 h003 step205
#print axioms h205
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
