/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode204
import Proofs.RadenkovicGutmanD24Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e205 : NestedArithmetic.Expr 3 := .times e204 e003
noncomputable def p205 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[48,0],[0]],[[0,0],[0]],[[768,0],[0]],[[0,0],[0]],[[5136,0],[0]],[[0,0],[0]],[[18624,0],[0]],[[0,0],[0]],[[39744,0],[0]],[[0,0],[0]],[[50688,48],[48]],[[0,0],[0]],[[37392,336],[336]],[[0,0],[0]],[[14400,768],[768]],[[0,0],[0]],[[2160,624],[624]],[[0,0],[0]],[[0,144],[144]]]
theorem step205 : p205=NestedArithmetic.mul p204 p003 := by decide +kernel
#print axioms step205
theorem h205 : NestedArithmetic.compile e205=p205 := StagedExprCompile.compile_times e205 e204 e003 p204 p003 p205 rfl h204 h003 step205
#print axioms h205
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
