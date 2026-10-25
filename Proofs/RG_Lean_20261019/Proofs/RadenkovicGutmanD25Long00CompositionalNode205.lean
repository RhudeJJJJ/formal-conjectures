/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode204
import Proofs.RadenkovicGutmanD25Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e205 : NestedArithmetic.Expr 3 := .times e204 e003
noncomputable def p205 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[50,0],[0]],[[0,0],[0]],[[800,0],[0]],[[0,0],[0]],[[5350,0],[0]],[[0,0],[0]],[[19400,0],[0]],[[0,0],[0]],[[41400,0],[0]],[[0,0],[0]],[[52800,50],[50]],[[0,0],[0]],[[38950,350],[350]],[[0,0],[0]],[[15000,800],[800]],[[0,0],[0]],[[2250,650],[650]],[[0,0],[0]],[[0,150],[150]]]
theorem step205 : p205=NestedArithmetic.mul p204 p003 := by decide +kernel
#print axioms step205
theorem h205 : NestedArithmetic.compile e205=p205 := StagedExprCompile.compile_times e205 e204 e003 p204 p003 p205 rfl h204 h003 step205
#print axioms h205
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
