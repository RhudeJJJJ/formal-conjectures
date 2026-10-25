/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode191
import Proofs.RadenkovicGutmanD38Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e192 : NestedArithmetic.Expr 3 := .times e191 e158
noncomputable def p192 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[68,0],[0,0]],[[0,0],[0,0]],[[758,0],[0,0]],[[0,0],[0,0]],[[4210,0],[0,0]],[[0,0],[0,0]],[[13394,0],[0,0]],[[0,0],[0,0]],[[25680,2],[2,0]],[[0,0],[0,0]],[[29756,54],[54,0]],[[0,0],[0,0]],[[19866,348],[348,0]],[[0,0],[0,0]],[[6352,884],[884,0]],[[0,0],[0,0]],[[96,930],[930,0]],[[0,0],[0,0]],[[-342,342],[342,2]],[[0],[0,0]],[[0],[0,38]]]
theorem step192 : p192=NestedArithmetic.mul p191 p158 := by decide +kernel
#print axioms step192
theorem h192 : NestedArithmetic.compile e192=p192 := StagedExprCompile.compile_times e192 e191 e158 p191 p158 p192 rfl h191 h158 step192
#print axioms h192
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
