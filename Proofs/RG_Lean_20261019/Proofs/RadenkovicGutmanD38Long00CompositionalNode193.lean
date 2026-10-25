/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode192
import Proofs.RadenkovicGutmanD38Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e193 : NestedArithmetic.Expr 3 := .times e192 e122
noncomputable def p193 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[68,0],[0,0]],[[0,0],[0,0]],[[758,0],[0,0]],[[0,0],[0,0]],[[4210,0],[0,0]],[[0,0],[0,0]],[[13394,0],[0,0]],[[0,0],[0,0]],[[25680,2],[2,0]],[[0,0],[0,0]],[[29756,54],[54,0]],[[0,0],[0,0]],[[19866,348],[348,0]],[[0,0],[0,0]],[[6352,884],[884,0]],[[0,0],[0,0]],[[96,930],[930,0]],[[0,0],[0,0]],[[-342,342],[342,2]],[[0],[0,0]],[[0],[0,38]]]
theorem step193 : p193=NestedArithmetic.mul p192 p122 := by decide +kernel
#print axioms step193
theorem h193 : NestedArithmetic.compile e193=p193 := StagedExprCompile.compile_times e193 e192 e122 p192 p122 p193 rfl h192 h122 step193
#print axioms h193
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
