/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode065
import Proofs.RadenkovicGutmanD20Long00CompositionalNode206
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e207 : NestedArithmetic.Expr 3 := .times e065 e206
noncomputable def p207 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-94,0],[0,0]],[[0,0],[0,0]],[[-1224,0],[0,0]],[[0,0],[0,0]],[[-7682,0],[0,0]],[[0,0],[0,0]],[[-27412,0],[0,0]],[[0,0],[0,0]],[[-59128,-2],[-2,0]],[[0,0],[0,0]],[[-77980,-76],[-76,0]],[[0,0],[0,0]],[[-61154,-484],[-484,0]],[[0,0],[0,0]],[[-26258,-1128],[-1128,0]],[[0,0],[0,0]],[[-4998,-1018],[-1018,0]],[[0,0],[0,0]],[[-180,-300],[-300,-2]],[[0],[0,0]],[[0],[0,-20]]]
theorem step207 : p207=NestedArithmetic.mul p065 p206 := by decide +kernel
#print axioms step207
theorem h207 : NestedArithmetic.compile e207=p207 := StagedExprCompile.compile_times e207 e065 e206 p065 p206 p207 rfl h065 h206 step207
#print axioms h207
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
