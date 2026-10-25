/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode092
import Proofs.RadenkovicGutmanD31Long00CompositionalNode103
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e104 : NestedArithmetic.Expr 3 := .plus e092 e103
noncomputable def p104 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-2232,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-20088,-20088,0],[-20088,-18786,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-523962,-222642,0],[-222642,-60884,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-5090634,-1047924,0],[-1047924,-97154,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-26840544,-2766750,0],[-2766750,-81716,0],[0,0]],[[0,0,0],[0,0],[0]],[[-89152466,-4559108,0],[-4559108,-34472],[0]],[[0,0,0],[0,0],[0]],[[-201503286,-4914678,0],[-4914678,-4588],[0]],[[0,0,0],[0,0],[0]],[[-323916396,-3504488,0],[-3504488,1550],[0]],[[0,0,0],[0,0],[0]],[[-379790176,-1605428,0],[-1605428,620],[0]],[[0,0,0],[0,0],[0]],[[-328563854,-415648,0],[-415648,62],[0]],[[0,0],[0]],[[-209363212,-21638],[-21638]],[[0,0],[0]],[[-96256364,22940],[22940]],[[0,0],[0]],[[-29996840,7874],[7874]],[[0,0],[0]],[[-5029998,1116],[1116]],[[0,0],[0]],[[324322,62],[62]],[[0]],[[445284]],[[0]],[[127224]],[[0]],[[19654]],[[0]],[[1674]],[[0]],[[62]]]
theorem step104 : p104=NestedHorner.add p092 p103 := by decide +kernel
#print axioms step104
theorem h104 : NestedArithmetic.compile e104=p104 := StagedExprCompile.compile_plus e104 e092 e103 p092 p103 p104 rfl h092 h103 step104
#print axioms h104
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
