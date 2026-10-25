/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode079
import Proofs.RadenkovicGutmanD7Long00CompositionalNode080
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e081 : NestedArithmetic.Expr 3 := .plus e079 e080
noncomputable def p081 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,-2646,0],[-2646,-441,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-43659,-38367,0],[-38367,-3822,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-713097,-236376,0],[-236376,-12985,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-5180868,-819035,0],[-819035,-22442,0],[0,0]],[[0,0,0],[0,0],[0]],[[-22258005,-1785168,0],[-1785168,-21756],[0]],[[0,0,0],[0,0],[0]],[[-63461321,-2597833,0],[-2597833,-12250],[0]],[[0,0,0],[0,0],[0]],[[-127780926,-2612484,0],[-2612484,-3969],[0]],[[0,0,0],[0,0],[0]],[[-188704684,-1849652,0],[-1849652,-686],[0]],[[0,0,0],[0,0],[0]],[[-209374011,-927570,0],[-927570,-49],[0]],[[0,0],[0]],[[-177190566,-327271],[-327271]],[[0,0],[0]],[[-115334730,-79380],[-79380]],[[0,0],[0]],[[-57887032,-12593],[-12593]],[[0,0],[0]],[[-22329643,-1176],[-1176]],[[0,0],[0]],[[-6554093,-49],[-49]],[[0]],[[-1436190]],[[0]],[[-227360]],[[0]],[[-24549]],[[0]],[[-1617]],[[0]],[[-49]]]
theorem step081 : p081=NestedHorner.add p079 p080 := by decide +kernel
#print axioms step081
theorem h081 : NestedArithmetic.compile e081=p081 := StagedExprCompile.compile_plus e081 e079 e080 p079 p080 p081 rfl h079 h080 step081
#print axioms h081
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
