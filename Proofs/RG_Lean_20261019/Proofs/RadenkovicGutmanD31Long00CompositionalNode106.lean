/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode095
import Proofs.RadenkovicGutmanD31Long00CompositionalNode105
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e106 : NestedArithmetic.Expr 3 := .plus e095 e105
noncomputable def p106 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-2232,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-20088,-20088,0],[-20088,-19344,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-528984,-227664,0],[-227664,-65720,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-5222880,-1104840,0],[-1104840,-113584,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-28146264,-3042960,0],[-3042960,-110112,0],[0,0]],[[0,0,0],[0,0],[0]],[[-96189032,-5319848,0],[-5319848,-62000],[0]],[[0,0,0],[0,0],[0]],[[-225550544,-6244640,0],[-6244640,-20088],[0]],[[0,0,0],[0,0],[0]],[[-380304032,-5065648,0],[-5065648,-3472],[0]],[[0,0,0],[0,0],[0]],[[-474866184,-2871840,0],[-2871840,-248],[0]],[[0,0,0],[0,0],[0]],[[-447280400,-1133608,0],[-1133608,0],[0]],[[0,0],[0]],[[-321183312,-305040],[-305040]],[[0,0],[0]],[[-176552192,-53320],[-53320]],[[0,0],[0]],[[-74134888,-5456],[-5456]],[[0,0],[0]],[[-23563720,-248],[-248]],[[0,0],[0]],[[-5566608,0],[0]],[[0]],[[-946368]],[[0]],[[-109368]],[[0]],[[-7688]],[[0]],[[-248]],[[0]],[[0]]]
theorem step106 : p106=NestedHorner.add p095 p105 := by decide +kernel
#print axioms step106
theorem h106 : NestedArithmetic.compile e106=p106 := StagedExprCompile.compile_plus e106 e095 e105 p095 p105 p106 rfl h095 h105 step106
#print axioms h106
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
