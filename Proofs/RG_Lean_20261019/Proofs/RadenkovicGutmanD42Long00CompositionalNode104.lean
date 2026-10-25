/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode092
import Proofs.RadenkovicGutmanD42Long00CompositionalNode103
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e104 : NestedArithmetic.Expr 3 := .plus e092 e103
noncomputable def p104 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-3024,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-27216,-27216,0],[-27216,-25452,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-709884,-301644,0],[-301644,-82488,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-6896988,-1419768,0],[-1419768,-131628,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-36364608,-3748500,0],[-3748500,-110712,0],[0,0]],[[0,0,0],[0,0],[0]],[[-120787212,-6176856,0],[-6176856,-46704],[0]],[[0,0,0],[0,0],[0]],[[-273004452,-6658596,0],[-6658596,-6216],[0]],[[0,0,0],[0,0],[0]],[[-438854472,-4748016,0],[-4748016,2100],[0]],[[0,0,0],[0,0],[0]],[[-514554432,-2175096,0],[-2175096,840],[0]],[[0,0,0],[0,0],[0]],[[-445151028,-563136,0],[-563136,84],[0]],[[0,0],[0]],[[-283653384,-29316],[-29316]],[[0,0],[0]],[[-130411848,31080],[31080]],[[0,0],[0]],[[-40640880,10668],[10668]],[[0,0],[0]],[[-6814836,1512],[1512]],[[0,0],[0]],[[439404,84],[84]],[[0]],[[603288]],[[0]],[[172368]],[[0]],[[26628]],[[0]],[[2268]],[[0]],[[84]]]
theorem step104 : p104=NestedHorner.add p092 p103 := by decide +kernel
#print axioms step104
theorem h104 : NestedArithmetic.compile e104=p104 := StagedExprCompile.compile_plus e104 e092 e103 p092 p103 p104 rfl h092 h103 step104
#print axioms h104
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
