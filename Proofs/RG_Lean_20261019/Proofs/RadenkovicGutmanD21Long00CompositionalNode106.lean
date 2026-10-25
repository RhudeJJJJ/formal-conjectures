/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode095
import Proofs.RadenkovicGutmanD21Long00CompositionalNode105
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e106 : NestedArithmetic.Expr 3 := .plus e095 e105
noncomputable def p106 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-1512,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-13608,-13608,0],[-13608,-13104,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-358344,-154224,0],[-154224,-44520,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3538080,-748440,0],[-748440,-76944,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-19066824,-2061360,0],[-2061360,-74592,0],[0,0]],[[0,0,0],[0,0],[0]],[[-65160312,-3603768,0],[-3603768,-42000],[0]],[[0,0,0],[0,0],[0]],[[-152792304,-4230240,0],[-4230240,-13608],[0]],[[0,0,0],[0,0],[0]],[[-257625312,-3431568,0],[-3431568,-2352],[0]],[[0,0,0],[0,0],[0]],[[-321683544,-1945440,0],[-1945440,-168],[0]],[[0,0,0],[0,0],[0]],[[-302996400,-767928,0],[-767928,0],[0]],[[0,0],[0]],[[-217575792,-206640],[-206640]],[[0,0],[0]],[[-119599872,-36120],[-36120]],[[0,0],[0]],[[-50220408,-3696],[-3696]],[[0,0],[0]],[[-15962520,-168],[-168]],[[0,0],[0]],[[-3770928,0],[0]],[[0]],[[-641088]],[[0]],[[-74088]],[[0]],[[-5208]],[[0]],[[-168]],[[0]],[[0]]]
theorem step106 : p106=NestedHorner.add p095 p105 := by decide +kernel
#print axioms step106
theorem h106 : NestedArithmetic.compile e106=p106 := StagedExprCompile.compile_plus e106 e095 e105 p095 p105 p106 rfl h095 h105 step106
#print axioms h106
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
