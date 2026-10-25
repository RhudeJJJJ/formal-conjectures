/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode093
import Proofs.RadenkovicGutmanD7Long00CompositionalNode094
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e095 : NestedArithmetic.Expr 3 := .plus e093 e094
noncomputable def p095 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,49]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-441],[0,-882,1386],[-441,1386,14]],[[0,0,0],[0,0,0],[0,0]],[[-3969,-15309,4683],[-15309,25494,4788],[4683,4788]],[[0,0,0],[0,0,0],[0,0]],[[-194670,13419,41069],[13419,182602,5516],[41069,5516]],[[0,0,0],[0,0,0],[0,0]],[[-1269513,853713,118930],[853713,494634,2576],[118930,2576]],[[0,0,0],[0,0,0],[0,0]],[[-1343244,4451832,177828],[4451832,709940,490],[177828,490]],[[0,0,0],[0,0,0],[0,0]],[[16800077,11723789,154812],[11723789,600236,28],[154812,28]],[[0,0,0],[0,0],[0]],[[94644116,19185075,81627],[19185075,309946],[81627]],[[0,0,0],[0,0],[0]],[[264288038,21113624,25998],[21113624,97426],[25998]],[[0,0,0],[0,0],[0]],[[481814970,16210285,4767],[16210285,17794],[4767]],[[0,0,0],[0,0],[0]],[[625574544,8814995,441],[8814995,1666],[441]],[[0,0,0],[0,0],[0]],[[602306544,3394958,14],[3394958,56],[14]],[[0,0],[0]],[[439097666,912275],[912275]],[[0,0],[0]],[[244779262,165207],[165207]],[[0,0],[0]],[[104532757,18837],[18837]],[[0,0],[0]],[[34012076,1176],[1176]],[[0,0],[0]],[[8318058,28],[28]],[[0]],[[1492134]],[[0]],[[188391]],[[0]],[[15582]],[[0]],[[735]],[[0]],[[14]]]
theorem step095 : p095=NestedHorner.add p093 p094 := by decide +kernel
#print axioms step095
theorem h095 : NestedArithmetic.compile e095=p095 := StagedExprCompile.compile_plus e095 e093 e094 p093 p094 p095 rfl h093 h094 step095
#print axioms h095
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
