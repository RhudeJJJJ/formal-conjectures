/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode073
import Proofs.RadenkovicGutmanD33Long00CompositionalNode084
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e085 : NestedArithmetic.Expr 3 := .plus e073 e084
noncomputable def p085 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,-2376,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-21384,-256608,0],[-256608,-60390,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-4449654,-3658446,0],[-3658446,-414876,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-69093486,-22250052,0],[-22250052,-1292742,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-491920704,-76343850,0],[-76343850,-2142492,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2088576534,-165170676,0],[-165170676,-2029368,0],[0,0]],[[0,0,0],[0,0],[0]],[[-5907282810,-239005338,0],[-239005338,-1126884],[0]],[[0,0,0],[0,0],[0]],[[-11824328868,-239298840,0],[-239298840,-361878],[0]],[[0,0,0],[0,0],[0]],[[-17382173952,-168835524,0],[-168835524,-62172],[0]],[[0,0,0],[0,0],[0]],[[-19215435162,-84430104,0],[-84430104,-4422],[0]],[[0,0,0],[0,0],[0]],[[-16212818820,-29720130,0],[-29720130,0],[0]],[[0,0],[0]],[[-10526440980,-7194660],[-7194660]],[[0,0],[0]],[[-5271942456,-1139490],[-1139490]],[[0,0],[0]],[[-2029873098,-106260],[-106260]],[[0,0],[0]],[[-594842226,-4422],[-4422]],[[0,0],[0]],[[-130163220,0],[0]],[[0]],[[-20580120]],[[0]],[[-2219646]],[[0]],[[-146058]],[[0]],[[-4422]],[[0]],[[0]]]
theorem step085 : p085=NestedHorner.add p073 p084 := by decide +kernel
#print axioms step085
theorem h085 : NestedArithmetic.compile e085=p085 := StagedExprCompile.compile_plus e085 e073 e084 p073 p084 p085 rfl h073 h084 step085
#print axioms h085
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
