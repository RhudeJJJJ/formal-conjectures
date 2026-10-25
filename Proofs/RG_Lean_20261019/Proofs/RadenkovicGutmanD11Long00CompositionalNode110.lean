/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode043
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e110 : NestedArithmetic.Expr 3 := .pow e043 2
noncomputable def p110 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,1089],[0,2178,-1188],[1089,-1188,324]],[[0,0,0],[0,0,0],[0,0]],[[0,54648,-1254],[54648,-32316,684],[-1254,684]],[[0,0,0],[0,0,0],[0,0]],[[685584,280584,-16535],[280584,-203278,9216],[-16535,9216]],[[0,0,0],[0,0,0],[0,0]],[[7829568,95868,-11326],[95868,-404180,11484],[-11326,11484]],[[0,0,0],[0,0,0],[0,0]],[[39904272,-2621368,68880],[-2621368,-260616,4788],[68880,4788]],[[0,0,0],[0,0,0],[0,0]],[[118539984,-8823620,167194],[-8823620,192692,648],[167194,648]],[[0,0,0],[0,0],[0]],[[223475716,-14024720,170541],[-14024720,428562],[170541]],[[0,0,0],[0,0],[0]],[[267749672,-12171992,94070],[-12171992,297076],[94070]],[[0,0,0],[0,0],[0]],[[177894676,-4559604,29173],[-4559604,103346],[29173]],[[0,0,0],[0,0],[0]],[[4921416,1685960,4788],[1685960,18216],[4788]],[[0,0,0],[0,0],[0]],[[-114645200,3083204,324],[3083204,1296],[324]],[[0,0],[0]],[[-114894640,1813460],[1813460]],[[0,0],[0]],[[-50838020,603772],[603772]],[[0,0],[0]],[[-826848,120324],[120324]],[[0,0],[0]],[[12944020,13428],[13428]],[[0,0],[0]],[[8589704,648],[648]],[[0]],[[3102460]],[[0]],[[708936]],[[0]],[[102600]],[[0]],[[8640]],[[0]],[[324]]]
theorem step110 : p110=NestedArithmetic.power p043 2 := by decide +kernel
#print axioms step110
theorem h110 : NestedArithmetic.compile e110=p110 := StagedExprCompile.compile_pow 2 e110 e043 p043 p110 rfl h043 step110
#print axioms h110
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
