/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode095
import Proofs.RadenkovicGutmanD5Long00CompositionalNode105
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e106 : NestedArithmetic.Expr 3 := .plus e095 e105
noncomputable def p106 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-360,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3240,-3240,0],[-3240,-3120,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-85320,-36720,0],[-36720,-10600,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-842400,-178200,0],[-178200,-18320,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-4539720,-490800,0],[-490800,-17760,0],[0,0]],[[0,0,0],[0,0],[0]],[[-15514360,-858040,0],[-858040,-10000],[0]],[[0,0,0],[0,0],[0]],[[-36379120,-1007200,0],[-1007200,-3240],[0]],[[0,0,0],[0,0],[0]],[[-61339360,-817040,0],[-817040,-560],[0]],[[0,0,0],[0,0],[0]],[[-76591320,-463200,0],[-463200,-40],[0]],[[0,0,0],[0,0],[0]],[[-72142000,-182840,0],[-182840,0],[0]],[[0,0],[0]],[[-51803760,-49200],[-49200]],[[0,0],[0]],[[-28476160,-8600],[-8600]],[[0,0],[0]],[[-11957240,-880],[-880]],[[0,0],[0]],[[-3800600,-40],[-40]],[[0,0],[0]],[[-897840,0],[0]],[[0]],[[-152640]],[[0]],[[-17640]],[[0]],[[-1240]],[[0]],[[-40]],[[0]],[[0]]]
theorem step106 : p106=NestedHorner.add p095 p105 := by decide +kernel
#print axioms step106
theorem h106 : NestedArithmetic.compile e106=p106 := StagedExprCompile.compile_plus e106 e095 e105 p095 p105 p106 rfl h095 h105 step106
#print axioms h106
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
