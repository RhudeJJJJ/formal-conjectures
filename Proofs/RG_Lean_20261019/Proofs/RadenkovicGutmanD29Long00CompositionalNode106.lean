/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode095
import Proofs.RadenkovicGutmanD29Long00CompositionalNode105
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e106 : NestedArithmetic.Expr 3 := .plus e095 e105
noncomputable def p106 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-2088,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-18792,-18792,0],[-18792,-18096,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-494856,-212976,0],[-212976,-61480,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-4885920,-1033560,0],[-1033560,-106256,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-26330376,-2846640,0],[-2846640,-103008,0],[0,0]],[[0,0,0],[0,0],[0]],[[-89983288,-4976632,0],[-4976632,-58000],[0]],[[0,0,0],[0,0],[0]],[[-210998896,-5841760,0],[-5841760,-18792],[0]],[[0,0,0],[0,0],[0]],[[-355768288,-4738832,0],[-4738832,-3248],[0]],[[0,0,0],[0,0],[0]],[[-444229656,-2686560,0],[-2686560,-232],[0]],[[0,0,0],[0,0],[0]],[[-418423600,-1060472,0],[-1060472,0],[0]],[[0,0],[0]],[[-300461808,-285360],[-285360]],[[0,0],[0]],[[-165161728,-49880],[-49880]],[[0,0],[0]],[[-69351992,-5104],[-5104]],[[0,0],[0]],[[-22043480,-232],[-232]],[[0,0],[0]],[[-5207472,0],[0]],[[0]],[[-885312]],[[0]],[[-102312]],[[0]],[[-7192]],[[0]],[[-232]],[[0]],[[0]]]
theorem step106 : p106=NestedHorner.add p095 p105 := by decide +kernel
#print axioms step106
theorem h106 : NestedArithmetic.compile e106=p106 := StagedExprCompile.compile_plus e106 e095 e105 p095 p105 p106 rfl h095 h105 step106
#print axioms h106
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
