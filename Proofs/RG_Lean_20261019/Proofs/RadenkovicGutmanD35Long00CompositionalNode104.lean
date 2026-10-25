/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode092
import Proofs.RadenkovicGutmanD35Long00CompositionalNode103
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e104 : NestedArithmetic.Expr 3 := .plus e092 e103
noncomputable def p104 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-2520,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-22680,-22680,0],[-22680,-21210,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-591570,-251370,0],[-251370,-68740,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-5747490,-1183140,0],[-1183140,-109690,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-30303840,-3123750,0],[-3123750,-92260,0],[0,0]],[[0,0,0],[0,0],[0]],[[-100656010,-5147380,0],[-5147380,-38920],[0]],[[0,0,0],[0,0],[0]],[[-227503710,-5548830,0],[-5548830,-5180],[0]],[[0,0,0],[0,0],[0]],[[-365712060,-3956680,0],[-3956680,1750],[0]],[[0,0,0],[0,0],[0]],[[-428795360,-1812580,0],[-1812580,700],[0]],[[0,0,0],[0,0],[0]],[[-370959190,-469280,0],[-469280,70],[0]],[[0,0],[0]],[[-236377820,-24430],[-24430]],[[0,0],[0]],[[-108676540,25900],[25900]],[[0,0],[0]],[[-33867400,8890],[8890]],[[0,0],[0]],[[-5679030,1260],[1260]],[[0,0],[0]],[[366170,70],[70]],[[0]],[[502740]],[[0]],[[143640]],[[0]],[[22190]],[[0]],[[1890]],[[0]],[[70]]]
theorem step104 : p104=NestedHorner.add p092 p103 := by decide +kernel
#print axioms step104
theorem h104 : NestedArithmetic.compile e104=p104 := StagedExprCompile.compile_plus e104 e092 e103 p092 p103 p104 rfl h092 h103 step104
#print axioms h104
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
