/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode041
import Proofs.RadenkovicGutmanD40Long00CompositionalNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e041 e042
noncomputable def p043 : NestedHorner.Poly 3 := [[[0],[0]],[[0,120],[120,-76]],[[0,0],[0]],[[2916,-164],[-164]],[[0,0],[0]],[[15516,-1184],[-1184]],[[0,0],[0]],[[31188,-1392],[-1392]],[[0,0],[0]],[[25160,-568],[-568]],[[0,0],[0]],[[-3024,-76],[-76]],[[0]],[[-20816]],[[0]],[[-16076]],[[0]],[[-5832]],[[0]],[[-1052]],[[0]],[[-76]]]
theorem step043 : p043=NestedHorner.add p041 p042 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := StagedExprCompile.compile_plus e043 e041 e042 p041 p042 p043 rfl h041 h042 step043
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
