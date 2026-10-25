/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode041
import Proofs.RadenkovicGutmanD13Long00CompositionalNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e041 e042
noncomputable def p043 : NestedHorner.Poly 3 := [[[0],[0]],[[0,39],[39,-22]],[[0,0],[0]],[[972,-29],[-29]],[[0,0],[0]],[[5472,-320],[-320]],[[0,0],[0]],[[12018,-393],[-393]],[[0,0],[0]],[[12038,-163],[-163]],[[0,0],[0]],[[3456,-22],[-22]],[[0]],[[-3698]],[[0]],[[-3926]],[[0]],[[-1566]],[[0]],[[-296]],[[0]],[[-22]]]
theorem step043 : p043=NestedHorner.add p041 p042 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := StagedExprCompile.compile_plus e043 e041 e042 p041 p042 p043 rfl h041 h042 step043
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
