/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode041
import Proofs.RadenkovicGutmanD38Long00CompositionalNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e041 e042
noncomputable def p043 : NestedHorner.Poly 3 := [[[0],[0]],[[0,114],[114,-72]],[[0,0],[0]],[[2772,-154],[-154]],[[0,0],[0]],[[14772,-1120],[-1120]],[[0,0],[0]],[[29768,-1318],[-1318]],[[0,0],[0]],[[24188,-538],[-538]],[[0,0],[0]],[[-2544,-72],[-72]],[[0]],[[-19548]],[[0]],[[-15176]],[[0]],[[-5516]],[[0]],[[-996]],[[0]],[[-72]]]
theorem step043 : p043=NestedHorner.add p041 p042 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := StagedExprCompile.compile_plus e043 e041 e042 p041 p042 p043 rfl h041 h042 step043
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
