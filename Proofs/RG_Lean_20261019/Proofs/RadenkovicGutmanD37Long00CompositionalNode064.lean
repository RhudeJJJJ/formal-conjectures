/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode062
import Proofs.RadenkovicGutmanD37Long00CompositionalNode063
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e064 : NestedArithmetic.Expr 3 := .plus e062 e063
noncomputable def p064 : NestedHorner.Poly 3 := [[[0],[0,37]],[[0,0],[0,0]],[[333,555],[555,2]],[[0,0],[0]],[[9231,1868],[1868]],[[0,0],[0]],[[48307,2046],[2046]],[[0,0],[0]],[[111950,858],[858]],[[0,0],[0]],[[141832,127],[127]],[[0,0],[0]],[[106592,2],[2]],[[0]],[[48781]],[[0]],[[13394]],[[0]],[[2057]],[[0]],[[145]],[[0]],[[2]]]
theorem step064 : p064=NestedHorner.add p062 p063 := by decide +kernel
#print axioms step064
theorem h064 : NestedArithmetic.compile e064=p064 := StagedExprCompile.compile_plus e064 e062 e063 p062 p063 p064 rfl h062 h063 step064
#print axioms h064
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
