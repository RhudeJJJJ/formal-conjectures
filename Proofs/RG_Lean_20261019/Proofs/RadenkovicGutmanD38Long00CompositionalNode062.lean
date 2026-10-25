/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode044
import Proofs.RadenkovicGutmanD38Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e062 : NestedArithmetic.Expr 3 := .times e044 e052
noncomputable def p062 : NestedHorner.Poly 3 := [[[0],[0,38]],[[0,0],[0,0]],[[342,342],[342,2]],[[0,0],[0]],[[6060,930],[930]],[[0,0],[0]],[[26804,884],[884]],[[0,0],[0]],[[55734,348],[348]],[[0,0],[0]],[[65332,54],[54]],[[0,0],[0]],[[46456,2],[2]],[[0]],[[20550]],[[0]],[[5598]],[[0]],[[890]],[[0]],[[72]],[[0]],[[2]]]
theorem step062 : p062=NestedArithmetic.mul p044 p052 := by decide +kernel
#print axioms step062
theorem h062 : NestedArithmetic.compile e062=p062 := StagedExprCompile.compile_times e062 e044 e052 p044 p052 p062 rfl h044 h052 step062
#print axioms h062
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
