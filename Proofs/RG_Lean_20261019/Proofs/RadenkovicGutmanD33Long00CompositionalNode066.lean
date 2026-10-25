/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode065
import Proofs.RadenkovicGutmanD33Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e066 : NestedArithmetic.Expr 3 := .times e065 e064
noncomputable def p066 : NestedHorner.Poly 3 := [[[0],[0,-33]],[[0,0],[0,0]],[[-297,-495],[-495,-2]],[[0,0],[0]],[[-8235,-1668],[-1668]],[[0,0],[0]],[[-43119,-1830],[-1830]],[[0,0],[0]],[[-99998,-770],[-770]],[[0,0],[0]],[[-126808,-115],[-115]],[[0,0],[0]],[[-95424,-2],[-2]],[[0]],[[-43753]],[[0]],[[-12050]],[[0]],[[-1861]],[[0]],[[-133]],[[0]],[[-2]]]
theorem step066 : p066=NestedArithmetic.mul p065 p064 := by decide +kernel
#print axioms step066
theorem h066 : NestedArithmetic.compile e066=p066 := StagedExprCompile.compile_times e066 e065 e064 p065 p064 p066 rfl h065 h064 step066
#print axioms h066
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
