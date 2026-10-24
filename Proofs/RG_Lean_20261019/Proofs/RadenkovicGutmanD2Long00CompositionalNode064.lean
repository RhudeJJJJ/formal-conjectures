/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode063
import Proofs.RadenkovicGutmanD2Long00CompositionalNode062
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e064 : NestedArithmetic.Expr 3 := .times e063 e062
noncomputable def p064 : NestedHorner.Poly 3 := [[[0],[0,-2]],[[0,0],[0,0]],[[-18,-30],[-30,-2]],[[0,0],[0]],[[-516,-118],[-118]],[[0,0],[0]],[[-2912,-156],[-156]],[[0,0],[0]],[[-7370,-88],[-88]],[[0,0],[0]],[[-10372,-22],[-22]],[[0,0],[0]],[[-8872,-2],[-2]],[[0]],[[-4786]],[[0]],[[-1634]],[[0]],[[-342]],[[0]],[[-40]],[[0]],[[-2]]]
theorem step064 : p064=NestedArithmetic.mul p063 p062 := by decide +kernel
#print axioms step064
theorem h064 : NestedArithmetic.compile e064=p064 := StagedExprCompile.compile_times e064 e063 e062 p063 p062 p064 rfl h063 h062 step064
#print axioms h064
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
