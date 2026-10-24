/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode036
import Proofs.RadenkovicGutmanD3Long00StagedUNode063
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e064 : NestedArithmetic.Expr 3 := .times e036 e063
noncomputable def p064 : NestedHorner.Poly 3 := [[[0],[0,-3]],[[0,0],[0,0]],[[-27,-45],[-45,-2]],[[0,0],[0]],[[-765,-168],[-168]],[[0,0],[0]],[[-4209,-210],[-210]],[[0,0],[0]],[[-10358,-110],[-110]],[[0,0],[0]],[[-14128,-25],[-25]],[[0,0],[0]],[[-11664,-2],[-2]],[[0]],[[-6043]],[[0]],[[-1970]],[[0]],[[-391]],[[0]],[[-43]],[[0]],[[-2]]]
theorem step064 : p064=NestedArithmetic.mul p036 p063 := by decide +kernel
#print axioms step064
theorem h064 : NestedArithmetic.compile e064=p064 := StagedExprCompile.compile_times e064 e036 e063 p036 p063 p064 rfl h036 h063 step064
#print axioms h064
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
