/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode036
import Proofs.RadenkovicGutmanD3Long00StagedUNode203
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e204 : NestedArithmetic.Expr 3 := .times e036 e203
noncomputable def p204 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-43,0],[0,0]],[[0,0],[0,0]],[[-391,0],[0,0]],[[0,0],[0,0]],[[-1970,0],[0,0]],[[0,0],[0,0]],[[-6043,0],[0,0]],[[0,0],[0,0]],[[-11664,-2],[-2,0]],[[0,0],[0,0]],[[-14128,-25],[-25,0]],[[0,0],[0,0]],[[-10358,-110],[-110,0]],[[0,0],[0,0]],[[-4209,-210],[-210,0]],[[0,0],[0,0]],[[-765,-168],[-168,0]],[[0,0],[0,0]],[[-27,-45],[-45,-2]],[[0],[0,0]],[[0],[0,-3]]]
theorem step204 : p204=NestedArithmetic.mul p036 p203 := by decide +kernel
#print axioms step204
theorem h204 : NestedArithmetic.compile e204=p204 := StagedExprCompile.compile_times e204 e036 e203 p036 p203 p204 rfl h036 h203 step204
#print axioms h204
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
