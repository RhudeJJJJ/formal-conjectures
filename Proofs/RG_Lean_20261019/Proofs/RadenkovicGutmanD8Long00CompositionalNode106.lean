/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode095
import Proofs.RadenkovicGutmanD8Long00CompositionalNode105
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e106 : NestedArithmetic.Expr 3 := .plus e095 e105
noncomputable def p106 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-576,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-5184,-5184,0],[-5184,-4992,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-136512,-58752,0],[-58752,-16960,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1347840,-285120,0],[-285120,-29312,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-7263552,-785280,0],[-785280,-28416,0],[0,0]],[[0,0,0],[0,0],[0]],[[-24822976,-1372864,0],[-1372864,-16000],[0]],[[0,0,0],[0,0],[0]],[[-58206592,-1611520,0],[-1611520,-5184],[0]],[[0,0,0],[0,0],[0]],[[-98142976,-1307264,0],[-1307264,-896],[0]],[[0,0,0],[0,0],[0]],[[-122546112,-741120,0],[-741120,-64],[0]],[[0,0,0],[0,0],[0]],[[-115427200,-292544,0],[-292544,0],[0]],[[0,0],[0]],[[-82886016,-78720],[-78720]],[[0,0],[0]],[[-45561856,-13760],[-13760]],[[0,0],[0]],[[-19131584,-1408],[-1408]],[[0,0],[0]],[[-6080960,-64],[-64]],[[0,0],[0]],[[-1436544,0],[0]],[[0]],[[-244224]],[[0]],[[-28224]],[[0]],[[-1984]],[[0]],[[-64]],[[0]],[[0]]]
theorem step106 : p106=NestedHorner.add p095 p105 := by decide +kernel
#print axioms step106
theorem h106 : NestedArithmetic.compile e106=p106 := StagedExprCompile.compile_plus e106 e095 e105 p095 p105 p106 rfl h095 h105 step106
#print axioms h106
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
