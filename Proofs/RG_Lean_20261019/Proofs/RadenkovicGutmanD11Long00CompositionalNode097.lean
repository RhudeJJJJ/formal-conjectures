/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode051
import Proofs.RadenkovicGutmanD11Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e097 : NestedArithmetic.Expr 3 := .times e051 e057
noncomputable def p097 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-363],[0,-363]],[[0,0,0],[0,0,0],[0,0]],[[0,3267,-5445],[3267,-16335,-1639],[-5445,-1639]],[[0,0,0],[0,0,0],[0,0]],[[49005,-108405,-42339],[-108405,-121968,-2222],[-42339,-2222]],[[0,0,0],[0,0,0],[0,0]],[[-286605,-1330956,-131450],[-1330956,-363759,-1199],[-131450,-1199]],[[0,0,0],[0,0,0],[0,0]],[[-8423514,-6304397,-213917],[-6304397,-572748,-275],[-213917,-275]],[[0,0,0],[0,0,0],[0,0]],[[-58879227,-16741472,-201058],[-16741472,-525536,-22],[-201058,-22]],[[0,0,0],[0,0],[0]],[[-224288911,-28296829,-113091],[-28296829,-291346],[-113091]],[[0,0,0],[0,0],[0]],[[-555440380,-32330342,-37994],[-32330342,-97471],[-37994]],[[0,0,0],[0,0],[0]],[[-966484464,-25741221,-7271],[-25741221,-18832],[-7271]],[[0,0,0],[0,0],[0]],[[-1232592911,-14464747,-693],[-14464747,-1859],[-693]],[[0,0,0],[0,0],[0]],[[-1180907618,-5729482,-22],[-5729482,-66],[-22]],[[0,0],[0]],[[-861899148,-1574298],[-1574298]],[[0,0],[0]],[[-482260988,-289322],[-289322]],[[0,0],[0]],[[-206816753,-33088],[-33088]],[[0,0],[0]],[[-67507891,-2024],[-2024]],[[0,0],[0]],[[-16522440,-44],[-44]],[[0]],[[-2953500]],[[0]],[[-368885]],[[0]],[[-29777]],[[0]],[[-1331]],[[0]],[[-22]]]
theorem step097 : p097=NestedArithmetic.mul p051 p057 := by decide +kernel
#print axioms step097
theorem h097 : NestedArithmetic.compile e097=p097 := StagedExprCompile.compile_times e097 e051 e057 p051 p057 p097 rfl h051 h057 step097
#print axioms h097
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
