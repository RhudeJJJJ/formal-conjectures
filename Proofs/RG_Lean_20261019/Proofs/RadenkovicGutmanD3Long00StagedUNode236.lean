/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode233
import Proofs.RadenkovicGutmanD3Long00StagedUNode235
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e236 : NestedArithmetic.Expr 3 := .plus e233 e235
noncomputable def p236 : NestedHorner.Poly 3 := [[[-9],[0],[0]],[[0,0],[0,0],[0]],[[-297,0,0],[0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-4509,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-41760,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-263790,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1203813,-9,0],[-9,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-4101363,-216,0],[-216,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-10632312,-2313,0],[-2313,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-21183930,-14580,0],[-14580,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-32545206,-60111,0],[-60111,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-38456451,-170370,0],[-170370,-9,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-34660044,-339732,0],[-339732,-126,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-23469966,-479844,0],[-479844,-729,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-11656161,-477153,0],[-477153,-2250,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-4088205,-327888,0],[-327888,-3996,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-951588,-150435,0],[-150435,-4122,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-130977,-43416,0],[-43416,-2385,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-8019,-7047,0],[-7047,-702,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,-486,0],[-486,-81,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0],[0,0,0],[0,0]]]
theorem step236 : p236=NestedHorner.add p233 p235 := by decide +kernel
#print axioms step236
theorem h236 : NestedArithmetic.compile e236=p236 := StagedExprCompile.compile_plus e236 e233 e235 p233 p235 p236 rfl h233 h235 step236
#print axioms h236
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
