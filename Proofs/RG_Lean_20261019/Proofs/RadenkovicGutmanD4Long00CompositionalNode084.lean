/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode072
import Proofs.RadenkovicGutmanD4Long00CompositionalNode083
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e084 : NestedArithmetic.Expr 3 := .plus e072 e083
noncomputable def p084 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,-288,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2592,-6048,0],[-6048,-3144,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-125928,-80136,0],[-80136,-14096,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1622376,-458640,0],[-458640,-33736,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-10567104,-1498040,0],[-1498040,-47184,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-42391112,-3116240,0],[-3116240,-39968,0],[0,0]],[[0,0,0],[0,0],[0]],[[-115094424,-4370456,0],[-4370456,-20592],[0]],[[0,0,0],[0,0],[0]],[[-223244848,-4267296,0],[-4267296,-6280],[0]],[[0,0,0],[0,0],[0]],[[-320012352,-2949840,0],[-2949840,-1040],[0]],[[0,0,0],[0,0],[0]],[[-346499960,-1450432,0],[-1450432,-72],[0]],[[0,0,0],[0,0],[0]],[[-287303984,-503384,0],[-503384,0],[0]],[[0,0],[0]],[[-183782960,-120400],[-120400]],[[0,0],[0]],[[-90868576,-18872],[-18872]],[[0,0],[0]],[[-34597176,-1744],[-1744]],[[0,0],[0]],[[-10038840,-72],[-72]],[[0,0],[0]],[[-2177520,0],[0]],[[0]],[[-341600]],[[0]],[[-36584]],[[0]],[[-2392]],[[0]],[[-72]],[[0]],[[0]]]
theorem step084 : p084=NestedHorner.add p072 p083 := by decide +kernel
#print axioms step084
theorem h084 : NestedArithmetic.compile e084=p084 := StagedExprCompile.compile_plus e084 e072 e083 p072 p083 p084 rfl h072 h083 step084
#print axioms h084
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
