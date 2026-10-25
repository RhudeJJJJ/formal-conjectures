/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode043
import Proofs.RadenkovicGutmanD42Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e096 : NestedArithmetic.Expr 3 := .times e043 e053
noncomputable def p096 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,5292],[0,5292,-3360]],[[0,0,0],[0,0,0],[0,0]],[[0,47628,47628],[47628,193536,-37548],[47628,-37548]],[[0,0,0],[0,0,0],[0,0]],[[1156680,1932336,61236],[1932336,271152,-133056],[61236,-133056]],[[0,0,0],[0,0,0],[0,0]],[[26580960,11285568,-530712],[11285568,-2033808,-135492],[-530712,-135492]],[[0,0,0],[0,0,0],[0,0]],[[210488544,25128936,-1930572],[25128936,-7568400,-51996],[-1930572,-51996]],[[0,0,0],[0,0,0],[0,0]],[[887412960,10498824,-2910096],[10498824,-11491200,-6720],[-2910096,-6720]],[[0,0,0],[0,0],[0]],[[2315614056,-67158672,-2414244],[-67158672,-9572976],[-2414244]],[[0,0,0],[0,0],[0]],[[3960396384,-174111000,-1178184],[-174111000,-4685520],[-1178184]],[[0,0,0],[0,0],[0]],[[4402150368,-223661676,-336420],[-223661676,-1340976],[-336420]],[[0,0,0],[0,0],[0]],[[2731692264,-181976172,-51996],[-181976172,-207648],[-51996]],[[0,0,0],[0,0],[0]],[[-115681944,-100054668,-3360],[-100054668,-13440],[-3360]],[[0,0],[0]],[[-2192283240,-37767240],[-37767240]],[[0,0],[0]],[[-2540971776,-9662604],[-9662604]],[[0,0],[0]],[[-1747422096,-1602888],[-1602888]],[[0,0],[0]],[[-832155240,-155652],[-155652]],[[0,0],[0]],[[-285490800,-6720],[-6720]],[[0]],[[-70751520]],[[0]],[[-12396216]],[[0]],[[-1459248]],[[0]],[[-103656]],[[0]],[[-3360]]]
theorem step096 : p096=NestedArithmetic.mul p043 p053 := by decide +kernel
#print axioms step096
theorem h096 : NestedArithmetic.compile e096=p096 := StagedExprCompile.compile_times e096 e043 e053 p043 p053 p096 rfl h043 h053 step096
#print axioms h096
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
