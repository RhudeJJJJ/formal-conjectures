/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode043
import Proofs.RadenkovicGutmanD35Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e067 : NestedArithmetic.Expr 3 := .times e043 e061
noncomputable def p067 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,11025],[0,22050,-13860],[11025,-13860,4356]],[[0,0,0],[0,0,0],[0,0]],[[0,371385,-29190],[371385,-291822,18348],[-29190,18348]],[[0,0,0],[0,0,0],[0,0]],[[2507436,942867,-195719],[942867,-1293130,135168],[-195719,135168]],[[0,0,0],[0,0,0],[0,0]],[[13411872,-4586301,31202],[-4586301,-525062,159324],[31202,159324]],[[0,0,0],[0,0,0],[0,0]],[[-20696958,-23138736,1280592],[-23138736,4850724,65076],[1280592,65076]],[[0,0,0],[0,0,0],[0,0]],[[-380174034,-31068029,2595130],[-31068029,10559228,8712],[2595130,8712]],[[0,0,0],[0,0],[0]],[[-1506897034,20818207,2484861],[20818207,10186494],[2484861]],[[0,0,0],[0,0],[0]],[[-3273095560,126476300,1325270],[126476300,5411122],[1325270]],[[0,0,0],[0,0],[0]],[[-4392528138,200138631,402373],[200138631,1631990],[402373]],[[0,0,0],[0,0],[0]],[[-3475636352,182160977,65076],[182160977,262086],[65076]],[[0,0,0],[0,0],[0]],[[-858093908,107920680,4356],[107920680,17424],[4356]],[[0,0],[0]],[[1545018070,43031345],[43031345]],[[0,0],[0]],[[2339328890,11487805],[11487805]],[[0,0],[0]],[[1784664222,1972075],[1972075]],[[0,0],[0]],[[905702406,197010],[197010]],[[0,0],[0]],[[325308756,8712],[8712]],[[0]],[[83557210]],[[0]],[[15073940]],[[0]],[[1818588]],[[0]],[[131934]],[[0]],[[4356]]]
theorem step067 : p067=NestedArithmetic.mul p043 p061 := by decide +kernel
#print axioms step067
theorem h067 : NestedArithmetic.compile e067=p067 := StagedExprCompile.compile_times e067 e043 e061 p043 p061 p067 rfl h043 h061 step067
#print axioms h067
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
