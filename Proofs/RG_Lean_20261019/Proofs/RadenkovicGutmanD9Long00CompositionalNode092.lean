/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode089
import Proofs.RadenkovicGutmanD9Long00CompositionalNode091
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e092 : NestedArithmetic.Expr 3 := .plus e089 e091
noncomputable def p092 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,486],[0,486,-126]],[[0,0,0],[0,0,0],[0,0]],[[0,0,5832],[0,19683,-108],[5832,-108]],[[0,0,0],[0,0,0],[0,0]],[[16767,160137,33534],[160137,102546,-3222],[33534,-3222]],[[0,0,0],[0,0,0],[0,0]],[[1342575,1440990,76464],[1440990,198531,-4122],[76464,-4122]],[[0,0,0],[0,0,0],[0,0]],[[14928462,5678343,83754],[5678343,149526,-1728],[83754,-1728]],[[0,0,0],[0,0,0],[0,0]],[[79650351,12864276,37386],[12864276,-30276,-234],[37386,-234]],[[0,0,0],[0,0],[0]],[[259362585,18485793,-8010],[18485793,-133290],[-8010]],[[0,0,0],[0,0],[0]],[[570925926,17479422,-16308],[17479422,-98037],[-16308]],[[0,0,0],[0,0],[0]],[[896490936,10812114,-7218],[10812114,-34542],[-7218]],[[0,0,0],[0,0],[0]],[[1034887077,4061736,-1422],[4061736,-6093],[-1422]],[[0,0,0],[0,0],[0]],[[892127790,624375,-108],[624375,-432],[-108]],[[0,0],[0]],[[576850014,-185526],[-185526]],[[0,0],[0]],[[277693128,-127809],[-127809]],[[0,0],[0]],[[97037433,-31644],[-31644]],[[0,0],[0]],[[23057469,-3897],[-3897]],[[0,0],[0]],[[2988342,-198],[-198]],[[0]],[[-98604]],[[0]],[[-125613]],[[0]],[[-24651]],[[0]],[[-2313]],[[0]],[[-90]]]
theorem step092 : p092=NestedHorner.add p089 p091 := by decide +kernel
#print axioms step092
theorem h092 : NestedArithmetic.compile e092=p092 := StagedExprCompile.compile_plus e092 e089 e091 p089 p091 p092 rfl h089 h091 step092
#print axioms h092
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
