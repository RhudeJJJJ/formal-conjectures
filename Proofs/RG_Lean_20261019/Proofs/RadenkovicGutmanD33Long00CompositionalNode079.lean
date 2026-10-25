/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode033
import Proofs.RadenkovicGutmanD33Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e079 : NestedArithmetic.Expr 3 := .times e033 e074
noncomputable def p079 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,3267],[0,3267]],[[0,0,0],[0,0,0],[0,0]],[[0,-29403,29403],[-29403,107811,14157],[29403,14157]],[[0,0,0],[0,0,0],[0,0]],[[-441045,323433,205821],[323433,738342,17424],[205821,17424]],[[0,0,0],[0,0,0],[0,0]],[[-2793285,4547664,568458],[4547664,1985247,7623],[568458,7623]],[[0,0,0],[0,0,0],[0,0]],[[1528956,20581011,824373],[20581011,2798730,1089],[824373,1089]],[[0,0,0],[0,0],[0]],[[71942607,50958666,692604],[50958666,2286900],[692604]],[[0,0,0],[0,0],[0]],[[341977581,80053479,347391],[80053479,1117314],[347391]],[[0,0,0],[0,0],[0]],[[905144130,85175046,102366],[85175046,321255],[102366]],[[0,0,0],[0,0],[0]],[[1606645260,63302481,16335],[63302481,50094],[16335]],[[0,0,0],[0,0],[0]],[[2051975475,33222123,1089],[33222123,3267],[1089]],[[0,0],[0]],[[1951814700,12251250],[12251250]],[[0,0],[0]],[[1407253716,3103650],[3103650]],[[0,0],[0]],[[774749448,514008],[514008]],[[0,0],[0]],[[325485765,50094],[50094]],[[0,0],[0]],[[103469157,2178],[2178]],[[0]],[[24443694]],[[0]],[[4155624]],[[0]],[[480249]],[[0]],[[33759]],[[0]],[[1089]]]
theorem step079 : p079=NestedArithmetic.mul p033 p074 := by decide +kernel
#print axioms step079
theorem h079 : NestedArithmetic.compile e079=p079 := StagedExprCompile.compile_times e079 e033 e074 p033 p074 p079 rfl h033 h074 step079
#print axioms h079
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
