/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode033
import Proofs.RadenkovicGutmanD21Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e079 : NestedArithmetic.Expr 3 := .times e033 e074
noncomputable def p079 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,1323],[0,1323]],[[0,0,0],[0,0,0],[0,0]],[[0,-11907,11907],[-11907,43659,5733],[11907,5733]],[[0,0,0],[0,0,0],[0,0]],[[-178605,130977,83349],[130977,298998,7056],[83349,7056]],[[0,0,0],[0,0,0],[0,0]],[[-1131165,1841616,230202],[1841616,803943,3087],[230202,3087]],[[0,0,0],[0,0,0],[0,0]],[[619164,8334459,333837],[8334459,1133370,441],[333837,441]],[[0,0,0],[0,0],[0]],[[29133783,20636154,280476],[20636154,926100],[280476]],[[0,0,0],[0,0],[0]],[[138486789,32418351,140679],[32418351,452466],[140679]],[[0,0,0],[0,0],[0]],[[366545970,34492374,41454],[34492374,130095],[41454]],[[0,0,0],[0,0],[0]],[[650624940,25634889,6615],[25634889,20286],[6615]],[[0,0,0],[0,0],[0]],[[830965275,13453587,441],[13453587,1323],[441]],[[0,0],[0]],[[790404300,4961250],[4961250]],[[0,0],[0]],[[569879604,1256850],[1256850]],[[0,0],[0]],[[313741512,208152],[208152]],[[0,0],[0]],[[131808285,20286],[20286]],[[0,0],[0]],[[41900733,882],[882]],[[0]],[[9898686]],[[0]],[[1682856]],[[0]],[[194481]],[[0]],[[13671]],[[0]],[[441]]]
theorem step079 : p079=NestedArithmetic.mul p033 p074 := by decide +kernel
#print axioms step079
theorem h079 : NestedArithmetic.compile e079=p079 := StagedExprCompile.compile_times e079 e033 e074 p033 p074 p079 rfl h033 h074 step079
#print axioms h079
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
