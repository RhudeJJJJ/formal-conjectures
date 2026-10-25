/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode033
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .pow e033 2
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,400]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-7200,7200],[0,7200]],[[0,0,0],[0,0,0],[0,0]],[[32400,-64800,32400],[-64800,67200,19200],[32400,19200]],[[0,0,0],[0,0,0],[0,0]],[[-21600,-151200,172800],[-151200,479200,17600],[172800,17600]],[[0,0,0],[0,0,0],[0,0]],[[-1198800,1101600,388800],[1101600,1188800,6400],[388800,6400]],[[0,0,0],[0,0,0],[0,0]],[[-3300000,6902400,480000],[6902400,1564800,800],[480000,800]],[[0,0,0],[0,0],[0]],[[6946000,18263200,354400],[18263200,1217600],[354400]],[[0,0,0],[0,0],[0]],[[65905600,29212000,160000],[29212000,575200],[160000]],[[0,0,0],[0,0],[0]],[[205909600,31236800,43200],[31236800,161600],[43200]],[[0,0,0],[0,0],[0]],[[395925600,23244800,6400],[23244800,24800],[6400]],[[0,0,0],[0,0],[0]],[[532873600,12202400,400],[12202400,1600],[400]],[[0,0],[0]],[[528412800,4500000],[4500000]],[[0,0],[0]],[[395388800,1140000],[1140000]],[[0,0],[0]],[[225460000,188800],[188800]],[[0,0],[0]],[[98014800,18400],[18400]],[[0,0],[0]],[[32225600,800],[800]],[[0]],[[7871200]],[[0]],[[1383200]],[[0]],[[165200]],[[0]],[[12000]],[[0]],[[400]]]
theorem step113 : p113=NestedArithmetic.power p033 2 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_pow 2 e113 e033 p033 p113 rfl h033 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
