/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode033
import Proofs.RadenkovicGutmanD15Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e079 : NestedArithmetic.Expr 3 := .times e033 e074
noncomputable def p079 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,675],[0,675]],[[0,0,0],[0,0,0],[0,0]],[[0,-6075,6075],[-6075,22275,2925],[6075,2925]],[[0,0,0],[0,0,0],[0,0]],[[-91125,66825,42525],[66825,152550,3600],[42525,3600]],[[0,0,0],[0,0,0],[0,0]],[[-577125,939600,117450],[939600,410175,1575],[117450,1575]],[[0,0,0],[0,0,0],[0,0]],[[315900,4252275,170325],[4252275,578250,225],[170325,225]],[[0,0,0],[0,0],[0]],[[14864175,10528650,143100],[10528650,472500],[143100]],[[0,0,0],[0,0],[0]],[[70656525,16539975,71775],[16539975,230850],[71775]],[[0,0,0],[0,0],[0]],[[187013250,17598150,21150],[17598150,66375],[21150]],[[0,0,0],[0,0],[0]],[[331951500,13079025,3375],[13079025,10350],[3375]],[[0,0,0],[0,0],[0]],[[423961875,6864075,225],[6864075,675],[225]],[[0,0],[0]],[[403267500,2531250],[2531250]],[[0,0],[0]],[[290754900,641250],[641250]],[[0,0],[0]],[[160072200,106200],[106200]],[[0,0],[0]],[[67249125,10350],[10350]],[[0,0],[0]],[[21377925,450],[450]],[[0]],[[5050350]],[[0]],[[858600]],[[0]],[[99225]],[[0]],[[6975]],[[0]],[[225]]]
theorem step079 : p079=NestedArithmetic.mul p033 p074 := by decide +kernel
#print axioms step079
theorem h079 : NestedArithmetic.compile e079=p079 := StagedExprCompile.compile_times e079 e033 e074 p033 p074 p079 rfl h033 h074 step079
#print axioms h079
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
