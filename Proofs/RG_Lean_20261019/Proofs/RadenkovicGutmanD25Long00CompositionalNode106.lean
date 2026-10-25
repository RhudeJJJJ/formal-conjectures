/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode095
import Proofs.RadenkovicGutmanD25Long00CompositionalNode105
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e106 : NestedArithmetic.Expr 3 := .plus e095 e105
noncomputable def p106 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-1800,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-16200,-16200,0],[-16200,-15600,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-426600,-183600,0],[-183600,-53000,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-4212000,-891000,0],[-891000,-91600,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-22698600,-2454000,0],[-2454000,-88800,0],[0,0]],[[0,0,0],[0,0],[0]],[[-77571800,-4290200,0],[-4290200,-50000],[0]],[[0,0,0],[0,0],[0]],[[-181895600,-5036000,0],[-5036000,-16200],[0]],[[0,0,0],[0,0],[0]],[[-306696800,-4085200,0],[-4085200,-2800],[0]],[[0,0,0],[0,0],[0]],[[-382956600,-2316000,0],[-2316000,-200],[0]],[[0,0,0],[0,0],[0]],[[-360710000,-914200,0],[-914200,0],[0]],[[0,0],[0]],[[-259018800,-246000],[-246000]],[[0,0],[0]],[[-142380800,-43000],[-43000]],[[0,0],[0]],[[-59786200,-4400],[-4400]],[[0,0],[0]],[[-19003000,-200],[-200]],[[0,0],[0]],[[-4489200,0],[0]],[[0]],[[-763200]],[[0]],[[-88200]],[[0]],[[-6200]],[[0]],[[-200]],[[0]],[[0]]]
theorem step106 : p106=NestedHorner.add p095 p105 := by decide +kernel
#print axioms step106
theorem h106 : NestedArithmetic.compile e106=p106 := StagedExprCompile.compile_plus e106 e095 e105 p095 p105 p106 rfl h095 h105 step106
#print axioms h106
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
