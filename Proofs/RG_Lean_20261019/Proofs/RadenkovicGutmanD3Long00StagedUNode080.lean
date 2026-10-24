/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode076
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e080 : NestedArithmetic.Expr 3 := .scaled -1 e076
noncomputable def p080 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,-9]],[[0,0],[0,0,0],[0,0]],[[0,0,-81],[0,-162,-162],[-81,-162]],[[0,0,0],[0,0,0],[0,0]],[[729,-2673,-1431],[-2673,-4320,-432],[-1431,-432]],[[0,0,0],[0,0,0],[0,0]],[[-9234,-43011,-6273],[-43011,-20322,-396],[-6273,-396]],[[0,0,0],[0,0,0],[0,0]],[[-260253,-247779,-12870],[-247779,-43236,-144],[-12870,-144]],[[0,0,0],[0,0,0],[0,0]],[[-2005614,-762714,-14796],[-762714,-51192,-18],[-14796,-18]],[[0,0,0],[0,0],[0]],[[-8345151,-1460547,-10224],[-1460547,-36396],[-10224]],[[0,0,0],[0,0],[0]],[[-22376700,-1874943,-4329],[-1874943,-15858],[-4329]],[[0,0,0],[0,0],[0]],[[-41991210,-1679220,-1098],[-1679220,-4140],[-1098]],[[0,0,0],[0,0],[0]],[[-57756762,-1070379,-153],[-1070379,-594],[-153]],[[0,0,0],[0,0],[0]],[[-59869530,-488313,-9],[-488313,-36],[-9]],[[0,0],[0]],[[-47554740,-158184],[-158184]],[[0,0],[0]],[[-29200770,-35505],[-35505]],[[0,0],[0]],[[-13895442,-5247],[-5247]],[[0,0],[0]],[[-5105691,-459],[-459]],[[0,0],[0]],[[-1433484,-18],[-18]],[[0]],[[-301590]],[[0]],[[-45990]],[[0]],[[-4797]],[[0]],[[-306]],[[0]],[[-9]]]
theorem step080 : p080=NestedHorner.scale -1 p076 := by decide +kernel
#print axioms step080
theorem h080 : NestedArithmetic.compile e080=p080 := by
  change NestedHorner.scale -1 (NestedArithmetic.compile e076)=p080
  rw [h076]
  exact step080.symm
#print axioms h080
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
