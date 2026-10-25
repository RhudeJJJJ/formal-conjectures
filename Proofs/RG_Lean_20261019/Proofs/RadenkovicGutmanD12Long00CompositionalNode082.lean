/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode078
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e082 : NestedArithmetic.Expr 3 := .scaled (-1) e078
noncomputable def p082 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,-144]],[[0,0],[0,0,0],[0,0]],[[0,0,-1296],[0,-2592,-2592],[-1296,-2592]],[[0,0,0],[0,0,0],[0,0]],[[11664,-42768,-22896],[-42768,-69120,-6912],[-22896,-6912]],[[0,0,0],[0,0,0],[0,0]],[[-147744,-688176,-100368],[-688176,-325152,-6336],[-100368,-6336]],[[0,0,0],[0,0,0],[0,0]],[[-4164048,-3964464,-205920],[-3964464,-691776,-2304],[-205920,-2304]],[[0,0,0],[0,0,0],[0,0]],[[-32089824,-12203424,-236736],[-12203424,-819072,-288],[-236736,-288]],[[0,0,0],[0,0],[0]],[[-133522416,-23368752,-163584],[-23368752,-582336],[-163584]],[[0,0,0],[0,0],[0]],[[-358027200,-29999088,-69264],[-29999088,-253728],[-69264]],[[0,0,0],[0,0],[0]],[[-671859360,-26867520,-17568],[-26867520,-66240],[-17568]],[[0,0,0],[0,0],[0]],[[-924108192,-17126064,-2448],[-17126064,-9504],[-2448]],[[0,0,0],[0,0],[0]],[[-957912480,-7813008,-144],[-7813008,-576],[-144]],[[0,0],[0]],[[-760875840,-2530944],[-2530944]],[[0,0],[0]],[[-467212320,-568080],[-568080]],[[0,0],[0]],[[-222327072,-83952],[-83952]],[[0,0],[0]],[[-81691056,-7344],[-7344]],[[0,0],[0]],[[-22935744,-288],[-288]],[[0]],[[-4825440]],[[0]],[[-735840]],[[0]],[[-76752]],[[0]],[[-4896]],[[0]],[[-144]]]
theorem step082 : p082=NestedHorner.scale (-1) p078 := by decide +kernel
#print axioms step082
theorem h082 : NestedArithmetic.compile e082=p082 := StagedExprCompile.compile_scaled (-1) e082 e078 p078 p082 rfl h078 step082
#print axioms h082
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
