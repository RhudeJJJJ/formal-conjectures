/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode050
import Proofs.RadenkovicGutmanD4Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e071 : NestedArithmetic.Expr 3 := .times e050 e060
noncomputable def p071 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,48],[0,48,-16]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-432,720],[-432,2160,-152],[720,-152,-8]],[[0,0,0],[0,0,0],[0,0]],[[-5184,13608,3576],[13608,7848,-968],[3576,-968]],[[0,0,0],[0,0,0],[0,0]],[[46224,121896,4736],[121896,-4128,-1360],[4736,-1360]],[[0,0,0],[0,0,0],[0,0]],[[826200,373808,-4768],[373808,-62072,-760],[-4768,-760]],[[0,0,0],[0,0,0],[0,0]],[[4166520,399400,-20760],[399400,-129552,-184],[-20760,-184]],[[0,0,0],[0,0,0],[0,0]],[[9989384,-507920,-25936],[-507920,-134400,-16],[-25936,-16]],[[0,0,0],[0,0],[0]],[[8926736,-2264808,-17048],[-2264808,-80672],[-17048]],[[0,0,0],[0,0],[0]],[[-15895792,-3556848,-6496],[-3556848,-29048],[-6496]],[[0,0,0],[0,0],[0]],[[-67577952,-3349976,-1432],[-3349976,-6144],[-1432]],[[0,0,0],[0,0],[0]],[[-119671960,-2101464,-168],[-2101464,-696],[-168]],[[0,0,0],[0,0],[0]],[[-137176224,-907232,-8],[-907232,-32],[-8]],[[0,0],[0]],[[-112363072,-270128],[-270128]],[[0,0],[0]],[[-68307696,-54272],[-54272]],[[0,0],[0]],[[-31288744,-6976],[-6976]],[[0,0],[0]],[[-10823472,-512],[-512]],[[0,0],[0]],[[-2804688,-16],[-16]],[[0]],[[-533920]],[[0]],[[-72072]],[[0]],[[-6480]],[[0]],[[-344]],[[0]],[[-8]]]
theorem step071 : p071=NestedArithmetic.mul p050 p060 := by decide +kernel
#print axioms step071
theorem h071 : NestedArithmetic.compile e071=p071 := StagedExprCompile.compile_times e071 e050 e060 p050 p060 p071 rfl h050 h060 step071
#print axioms h071
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
