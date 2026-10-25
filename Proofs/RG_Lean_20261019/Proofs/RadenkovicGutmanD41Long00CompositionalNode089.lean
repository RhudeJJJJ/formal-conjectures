/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode033
import Proofs.RadenkovicGutmanD41Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e089 : NestedArithmetic.Expr 3 := .times e033 e061
noncomputable def p089 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,5043],[0,5043,-3198]],[[0,0,0],[0,0,0],[0,0]],[[0,-45387,45387],[-45387,166419,-35711],[45387,-35711]],[[0,0,0],[0,0,0],[0,0]],[[-421767,499257,58671],[499257,103566,-126608],[58671,-126608]],[[0,0,0],[0,0,0],[0,0]],[[178227,2357172,-504054],[2357172,-2461681,-128945],[-504054,-128945]],[[0,0,0],[0,0,0],[0,0]],[[16089138,-5532253,-1835939],[-5532253,-8113654,-49487],[-1835939,-49487]],[[0,0,0],[0,0,0],[0,0]],[[45812703,-55002894,-2768484],[-55002894,-11820300,-6396],[-2768484,-6396]],[[0,0,0],[0,0],[0]],[[-93882005,-159642889,-2297189],[-159642889,-9609006],[-2297189]],[[0,0,0],[0,0],[0]],[[-898020622,-263123486,-1121186],[-263123486,-4620905],[-1121186]],[[0,0,0],[0,0],[0]],[[-2763311112,-282668063,-320169],[-282668063,-1304210],[-320169]],[[0,0,0],[0,0],[0]],[[-5182550101,-208625589,-49487],[-208625589,-199629],[-49487]],[[0,0,0],[0,0],[0]],[[-6754513676,-107883054,-3198],[-107883054,-12792],[-3198]],[[0,0],[0]],[[-6449967972,-39053730],[-39053730]],[[0,0],[0]],[[-4628126904,-9696008],[-9696008]],[[0,0],[0]],[[-2523266075,-1572842],[-1572842]],[[0,0],[0]],[[-1046795805,-150142],[-150142]],[[0,0],[0]],[[-328068306,-6396],[-6396]],[[0]],[[-76343148]],[[0]],[[-12779823]],[[0]],[[-1454147]],[[0]],[[-100655]],[[0]],[[-3198]]]
theorem step089 : p089=NestedArithmetic.mul p033 p061 := by decide +kernel
#print axioms step089
theorem h089 : NestedArithmetic.compile e089=p089 := StagedExprCompile.compile_times e089 e033 e061 p033 p061 p089 rfl h033 h061 step089
#print axioms h089
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
