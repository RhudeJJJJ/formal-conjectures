/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode035
import Proofs.RadenkovicGutmanD44Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e080 : NestedArithmetic.Expr 3 := .times e035 e053
noncomputable def p080 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-5808],[0,-5808]],[[0,0,0],[0,0,0],[0,0]],[[0,-52272,-52272],[-52272,-209088,-25168],[-52272,-25168]],[[0,0,0],[0,0,0],[0,0]],[[-940896,-2090880,-365904],[-2090880,-1463616,-30976],[-365904,-30976]],[[0,0,0],[0,0,0],[0,0]],[[-23208768,-17424000,-1010592],[-17424000,-4042368,-13552],[-1010592,-13552]],[[0,0,0],[0,0,0],[0,0]],[[-207415296,-68948704,-1465552],[-68948704,-5862208,-1936],[-1465552,-1936]],[[0,0,0],[0,0],[0]],[[-1007316288,-161125536,-1231296],[-161125536,-4925184],[-1231296]],[[0,0,0],[0,0],[0]],[[-3115329888,-244958208,-617584],[-244958208,-2470336],[-617584]],[[0,0,0],[0,0],[0]],[[-6657795584,-254642080,-181984],[-254642080,-727936],[-181984]],[[0,0,0],[0,0],[0]],[[-10312018816,-185617872,-29040],[-185617872,-116160],[-29040]],[[0,0,0],[0,0],[0]],[[-11920366304,-95710032,-1936],[-95710032,-7744],[-1936]],[[0,0],[0]],[[-10470728224,-34710544],[-34710544]],[[0,0],[0]],[[-7058683104,-8653920],[-8653920]],[[0,0],[0]],[[-3664460800,-1411344],[-1411344]],[[0,0],[0]],[[-1460890112,-135520],[-135520]],[[0,0],[0]],[[-442898720,-5808],[-5808]],[[0]],[[-100199616]],[[0]],[[-16370816]],[[0]],[[-1823712]],[[0]],[[-123904]],[[0]],[[-3872]]]
theorem step080 : p080=NestedArithmetic.mul p035 p053 := by decide +kernel
#print axioms step080
theorem h080 : NestedArithmetic.compile e080=p080 := StagedExprCompile.compile_times e080 e035 e053 p035 p053 p080 rfl h035 h053 step080
#print axioms h080
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
