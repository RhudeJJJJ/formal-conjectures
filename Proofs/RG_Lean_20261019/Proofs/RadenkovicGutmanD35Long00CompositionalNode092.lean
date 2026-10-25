/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode089
import Proofs.RadenkovicGutmanD35Long00CompositionalNode091
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e092 : NestedArithmetic.Expr 3 := .plus e089 e091
noncomputable def p092 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,7350],[0,7350,-2310]],[[0,0,0],[0,0,0],[0,0]],[[0,0,88200],[0,297675,-9520],[88200,-9520]],[[0,0,0],[0,0,0],[0,0]],[[286335,2416365,468930],[2416365,1397970,-70770],[468930,-70770]],[[0,0,0],[0,0,0],[0,0]],[[20773935,20984670,943460],[20984670,2150715,-83370],[943460,-83370]],[[0,0,0],[0,0,0],[0,0]],[[225081990,79338735,767970],[79338735,266630,-34020],[767970,-34020]],[[0,0,0],[0,0,0],[0,0]],[[1174672695,170446220,-73010],[170446220,-3011540,-4550],[-73010,-4550]],[[0,0,0],[0,0],[0]],[[3738607705,226921345,-608090],[226921345,-3963610],[-608090]],[[0,0,0],[0,0],[0]],[[8018694670,188858110,-472920],[188858110,-2387805],[-472920]],[[0,0,0],[0,0],[0]],[[12199494440,88812010,-171850],[88812010,-773150],[-171850]],[[0,0,0],[0,0],[0]],[[13517932925,9169020,-31010],[9169020,-130165],[-31010]],[[0,0,0],[0,0],[0]],[[11011671510,-16589965,-2240],[-16589965,-8960],[-2240]],[[0,0],[0]],[[6539825110,-11976370],[-11976370]],[[0,0],[0]],[[2725820160,-4163425],[-4163425]],[[0,0],[0]],[[702122225,-834680],[-834680]],[[0,0],[0]],[[43528205,-92505],[-92505]],[[0,0],[0]],[[-47330290,-4410],[-4410]],[[0]],[[-22423660]],[[0]],[[-5319685]],[[0]],[[-753795]],[[0]],[[-60865]],[[0]],[[-2170]]]
theorem step092 : p092=NestedHorner.add p089 p091 := by decide +kernel
#print axioms step092
theorem h092 : NestedArithmetic.compile e092=p092 := StagedExprCompile.compile_plus e092 e089 e091 p089 p091 p092 rfl h089 h091 step092
#print axioms h092
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
