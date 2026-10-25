/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode035
import Proofs.RadenkovicGutmanD33Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e080 : NestedArithmetic.Expr 3 := .times e035 e053
noncomputable def p080 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-3267],[0,-3267]],[[0,0,0],[0,0,0],[0,0]],[[0,-29403,-29403],[-29403,-117612,-14157],[-29403,-14157]],[[0,0,0],[0,0,0],[0,0]],[[-529254,-1176120,-205821],[-1176120,-823284,-17424],[-205821,-17424]],[[0,0,0],[0,0,0],[0,0]],[[-13054932,-9801000,-568458],[-9801000,-2273832,-7623],[-568458,-7623]],[[0,0,0],[0,0,0],[0,0]],[[-116671104,-38783646,-824373],[-38783646,-3297492,-1089],[-824373,-1089]],[[0,0,0],[0,0],[0]],[[-566615412,-90633114,-692604],[-90633114,-2770416],[-692604]],[[0,0,0],[0,0],[0]],[[-1752373062,-137788992,-347391],[-137788992,-1389564],[-347391]],[[0,0,0],[0,0],[0]],[[-3745010016,-143236170,-102366],[-143236170,-409464],[-102366]],[[0,0,0],[0,0],[0]],[[-5800510584,-104410053,-16335],[-104410053,-65340],[-16335]],[[0,0,0],[0,0],[0]],[[-6705206046,-53836893,-1089],[-53836893,-4356],[-1089]],[[0,0],[0]],[[-5889784626,-19524681],[-19524681]],[[0,0],[0]],[[-3970509246,-4867830],[-4867830]],[[0,0],[0]],[[-2061259200,-793881],[-793881]],[[0,0],[0]],[[-821750688,-76230],[-76230]],[[0,0],[0]],[[-249130530,-3267],[-3267]],[[0]],[[-56362284]],[[0]],[[-9208584]],[[0]],[[-1025838]],[[0]],[[-69696]],[[0]],[[-2178]]]
theorem step080 : p080=NestedArithmetic.mul p035 p053 := by decide +kernel
#print axioms step080
theorem h080 : NestedArithmetic.compile e080=p080 := StagedExprCompile.compile_times e080 e035 e053 p035 p053 p080 rfl h035 h053 step080
#print axioms h080
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
