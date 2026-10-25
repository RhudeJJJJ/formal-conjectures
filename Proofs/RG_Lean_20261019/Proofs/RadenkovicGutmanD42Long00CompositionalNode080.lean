/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode035
import Proofs.RadenkovicGutmanD42Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e080 : NestedArithmetic.Expr 3 := .times e035 e053
noncomputable def p080 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-5292],[0,-5292]],[[0,0,0],[0,0,0],[0,0]],[[0,-47628,-47628],[-47628,-190512,-22932],[-47628,-22932]],[[0,0,0],[0,0,0],[0,0]],[[-857304,-1905120,-333396],[-1905120,-1333584,-28224],[-333396,-28224]],[[0,0,0],[0,0,0],[0,0]],[[-21146832,-15876000,-920808],[-15876000,-3683232,-12348],[-920808,-12348]],[[0,0,0],[0,0,0],[0,0]],[[-188987904,-62823096,-1335348],[-62823096,-5341392,-1764],[-1335348,-1764]],[[0,0,0],[0,0],[0]],[[-917823312,-146810664,-1121904],[-146810664,-4487616],[-1121904]],[[0,0,0],[0,0],[0]],[[-2838554712,-223195392,-562716],[-223195392,-2250864],[-562716]],[[0,0,0],[0,0],[0]],[[-6066297216,-232018920,-165816],[-232018920,-663264],[-165816]],[[0,0,0],[0,0],[0]],[[-9395868384,-169127028,-26460],[-169127028,-105840],[-26460]],[[0,0,0],[0,0],[0]],[[-10861325496,-87206868,-1764],[-87206868,-7056],[-1764]],[[0,0],[0]],[[-9540477576,-31626756],[-31626756]],[[0,0],[0]],[[-6431568696,-7885080],[-7885080]],[[0,0],[0]],[[-3338899200,-1285956],[-1285956]],[[0,0],[0]],[[-1331100288,-123480],[-123480]],[[0,0],[0]],[[-403550280,-5292],[-5292]],[[0]],[[-91297584]],[[0]],[[-14916384]],[[0]],[[-1661688]],[[0]],[[-112896]],[[0]],[[-3528]]]
theorem step080 : p080=NestedArithmetic.mul p035 p053 := by decide +kernel
#print axioms step080
theorem h080 : NestedArithmetic.compile e080=p080 := StagedExprCompile.compile_times e080 e035 e053 p035 p053 p080 rfl h035 h053 step080
#print axioms h080
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
