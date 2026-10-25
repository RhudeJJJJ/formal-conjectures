/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode035
import Proofs.RadenkovicGutmanD22Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e080 : NestedArithmetic.Expr 3 := .times e035 e053
noncomputable def p080 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-1452],[0,-1452]],[[0,0,0],[0,0,0],[0,0]],[[0,-13068,-13068],[-13068,-52272,-6292],[-13068,-6292]],[[0,0,0],[0,0,0],[0,0]],[[-235224,-522720,-91476],[-522720,-365904,-7744],[-91476,-7744]],[[0,0,0],[0,0,0],[0,0]],[[-5802192,-4356000,-252648],[-4356000,-1010592,-3388],[-252648,-3388]],[[0,0,0],[0,0,0],[0,0]],[[-51853824,-17237176,-366388],[-17237176,-1465552,-484],[-366388,-484]],[[0,0,0],[0,0],[0]],[[-251829072,-40281384,-307824],[-40281384,-1231296],[-307824]],[[0,0,0],[0,0],[0]],[[-778832472,-61239552,-154396],[-61239552,-617584],[-154396]],[[0,0,0],[0,0],[0]],[[-1664448896,-63660520,-45496],[-63660520,-181984],[-45496]],[[0,0,0],[0,0],[0]],[[-2578004704,-46404468,-7260],[-46404468,-29040],[-7260]],[[0,0,0],[0,0],[0]],[[-2980091576,-23927508,-484],[-23927508,-1936],[-484]],[[0,0],[0]],[[-2617682056,-8677636],[-8677636]],[[0,0],[0]],[[-1764670776,-2163480],[-2163480]],[[0,0],[0]],[[-916115200,-352836],[-352836]],[[0,0],[0]],[[-365222528,-33880],[-33880]],[[0,0],[0]],[[-110724680,-1452],[-1452]],[[0]],[[-25049904]],[[0]],[[-4092704]],[[0]],[[-455928]],[[0]],[[-30976]],[[0]],[[-968]]]
theorem step080 : p080=NestedArithmetic.mul p035 p053 := by decide +kernel
#print axioms step080
theorem h080 : NestedArithmetic.compile e080=p080 := StagedExprCompile.compile_times e080 e035 e053 p035 p053 p080 rfl h035 h053 step080
#print axioms h080
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
