/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode089
import Proofs.RadenkovicGutmanD34Long00CompositionalNode091
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e092 : NestedArithmetic.Expr 3 := .plus e089 e091
noncomputable def p092 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,6936],[0,6936,-2176]],[[0,0,0],[0,0,0],[0,0]],[[0,0,83232],[0,280908,-8908],[83232,-8908]],[[0,0,0],[0,0,0],[0,0]],[[269892,2280312,442884],[2280312,1320696,-66572],[442884,-66572]],[[0,0,0],[0,0,0],[0,0]],[[19599300,19810440,892364],[19810440,2037756,-78472],[892364,-78472]],[[0,0,0],[0,0,0],[0,0]],[[212410512,74932668,729504],[74932668,270776,-32028],[729504,-32028]],[[0,0,0],[0,0,0],[0,0]],[[1108794876,161077176,-62764],[161077176,-2817376,-4284],[-62764,-4284]],[[0,0,0],[0,0],[0]],[[3529791260,214645468,-569160],[214645468,-3721640],[-569160]],[[0,0,0],[0,0],[0]],[[7572944576,178945672,-444108],[178945672,-2244612],[-444108]],[[0,0,0],[0,0],[0]],[[11525391536,84527264,-161568],[84527264,-727192],[-161568]],[[0,0,0],[0,0],[0]],[[12777008852,9154636,-29172],[9154636,-122468],[-29172]],[[0,0,0],[0,0],[0]],[[10415252640,-15405400,-2108],[-15405400,-8432],[-2108]],[[0,0],[0]],[[6192443664,-11213676],[-11213676]],[[0,0],[0]],[[2586444328,-3907484],[-3907484]],[[0,0],[0]],[[669927908,-784244],[-784244]],[[0,0],[0]],[[44008444,-86972],[-86972]],[[0,0],[0]],[[-43775408,-4148],[-4148]],[[0]],[[-20959504]],[[0]],[[-4987188]],[[0]],[[-707676]],[[0]],[[-57188]],[[0]],[[-2040]]]
theorem step092 : p092=NestedHorner.add p089 p091 := by decide +kernel
#print axioms step092
theorem h092 : NestedArithmetic.compile e092=p092 := StagedExprCompile.compile_plus e092 e089 e091 p089 p091 p092 rfl h089 h091 step092
#print axioms h092
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
