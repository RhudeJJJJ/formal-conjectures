/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode073
import Proofs.RadenkovicGutmanD31Long00CompositionalNode084
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e085 : NestedArithmetic.Expr 3 := .plus e073 e084
noncomputable def p085 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,-2232,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-20088,-227664,0],[-227664,-54498,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3959010,-3242538,0],[-3242538,-370388,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-61296858,-19705212,0],[-19705212,-1148674,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-435885792,-67571630,0],[-67571630,-1899060,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1849343378,-146125196,0],[-146125196,-1796264,0],[0,0]],[[0,0,0],[0,0],[0]],[[-5228073678,-211371950,0],[-211371950,-996588],[0]],[[0,0,0],[0,0],[0]],[[-10460974924,-211573512,0],[-211573512,-319858],[0]],[[0,0,0],[0,0],[0]],[[-15373632096,-149241564,0],[-149241564,-54932],[0]],[[0,0,0],[0,0],[0]],[[-16991174462,-74618488,0],[-74618488,-3906],[0]],[[0,0,0],[0,0],[0]],[[-14333422508,-26262518,0],[-26262518,0],[0]],[[0,0],[0]],[[-9304739900,-6356860],[-6356860]],[[0,0],[0]],[[-4659451528,-1006694],[-1006694]],[[0,0],[0]],[[-1793835150,-93868],[-93868]],[[0,0],[0]],[[-525619446,-3906],[-3906]],[[0,0],[0]],[[-115005660,0],[0]],[[0]],[[-18182120]],[[0]],[[-1960874]],[[0]],[[-129022]],[[0]],[[-3906]],[[0]],[[0]]]
theorem step085 : p085=NestedHorner.add p073 p084 := by decide +kernel
#print axioms step085
theorem h085 : NestedArithmetic.compile e085=p085 := StagedExprCompile.compile_plus e085 e073 e084 p073 p084 p085 rfl h073 h084 step085
#print axioms h085
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
