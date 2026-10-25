/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode035
import Proofs.RadenkovicGutmanD23Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e080 : NestedArithmetic.Expr 3 := .times e035 e053
noncomputable def p080 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-1587],[0,-1587]],[[0,0,0],[0,0,0],[0,0]],[[0,-14283,-14283],[-14283,-57132,-6877],[-14283,-6877]],[[0,0,0],[0,0,0],[0,0]],[[-257094,-571320,-99981],[-571320,-399924,-8464],[-99981,-8464]],[[0,0,0],[0,0,0],[0,0]],[[-6341652,-4761000,-276138],[-4761000,-1104552,-3703],[-276138,-3703]],[[0,0,0],[0,0,0],[0,0]],[[-56674944,-18839806,-400453],[-18839806,-1601812,-529],[-400453,-529]],[[0,0,0],[0,0],[0]],[[-275242932,-44026554,-336444],[-44026554,-1345776],[-336444]],[[0,0,0],[0,0],[0]],[[-851244582,-66933312,-168751],[-66933312,-675004],[-168751]],[[0,0,0],[0,0],[0]],[[-1819201376,-69579370,-49726],[-69579370,-198904],[-49726]],[[0,0,0],[0,0],[0]],[[-2817695224,-50718933,-7935],[-50718933,-31740],[-7935]],[[0,0,0],[0,0],[0]],[[-3257166206,-26152173,-529],[-26152173,-2116],[-529]],[[0,0],[0]],[[-2861061586,-9484441],[-9484441]],[[0,0],[0]],[[-1928741406,-2364630],[-2364630]],[[0,0],[0]],[[-1001291200,-385641],[-385641]],[[0,0],[0]],[[-399179168,-37030],[-37030]],[[0,0],[0]],[[-121019330,-1587],[-1587]],[[0]],[[-27378924]],[[0]],[[-4473224]],[[0]],[[-498318]],[[0]],[[-33856]],[[0]],[[-1058]]]
theorem step080 : p080=NestedArithmetic.mul p035 p053 := by decide +kernel
#print axioms step080
theorem h080 : NestedArithmetic.compile e080=p080 := StagedExprCompile.compile_times e080 e035 e053 p035 p053 p080 rfl h035 h053 step080
#print axioms h080
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
