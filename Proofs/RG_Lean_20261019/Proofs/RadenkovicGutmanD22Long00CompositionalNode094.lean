/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode035
import Proofs.RadenkovicGutmanD22Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e094 : NestedArithmetic.Expr 3 := .times e035 e061
noncomputable def p094 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-4356],[0,-8712,2640],[-4356,2640]],[[0,0,0],[0,0,0],[0,0]],[[0,-119988,-13992],[-119988,19536,11440],[-13992,11440]],[[0,0,0],[0,0,0],[0,0]],[[-748440,-656964,38060],[-656964,408760,14080],[38060,14080]],[[0,0,0],[0,0,0],[0,0]],[[-5524200,240372,237688],[240372,1394096,6160],[237688,6160]],[[0,0,0],[0,0,0],[0,0]],[[-3704184,10552520,451264],[10552520,2234848,880],[451264,880]],[[0,0,0],[0,0],[0]],[[103188096,37556948,438680],[37556948,1996720],[438680]],[[0,0,0],[0,0],[0]],[[560058576,70235132,241516],[70235132,1044472],[241516]],[[0,0,0],[0,0],[0]],[[1561630576,83010576,75944],[83010576,317328],[75944]],[[0,0,0],[0,0],[0]],[[2844980776,66144804,12716],[66144804,51832],[12716]],[[0,0,0],[0,0],[0]],[[3676936648,36433804,880],[36433804,3520],[880]],[[0,0],[0]],[[3506961568,13906376],[13906376]],[[0,0],[0]],[[2519577368,3611740],[3611740]],[[0,0],[0]],[[1376320088,609092],[609092]],[[0,0],[0]],[[572067408,60148],[60148]],[[0,0],[0]],[[179589872,2640],[2640]],[[0]],[[41851392]],[[0]],[[7014392]],[[0]],[[798952]],[[0]],[[55352]],[[0]],[[1760]]]
theorem step094 : p094=NestedArithmetic.mul p035 p061 := by decide +kernel
#print axioms step094
theorem h094 : NestedArithmetic.compile e094=p094 := StagedExprCompile.compile_times e094 e035 e061 p035 p061 p094 rfl h035 h061 step094
#print axioms h094
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
