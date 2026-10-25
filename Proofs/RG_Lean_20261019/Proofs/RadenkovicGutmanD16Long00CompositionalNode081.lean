/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode079
import Proofs.RadenkovicGutmanD16Long00CompositionalNode080
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e081 : NestedArithmetic.Expr 3 := .plus e079 e080
noncomputable def p081 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,-13824,0],[-13824,-2304,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-228096,-200448,0],[-200448,-19968,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3725568,-1234944,0],[-1234944,-67840,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-27067392,-4279040,0],[-4279040,-117248,0],[0,0]],[[0,0,0],[0,0],[0]],[[-116286720,-9326592,0],[-9326592,-113664],[0]],[[0,0,0],[0,0],[0]],[[-331553024,-13572352,0],[-13572352,-64000],[0]],[[0,0,0],[0,0],[0]],[[-667590144,-13648896,0],[-13648896,-20736],[0]],[[0,0,0],[0,0],[0]],[[-985885696,-9663488,0],[-9663488,-3584],[0]],[[0,0,0],[0,0],[0]],[[-1093872384,-4846080,0],[-4846080,-256],[0]],[[0,0],[0]],[[-925730304,-1709824],[-1709824]],[[0,0],[0]],[[-602565120,-414720],[-414720]],[[0,0],[0]],[[-302430208,-65792],[-65792]],[[0,0],[0]],[[-116660992,-6144],[-6144]],[[0,0],[0]],[[-34241792,-256],[-256]],[[0]],[[-7503360]],[[0]],[[-1187840]],[[0]],[[-128256]],[[0]],[[-8448]],[[0]],[[-256]]]
theorem step081 : p081=NestedHorner.add p079 p080 := by decide +kernel
#print axioms step081
theorem h081 : NestedArithmetic.compile e081=p081 := StagedExprCompile.compile_plus e081 e079 e080 p079 p080 p081 rfl h079 h080 step081
#print axioms h081
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
