/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode079
import Proofs.RadenkovicGutmanD35Long00CompositionalNode080
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e081 : NestedArithmetic.Expr 3 := .plus e079 e080
noncomputable def p081 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,-66150,0],[-66150,-11025,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1091475,-959175,0],[-959175,-95550,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-17827425,-5909400,0],[-5909400,-324625,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-129521700,-20475875,0],[-20475875,-561050,0],[0,0]],[[0,0,0],[0,0],[0]],[[-556450125,-44629200,0],[-44629200,-543900],[0]],[[0,0,0],[0,0],[0]],[[-1586533025,-64945825,0],[-64945825,-306250],[0]],[[0,0,0],[0,0],[0]],[[-3194523150,-65312100,0],[-65312100,-99225],[0]],[[0,0,0],[0,0],[0]],[[-4717617100,-46241300,0],[-46241300,-17150],[0]],[[0,0,0],[0,0],[0]],[[-5234350275,-23189250,0],[-23189250,-1225],[0]],[[0,0],[0]],[[-4429764150,-8181775],[-8181775]],[[0,0],[0]],[[-2883368250,-1984500],[-1984500]],[[0,0],[0]],[[-1447175800,-314825],[-314825]],[[0,0],[0]],[[-558241075,-29400],[-29400]],[[0,0],[0]],[[-163852325,-1225],[-1225]],[[0]],[[-35904750]],[[0]],[[-5684000]],[[0]],[[-613725]],[[0]],[[-40425]],[[0]],[[-1225]]]
theorem step081 : p081=NestedHorner.add p079 p080 := by decide +kernel
#print axioms step081
theorem h081 : NestedArithmetic.compile e081=p081 := StagedExprCompile.compile_plus e081 e079 e080 p079 p080 p081 rfl h079 h080 step081
#print axioms h081
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
