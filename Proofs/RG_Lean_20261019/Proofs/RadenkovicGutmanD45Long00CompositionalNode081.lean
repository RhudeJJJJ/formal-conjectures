/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode079
import Proofs.RadenkovicGutmanD45Long00CompositionalNode080
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e081 : NestedArithmetic.Expr 3 := .plus e079 e080
noncomputable def p081 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,-109350,0],[-109350,-18225,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1804275,-1585575,0],[-1585575,-157950,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-29469825,-9768600,0],[-9768600,-536625,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-214107300,-33847875,0],[-33847875,-927450,0],[0,0]],[[0,0,0],[0,0],[0]],[[-919846125,-73774800,0],[-73774800,-899100],[0]],[[0,0,0],[0,0],[0]],[[-2622636225,-107359425,0],[-107359425,-506250],[0]],[[0,0,0],[0,0],[0]],[[-5280742350,-107964900,0],[-107964900,-164025],[0]],[[0,0,0],[0,0],[0]],[[-7798509900,-76439700,0],[-76439700,-28350],[0]],[[0,0,0],[0,0],[0]],[[-8652701475,-38333250,0],[-38333250,-2025],[0]],[[0,0],[0]],[[-7322671350,-13524975],[-13524975]],[[0,0],[0]],[[-4766384250,-3280500],[-3280500]],[[0,0],[0]],[[-2392270200,-520425],[-520425]],[[0,0],[0]],[[-922806675,-48600],[-48600]],[[0,0],[0]],[[-270857925,-2025],[-2025]],[[0]],[[-59352750]],[[0]],[[-9396000]],[[0]],[[-1014525]],[[0]],[[-66825]],[[0]],[[-2025]]]
theorem step081 : p081=NestedHorner.add p079 p080 := by decide +kernel
#print axioms step081
theorem h081 : NestedArithmetic.compile e081=p081 := StagedExprCompile.compile_plus e081 e079 e080 p079 p080 p081 rfl h079 h080 step081
#print axioms h081
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
