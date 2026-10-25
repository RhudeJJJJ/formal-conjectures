/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode073
import Proofs.RadenkovicGutmanD29Long00CompositionalNode084
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e085 : NestedArithmetic.Expr 3 := .plus e073 e084
noncomputable def p085 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,-2088,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-18792,-200448,0],[-200448,-48894,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3496878,-2851686,0],[-2851686,-328396,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-53965926,-17314740,0],[-17314740,-1013086,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-383234304,-59334290,0],[-59334290,-1670284,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1624646062,-128245540,0],[-128245540,-1577368,0],[0,0]],[[0,0,0],[0,0],[0]],[[-4590308674,-185435106,0],[-185435106,-874292],[0]],[[0,0,0],[0,0],[0]],[[-9181069748,-185554296,0],[-185554296,-280430],[0]],[[0,0,0],[0,0],[0]],[[-13488325952,-130855540,0],[-130855540,-48140],[0]],[[0,0,0],[0,0],[0]],[[-14903647810,-65412632,0],[-65412632,-3422],[0]],[[0,0,0],[0,0],[0]],[[-12569742484,-23018634,0],[-23018634,0],[0]],[[0,0],[0]],[[-8158359460,-5570900],[-5570900]],[[0,0],[0]],[[-4084764376,-882122],[-882122]],[[0,0],[0]],[[-1572379826,-82244],[-82244]],[[0,0],[0]],[[-460676890,-3422],[-3422]],[[0,0],[0]],[[-100786020,0],[0]],[[0]],[[-15932600]],[[0]],[[-1718134]],[[0]],[[-113042]],[[0]],[[-3422]],[[0]],[[0]]]
theorem step085 : p085=NestedHorner.add p073 p084 := by decide +kernel
#print axioms step085
theorem h085 : NestedArithmetic.compile e085=p085 := StagedExprCompile.compile_plus e085 e073 e084 p073 p084 p085 rfl h073 h084 step085
#print axioms h085
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
