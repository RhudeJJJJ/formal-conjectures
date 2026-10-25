/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode043
import Proofs.RadenkovicGutmanD16Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e100 : NestedArithmetic.Expr 3 := .times e043 e057
noncomputable def p100 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-2304],[0,-4608,1344],[-2304,1344]],[[0,0,0],[0,0,0],[0,0]],[[0,-91584,-7872],[-91584,4416,5824],[-7872,5824]],[[0,0,0],[0,0,0],[0,0]],[[-855360,-762048,16832],[-762048,168064,7168],[16832,7168]],[[0,0,0],[0,0,0],[0,0]],[[-10445760,-2441088,116608],[-2441088,582208,3136],[116608,3136]],[[0,0,0],[0,0,0],[0,0]],[[-56616192,-3313088,225472],[-3313088,924032,448],[225472,448]],[[0,0,0],[0,0],[0]],[[-179812800,544256,220928],[544256,812800],[220928]],[[0,0,0],[0,0],[0]],[[-370140864,9168832,122176],[9168832,418176],[122176]],[[0,0,0],[0,0],[0]],[[-511012480,15924352,38528],[15924352,124992],[38528]],[[0,0,0],[0,0],[0]],[[-461816064,15292480,6464],[15292480,20096],[6464]],[[0,0,0],[0,0],[0]],[[-227844032,9456832,448],[9456832,1344],[448]],[[0,0],[0]],[[24486656,3915392],[3915392]],[[0,0],[0]],[[146785280,1081600],[1081600]],[[0,0],[0]],[[135634432,191616],[191616]],[[0,0],[0]],[[75219648,19712],[19712]],[[0,0],[0]],[[28593984,896],[896]],[[0]],[[7662720]],[[0]],[[1431040]],[[0]],[[177856]],[[0]],[[13248]],[[0]],[[448]]]
theorem step100 : p100=NestedArithmetic.mul p043 p057 := by decide +kernel
#print axioms step100
theorem h100 : NestedArithmetic.compile e100=p100 := StagedExprCompile.compile_times e100 e043 e057 p043 p057 p100 rfl h043 h057 step100
#print axioms h100
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
