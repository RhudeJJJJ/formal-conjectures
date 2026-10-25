/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode071
import Proofs.RadenkovicGutmanD28Long00CompositionalNode072
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e073 : NestedArithmetic.Expr 3 := .plus e071 e072
noncomputable def p073 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-42336,0],[-42336,-9072,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-716688,-801360,0],[-801360,-107352,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-14686056,-6447672,0],[-6447672,-516096,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-133368984,-29281952,0],[-29281952,-1307544,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-714305424,-83978888,0],[-83978888,-1909488,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2533129480,-161308224,0],[-161308224,-1669248,0],[0,0]],[[0,0,0],[0,0],[0]],[[-6331462536,-214902632,0],[-214902632,-879648],[0]],[[0,0,0],[0,0],[0]],[[-11591685392,-202778912,0],[-202778912,-272664],[0]],[[0,0,0],[0,0],[0]],[[-15941870448,-136956624,0],[-136956624,-45696],[0]],[[0,0,0],[0,0],[0]],[[-16746208808,-66273200,0],[-66273200,-3192],[0]],[[0,0,0],[0,0],[0]],[[-13576651760,-22746920,0],[-22746920,0],[0]],[[0,0],[0]],[[-8539606992,-5398848],[-5398848]],[[0,0],[0]],[[-4168871504,-841736],[-841736]],[[0,0],[0]],[[-1571986136,-77504],[-77504]],[[0,0],[0]],[[-452789736,-3192],[-3192]],[[0,0],[0]],[[-97665680,0],[0]],[[0]],[[-15256304]],[[0]],[[-1628648]],[[0]],[[-106232]],[[0]],[[-3192]],[[0]],[[0]]]
theorem step073 : p073=NestedHorner.add p071 p072 := by decide +kernel
#print axioms step073
theorem h073 : NestedArithmetic.compile e073=p073 := StagedExprCompile.compile_plus e073 e071 e072 p071 p072 p073 rfl h071 h072 step073
#print axioms h073
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
