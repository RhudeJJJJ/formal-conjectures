/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode073
import Proofs.RadenkovicGutmanD14Long00CompositionalNode084
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e085 : NestedArithmetic.Expr 3 := .plus e073 e084
noncomputable def p085 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,-1008,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-9072,-51408,0],[-51408,-16044,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-939708,-718956,0],[-718956,-93016,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-13827996,-4306680,0],[-4306680,-266476,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-96194784,-14603540,0],[-14603540,-421624,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-402746092,-31308760,0],[-31308760,-388528,0],[0,0]],[[0,0,0],[0,0],[0]],[[-1128102724,-44986116,0],[-44986116,-212072],[0]],[[0,0,0],[0,0],[0]],[[-2241710408,-44792496,0],[-44792496,-67340],[0]],[[0,0,0],[0,0],[0]],[[-3276668192,-31463320,0],[-31463320,-11480],[0]],[[0,0,0],[0,0],[0]],[[-3605595700,-15677312,0],[-15677312,-812],[0]],[[0,0,0],[0,0],[0]],[[-3030598984,-5502084,0],[-5502084,0],[0]],[[0,0],[0]],[[-1961351560,-1328600],[-1328600]],[[0,0],[0]],[[-979606096,-209972],[-209972]],[[0,0],[0]],[[-376286036,-19544],[-19544]],[[0,0],[0]],[[-110039860,-812],[-812]],[[0,0],[0]],[[-24034920,0],[0]],[[0]],[[-3794000]],[[0]],[[-408604]],[[0]],[[-26852]],[[0]],[[-812]],[[0]],[[0]]]
theorem step085 : p085=NestedHorner.add p073 p084 := by decide +kernel
#print axioms step085
theorem h085 : NestedArithmetic.compile e085=p085 := StagedExprCompile.compile_plus e085 e073 e084 p073 p084 p085 rfl h073 h084 step085
#print axioms h085
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
