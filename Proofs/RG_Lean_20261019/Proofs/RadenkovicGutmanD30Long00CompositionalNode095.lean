/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode093
import Proofs.RadenkovicGutmanD30Long00CompositionalNode094
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e095 : NestedArithmetic.Expr 3 := .plus e093 e094
noncomputable def p095 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,900]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-8100],[0,-16200,26640],[-8100,26640,60]],[[0,0,0],[0,0,0],[0,0]],[[-72900,-270540,96660],[-270540,510840,89520],[96660,89520]],[[0,0,0],[0,0,0],[0,0]],[[-3367980,672300,812880],[672300,3588120,98160],[812880,98160]],[[0,0,0],[0,0,0],[0,0]],[[-18314100,18941580,2305080],[18941580,9567720,41400],[2305080,41400]],[[0,0,0],[0,0,0],[0,0]],[[18416700,93510960,3373080],[93510960,13467120,6240],[3373080,6240]],[[0,0,0],[0,0,0],[0,0]],[[509701140,239909940,2857680],[239909940,11081520,120],[2857680,120]],[[0,0,0],[0,0],[0]],[[2334500220,384808140,1450380],[384808140,5497320],[1450380]],[[0,0,0],[0,0],[0]],[[6068706360,415336200,435720],[415336200,1622280],[435720]],[[0,0,0],[0,0],[0]],[[10626577920,312093900,72180],[312093900,265320],[72180]],[[0,0,0],[0,0],[0]],[[13403103840,165378180,5340],[165378180,19560],[5340]],[[0,0,0],[0,0],[0]],[[12593125440,61609200,60],[61609200,240],[60]],[[0,0],[0]],[[8971107240,15815700],[15815700]],[[0,0],[0]],[[4883222520,2675220],[2675220]],[[0,0],[0]],[[2030993460,271860],[271860]],[[0,0],[0]],[[640536060,13320],[13320]],[[0,0],[0]],[[150637320,120],[120]],[[0]],[[25638960]],[[0]],[[2998140]],[[0]],[[218580]],[[0]],[[7980]],[[0]],[[60]]]
theorem step095 : p095=NestedHorner.add p093 p094 := by decide +kernel
#print axioms step095
theorem h095 : NestedArithmetic.compile e095=p095 := StagedExprCompile.compile_plus e095 e093 e094 p093 p094 p095 rfl h093 h094 step095
#print axioms h095
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
