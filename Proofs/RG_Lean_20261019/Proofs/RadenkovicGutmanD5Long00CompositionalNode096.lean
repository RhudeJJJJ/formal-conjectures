/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode043
import Proofs.RadenkovicGutmanD5Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e096 : NestedArithmetic.Expr 3 := .times e043 e053
noncomputable def p096 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,75],[0,75,-30]],[[0,0,0],[0,0,0],[0,0]],[[0,675,675],[675,3060,-215],[675,-215]],[[0,0,0],[0,0,0],[0,0]],[[17820,30240,2295],[30240,12300,-1040],[2295,-1040]],[[0,0,0],[0,0,0],[0,0]],[[427140,217980,90],[217980,10960,-1145],[90,-1145]],[[0,0,0],[0,0,0],[0,0]],[[3649590,718630,-10235],[718630,-22620,-455],[-10235,-455]],[[0,0,0],[0,0,0],[0,0]],[[16935420,1317570,-20100],[1317570,-62640,-60],[-20100,-60]],[[0,0,0],[0,0],[0]],[[49910620,1364440,-18605],[1364440,-64420],[-18605]],[[0,0,0],[0,0],[0]],[[100821600,593750,-9650],[593750,-35360],[-9650]],[[0,0,0],[0,0],[0]],[[145313540,-354355,-2865],[-354355,-10900],[-2865]],[[0,0,0],[0,0],[0]],[[152191310,-739035,-455],[-739035,-1780],[-455]],[[0,0,0],[0,0],[0]],[[115726490,-558375,-30],[-558375,-120],[-30]],[[0,0],[0]],[[62070150,-250350],[-250350]],[[0,0],[0]],[[21161600,-71575],[-71575]],[[0,0],[0]],[[2438440,-12850],[-12850]],[[0,0],[0]],[[-1798280,-1325],[-1325]],[[0,0],[0]],[[-1239780,-60],[-60]],[[0]],[[-412300]],[[0]],[[-85650]],[[0]],[[-11290]],[[0]],[[-870]],[[0]],[[-30]]]
theorem step096 : p096=NestedArithmetic.mul p043 p053 := by decide +kernel
#print axioms step096
theorem h096 : NestedArithmetic.compile e096=p096 := StagedExprCompile.compile_times e096 e043 e053 p043 p053 p096 rfl h043 h053 step096
#print axioms h096
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
