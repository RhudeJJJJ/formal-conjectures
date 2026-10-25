/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode092
import Proofs.RadenkovicGutmanD19Long00CompositionalNode103
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e104 : NestedArithmetic.Expr 3 := .plus e092 e103
noncomputable def p104 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-1368,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-12312,-12312,0],[-12312,-11514,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-321138,-136458,0],[-136458,-37316,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3120066,-642276,0],[-642276,-59546,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-16450656,-1695750,0],[-1695750,-50084,0],[0,0]],[[0,0,0],[0,0],[0]],[[-54641834,-2794292,0],[-2794292,-21128],[0]],[[0,0,0],[0,0],[0]],[[-123502014,-3012222,0],[-3012222,-2812],[0]],[[0,0,0],[0,0],[0]],[[-198529404,-2147912,0],[-2147912,950],[0]],[[0,0,0],[0,0],[0]],[[-232774624,-983972,0],[-983972,380],[0]],[[0,0,0],[0,0],[0]],[[-201377846,-254752,0],[-254752,38],[0]],[[0,0],[0]],[[-128319388,-13262],[-13262]],[[0,0],[0]],[[-58995836,14060],[14060]],[[0,0],[0]],[[-18385160,4826],[4826]],[[0,0],[0]],[[-3082902,684],[684]],[[0,0],[0]],[[198778,38],[38]],[[0]],[[272916]],[[0]],[[77976]],[[0]],[[12046]],[[0]],[[1026]],[[0]],[[38]]]
theorem step104 : p104=NestedHorner.add p092 p103 := by decide +kernel
#print axioms step104
theorem h104 : NestedArithmetic.compile e104=p104 := StagedExprCompile.compile_plus e104 e092 e103 p092 p103 p104 rfl h092 h103 step104
#print axioms h104
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
