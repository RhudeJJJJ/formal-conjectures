/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode092
import Proofs.RadenkovicGutmanD20Long00CompositionalNode103
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e104 : NestedArithmetic.Expr 3 := .plus e092 e103
noncomputable def p104 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-1440,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-12960,-12960,0],[-12960,-12120,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-338040,-143640,0],[-143640,-39280,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3284280,-676080,0],[-676080,-62680,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-17316480,-1785000,0],[-1785000,-52720,0],[0,0]],[[0,0,0],[0,0],[0]],[[-57517720,-2941360,0],[-2941360,-22240],[0]],[[0,0,0],[0,0],[0]],[[-130002120,-3170760,0],[-3170760,-2960],[0]],[[0,0,0],[0,0],[0]],[[-208978320,-2260960,0],[-2260960,1000],[0]],[[0,0,0],[0,0],[0]],[[-245025920,-1035760,0],[-1035760,400],[0]],[[0,0,0],[0,0],[0]],[[-211976680,-268160,0],[-268160,40],[0]],[[0,0],[0]],[[-135073040,-13960],[-13960]],[[0,0],[0]],[[-62100880,14800],[14800]],[[0,0],[0]],[[-19352800,5080],[5080]],[[0,0],[0]],[[-3245160,720],[720]],[[0,0],[0]],[[209240,40],[40]],[[0]],[[287280]],[[0]],[[82080]],[[0]],[[12680]],[[0]],[[1080]],[[0]],[[40]]]
theorem step104 : p104=NestedHorner.add p092 p103 := by decide +kernel
#print axioms step104
theorem h104 : NestedArithmetic.compile e104=p104 := StagedExprCompile.compile_plus e104 e092 e103 p092 p103 p104 rfl h092 h103 step104
#print axioms h104
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
