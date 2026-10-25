/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode217
import Proofs.RadenkovicGutmanD44Long00CompositionalNode219
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e220 : NestedArithmetic.Expr 3 := .times e217 e219
noncomputable def p220 : NestedHorner.Poly 3 := [[[-3872],[0],[0]],[[0,0],[0,0],[0]],[[-120032,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-1707552,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-14775552,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-86910912,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-367894208,-5808,0],[-5808,0],[0]],[[0,0,0],[0,0],[0]],[[-1157375648,-129712,0],[-129712,0],[0]],[[0,0,0],[0,0],[0]],[[-2755659808,-1287440,0],[-1287440,0],[0]],[[0,0,0],[0,0],[0]],[[-5009841408,-7484576,0],[-7484576,0],[0]],[[0,0,0],[0,0],[0]],[[-6965646688,-28283024,0],[-28283024,0],[0]],[[0,0,0],[0,0],[0]],[[-7369202016,-72907824,-1936],[-72907824,-3872],[-1936]],[[0,0,0],[0,0],[0]],[[-5858560576,-130943296,-27104],[-130943296,-54208],[-27104]],[[0,0,0],[0,0],[0]],[[-3424001856,-164438032,-156816],[-164438032,-313632],[-156816]],[[0,0,0],[0,0],[0]],[[-1418731776,-142727728,-484000],[-142727728,-968000],[-484000]],[[0,0,0],[0,0],[0]],[[-391935456,-83151200,-859584],[-83151200,-1719168],[-859584]],[[0,0,0],[0,0],[0]],[[-64294560,-30718512,-886688],[-30718512,-1773376],[-886688]],[[0,0,0],[0,0],[0]],[[-4704480,-6429456,-513040],[-6429456,-1026080],[-513040]],[[0,0,0],[0,0],[0]],[[0,-574992,-151008],[-574992,-302016],[-151008]],[[0,0,0],[0,0],[0]],[[0,0,-17424],[0,-34848],[-17424]]]
theorem step220 : p220=NestedArithmetic.mul p217 p219 := by decide +kernel
#print axioms step220
theorem h220 : NestedArithmetic.compile e220=p220 := StagedExprCompile.compile_times e220 e217 e219 p217 p219 p220 rfl h217 h219 step220
#print axioms h220
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
