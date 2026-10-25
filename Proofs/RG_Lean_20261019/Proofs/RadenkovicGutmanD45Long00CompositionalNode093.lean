/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode033
import Proofs.RadenkovicGutmanD45Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e093 : NestedArithmetic.Expr 3 := .times e033 e064
noncomputable def p093 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,2025]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,48600],[0,48600,90]],[[0,0,0],[0,0,0],[0,0]],[[-164025,-109350,273375],[-109350,1057050,151470],[273375,151470]],[[0,0,0],[0,0,0],[0,0]],[[-4490640,4155300,1647540],[4155300,6274260,158220],[1647540,158220]],[[0,0,0],[0,0,0],[0,0]],[[-19207935,40663620,4121280],[40663620,15411870,64710],[4121280,64710]],[[0,0,0],[0,0,0],[0,0]],[[46609830,162227610,5583330],[162227610,20478420,9540],[5583330,9540]],[[0,0,0],[0,0,0],[0,0]],[[663097725,372611340,4477950],[372611340,16113600,180],[4477950,180]],[[0,0,0],[0,0],[0]],[[2742666120,555554700,2181690],[555554700,7714260],[2181690]],[[0,0,0],[0,0],[0]],[[6750969210,568733400,635400],[568733400,2213550],[635400]],[[0,0,0],[0,0],[0]],[[11409987960,410703210,102870],[410703210,354780],[102870]],[[0,0,0],[0,0],[0]],[[14051084130,211155030,7515],[211155030,26010],[7515]],[[0,0,0],[0,0],[0]],[[12993361380,76893570,90],[76893570,360],[90]],[[0,0],[0]],[[9164072880,19418400],[19418400]],[[0,0],[0]],[[4961096280,3251700],[3251700]],[[0,0],[0]],[[2059608825,329940],[329940]],[[0,0],[0]],[[650384640,16470],[16470]],[[0,0],[0]],[[153603810,180],[180]],[[0]],[[26345520]],[[0]],[[3120345]],[[0]],[[232740]],[[0]],[[8955]],[[0]],[[90]]]
theorem step093 : p093=NestedArithmetic.mul p033 p064 := by decide +kernel
#print axioms step093
theorem h093 : NestedArithmetic.compile e093=p093 := StagedExprCompile.compile_times e093 e033 e064 p033 p064 p093 rfl h033 h064 step093
#print axioms h093
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
