/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode221
import Proofs.RadenkovicGutmanD11Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e222 : NestedArithmetic.Expr 3 := .times e221 e003
noncomputable def p222 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[242,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[7502,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[106722,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[923472,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[5431932,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[22993388,363,0],[363,0],[0]],[[0,0,0],[0,0],[0]],[[72335978,8107,0],[8107,0],[0]],[[0,0,0],[0,0],[0]],[[172228738,80465,0],[80465,0],[0]],[[0,0,0],[0,0],[0]],[[313115088,467786,0],[467786,0],[0]],[[0,0,0],[0,0],[0]],[[435352918,1767689,0],[1767689,0],[0]],[[0,0,0],[0,0],[0]],[[460575126,4556739,121],[4556739,242],[121]],[[0,0,0],[0,0],[0]],[[366160036,8183956,1694],[8183956,3388],[1694]],[[0,0,0],[0,0],[0]],[[214000116,10277377,9801],[10277377,19602],[9801]],[[0,0,0],[0,0],[0]],[[88670736,8920483,30250],[8920483,60500],[30250]],[[0,0,0],[0,0],[0]],[[24495966,5196950,53724],[5196950,107448],[53724]],[[0,0,0],[0,0],[0]],[[4018410,1919907,55418],[1919907,110836],[55418]],[[0,0,0],[0,0],[0]],[[294030,401841,32065],[401841,64130],[32065]],[[0,0,0],[0,0],[0]],[[0,35937,9438],[35937,18876],[9438]],[[0,0,0],[0,0],[0]],[[0,0,1089],[0,2178],[1089]]]
theorem step222 : p222=NestedArithmetic.mul p221 p003 := by decide +kernel
#print axioms step222
theorem h222 : NestedArithmetic.compile e222=p222 := StagedExprCompile.compile_times e222 e221 e003 p221 p003 p222 rfl h221 h003 step222
#print axioms h222
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
