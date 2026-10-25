/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode043
import Proofs.RadenkovicGutmanD14Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e067 : NestedArithmetic.Expr 3 := .times e043 e061
noncomputable def p067 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,1764],[0,3528,-2016],[1764,-2016,576]],[[0,0,0],[0,0,0],[0,0]],[[0,61236,-2856],[61236,-40704,1632],[-2856,1632]],[[0,0,0],[0,0,0],[0,0]],[[432216,212004,-28412],[212004,-206296,16896],[-28412,16896]],[[0,0,0],[0,0,0],[0,0]],[[2820312,-434916,-12184],[-434916,-190112,20640],[-12184,20640]],[[0,0,0],[0,0,0],[0,0]],[[1435320,-3348504,138192],[-3348504,444672,8544],[138192,8544]],[[0,0,0],[0,0,0],[0,0]],[[-44346864,-6165284,312808],[-6165284,1217168,1152],[312808,1152]],[[0,0,0],[0,0],[0]],[[-211220176,-1905788,311844],[-1905788,1251624],[311844]],[[0,0,0],[0,0],[0]],[[-507757264,10596368,169976],[10596368,686080],[169976]],[[0,0,0],[0,0],[0]],[[-759594792,21195132,52324],[21195132,210920],[52324]],[[0,0,0],[0,0],[0]],[[-728379224,21003092,8544],[21003092,34320],[8544]],[[0,0,0],[0,0],[0]],[[-397802720,13031256,576],[13031256,2304],[576]],[[0,0],[0]],[[-16672760,5353460],[5353460]],[[0,0],[0]],[[180738344,1459948],[1459948]],[[0,0],[0]],[[179627040,254716],[254716]],[[0,0],[0]],[[101242512,25776],[25776]],[[0,0],[0]],[[38523936,1152],[1152]],[[0]],[[10268680]],[[0]],[[1901480]],[[0]],[[233928]],[[0]],[[17232]],[[0]],[[576]]]
theorem step067 : p067=NestedArithmetic.mul p043 p061 := by decide +kernel
#print axioms step067
theorem h067 : NestedArithmetic.compile e067=p067 := StagedExprCompile.compile_times e067 e043 e061 p043 p061 p067 rfl h043 h061 step067
#print axioms h067
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
