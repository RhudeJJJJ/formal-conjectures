/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode043
import Proofs.RadenkovicGutmanD11Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e067 : NestedArithmetic.Expr 3 := .times e043 e061
noncomputable def p067 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,1089],[0,2178,-1188],[1089,-1188,324]],[[0,0,0],[0,0,0],[0,0]],[[0,38313,-1254],[38313,-23406,684],[-1254,684]],[[0,0,0],[0,0,0],[0,0]],[[275724,148419,-16535],[148419,-126058,9216],[-16535,9216]],[[0,0,0],[0,0,0],[0,0]],[[1937088,-176877,-11326],[-176877,-141830,11484],[-11326,11484]],[[0,0,0],[0,0,0],[0,0]],[[2307042,-1919568,68880],[-1919568,192804,4788],[68880,4788]],[[0,0,0],[0,0,0],[0,0]],[[-22171026,-3985325,167194],[-3985325,632252,648],[167194,648]],[[0,0,0],[0,0],[0]],[[-119729674,-2336945,170541],[-2336945,676062],[170541]],[[0,0,0],[0,0],[0]],[[-303026248,4245068,94070],[4245068,377266],[94070]],[[0,0,0],[0,0],[0]],[[-473804394,10422231,29173],[10422231,117206],[29173]],[[0,0,0],[0,0],[0]],[[-482863904,10926785,4788],[10926785,19206],[4788]],[[0,0,0],[0,0],[0]],[[-303023060,6970824,324],[6970824,1296],[324]],[[0,0],[0]],[[-71911370,2913185],[2913185]],[[0,0],[0]],[[64893530,803917],[803917]],[[0,0],[0]],[[84799902,141499],[141499]],[[0,0],[0]],[[51581190,14418],[14418]],[[0,0],[0]],[[20361684,648],[648]],[[0]],[[5548090]],[[0]],[[1042676]],[[0]],[[129660]],[[0]],[[9630]],[[0]],[[324]]]
theorem step067 : p067=NestedArithmetic.mul p043 p061 := by decide +kernel
#print axioms step067
theorem h067 : NestedArithmetic.compile e067=p067 := StagedExprCompile.compile_times e067 e043 e061 p043 p061 p067 rfl h043 h061 step067
#print axioms h067
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
