/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode043
import Proofs.RadenkovicGutmanD16Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e067 : NestedArithmetic.Expr 3 := .times e043 e061
noncomputable def p067 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,2304],[0,4608,-2688],[2304,-2688,784]],[[0,0,0],[0,0,0],[0,0]],[[0,79488,-4224],[79488,-54816,2464],[-4224,2464]],[[0,0,0],[0,0,0],[0,0]],[[555984,260064,-38000],[260064,-270208,23296],[-38000,23296]],[[0,0,0],[0,0,0],[0,0]],[[3496608,-653472,-11776],[-653472,-222240,28224],[-11776,28224]],[[0,0,0],[0,0,0],[0,0]],[[536112,-4495328,197440],[-4495328,665024,11648],[197440,11648]],[[0,0,0],[0,0,0],[0,0]],[[-62714016,-7809920,434944],[-7809920,1711232,1568],[434944,1568]],[[0,0,0],[0,0],[0]],[[-285214704,-1227360,429536],[-1227360,1732672],[429536]],[[0,0,0],[0,0],[0]],[[-670677568,16247648,232960],[16247648,942816],[232960]],[[0,0,0],[0,0],[0]],[[-982510624,30431296,71488],[30431296,288576],[71488]],[[0,0,0],[0,0],[0]],[[-912465824,29518720,11648],[29518720,46816],[11648]],[[0,0,0],[0,0],[0]],[[-456958080,18112544,784],[18112544,3136],[784]],[[0,0],[0]],[[43466880,7388960],[7388960]],[[0,0],[0]],[[284707840,2005152],[2005152]],[[0,0],[0]],[[261520672,348544],[348544]],[[0,0],[0]],[[143414160,35168],[35168]],[[0,0],[0]],[[53799744,1568],[1568]],[[0]],[[14214240]],[[0]],[[2616096]],[[0]],[[320400]],[[0]],[[23520]],[[0]],[[784]]]
theorem step067 : p067=NestedArithmetic.mul p043 p061 := by decide +kernel
#print axioms step067
theorem h067 : NestedArithmetic.compile e067=p067 := StagedExprCompile.compile_times e067 e043 e061 p043 p061 p067 rfl h043 h061 step067
#print axioms h067
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
