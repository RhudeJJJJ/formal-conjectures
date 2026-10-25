/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode051
import Proofs.RadenkovicGutmanD12Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e097 : NestedArithmetic.Expr 3 := .times e051 e057
noncomputable def p097 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-432],[0,-432]],[[0,0,0],[0,0,0],[0,0]],[[0,3888,-6480],[3888,-19440,-1944],[-6480,-1944]],[[0,0,0],[0,0,0],[0,0]],[[58320,-128952,-50328],[-128952,-144936,-2616],[-50328,-2616]],[[0,0,0],[0,0,0],[0,0]],[[-340200,-1581768,-156024],[-1581768,-431424,-1392],[-156024,-1392]],[[0,0,0],[0,0,0],[0,0]],[[-10003176,-7485120,-253440],[-7485120,-677640,-312],[-253440,-312]],[[0,0,0],[0,0,0],[0,0]],[[-69883344,-19855752,-237624],[-19855752,-619824,-24],[-237624,-24]],[[0,0,0],[0,0],[0]],[[-266034744,-33520752,-133200],[-33520752,-342144],[-133200]],[[0,0,0],[0,0],[0]],[[-658355304,-38246520,-44520],[-38246520,-113760],[-44520]],[[0,0,0],[0,0],[0]],[[-1144677552,-30402144,-8448],[-30402144,-21768],[-8448]],[[0,0,0],[0,0],[0]],[[-1458611856,-17049624,-792],[-17049624,-2112],[-792]],[[0,0,0],[0,0],[0]],[[-1396121448,-6735960,-24],[-6735960,-72],[-24]],[[0,0],[0]],[[-1017866016,-1844400],[-1844400]],[[0,0],[0]],[[-568801152,-337248],[-337248]],[[0,0],[0]],[[-243552528,-38256],[-38256]],[[0,0],[0]],[[-79345800,-2304],[-2304]],[[0,0],[0]],[[-19371240,-48],[-48]],[[0]],[[-3450960]],[[0]],[[-428880]],[[0]],[[-34344]],[[0]],[[-1512]],[[0]],[[-24]]]
theorem step097 : p097=NestedArithmetic.mul p051 p057 := by decide +kernel
#print axioms step097
theorem h097 : NestedArithmetic.compile e097=p097 := StagedExprCompile.compile_times e097 e051 e057 p051 p057 p097 rfl h051 h057 step097
#print axioms h097
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
