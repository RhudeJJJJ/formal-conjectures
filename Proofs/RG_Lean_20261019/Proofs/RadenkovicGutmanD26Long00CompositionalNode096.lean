/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode043
import Proofs.RadenkovicGutmanD26Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e096 : NestedArithmetic.Expr 3 := .times e043 e053
noncomputable def p096 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,2028],[0,2028,-1248]],[[0,0,0],[0,0,0],[0,0]],[[0,18252,18252],[18252,74880,-13676],[18252,-13676]],[[0,0,0],[0,0,0],[0,0]],[[446472,746928,26676],[746928,122928,-49088],[26676,-49088]],[[0,0,0],[0,0,0],[0,0]],[[10299744,4455360,-186264],[4455360,-689936,-50180],[-186264,-50180]],[[0,0,0],[0,0,0],[0,0]],[[82162080,10445032,-701324],[10445032,-2710032,-19292],[-701324,-19292]],[[0,0,0],[0,0,0],[0,0]],[[349875552,6651528,-1067664],[6651528,-4178304,-2496],[-1067664,-2496]],[[0,0,0],[0,0],[0]],[[925825576,-20528144,-890084],[-20528144,-3508336],[-890084]],[[0,0,0],[0,0],[0]],[[1618202976,-59839000,-435656],[-59839000,-1725776],[-435656]],[[0,0,0],[0,0],[0]],[[1873460576,-79380652,-124644],[-79380652,-495664],[-124644]],[[0,0,0],[0,0],[0]],[[1302008552,-65599404,-19292],[-65599404,-76960],[-19292]],[[0,0,0],[0,0],[0]],[[219583208,-36409932,-1248],[-36409932,-4992],[-1248]],[[0,0],[0]],[[-630687720,-13832520],[-13832520]],[[0,0],[0]],[[-845188864,-3555916],[-3555916]],[[0,0],[0]],[[-608475920,-592072],[-592072]],[[0,0],[0]],[[-296422568,-57668],[-57668]],[[0,0],[0]],[[-103095408,-2496],[-2496]],[[0]],[[-25785760]],[[0]],[[-4548024]],[[0]],[[-538096]],[[0]],[[-38376]],[[0]],[[-1248]]]
theorem step096 : p096=NestedArithmetic.mul p043 p053 := by decide +kernel
#print axioms step096
theorem h096 : NestedArithmetic.compile e096=p096 := StagedExprCompile.compile_times e096 e043 e053 p043 p053 p096 rfl h043 h053 step096
#print axioms h096
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
