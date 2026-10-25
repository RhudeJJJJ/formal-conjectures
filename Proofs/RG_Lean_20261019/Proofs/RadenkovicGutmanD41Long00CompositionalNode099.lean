/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode096
import Proofs.RadenkovicGutmanD41Long00CompositionalNode098
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e099 : NestedArithmetic.Expr 3 := .plus e096 e098
noncomputable def p099 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,10086],[0,10086,-3198]],[[0,0,0],[0,0,0],[0,0]],[[0,0,121032],[0,411435,-13612],[121032,-13612]],[[0,0,0],[0,0,0],[0,0]],[[421767,3342033,640830],[3342033,1932576,-98646],[640830,-98646]],[[0,0,0],[0,0,0],[0,0]],[[29232549,29034396,1279856],[29034396,2972623,-115866],[1279856,-115866]],[[0,0,0],[0,0,0],[0,0]],[[315552564,109803699,1019178],[109803699,355716,-47232],[1019178,-47232]],[[0,0,0],[0,0,0],[0,0]],[[1645357839,235877510,-144566],[235877510,-4202008,-6314],[-144566,-6314]],[[0,0,0],[0,0],[0]],[[5235416567,313761725,-868298],[313761725,-5528850],[-868298]],[[0,0,0],[0,0],[0]],[[11227319296,260411992,-664692],[260411992,-3333505],[-664692]],[[0,0,0],[0,0],[0]],[[17074662380,121313834,-240178],[121313834,-1080432],[-240178]],[[0,0,0],[0,0],[0]],[[18903936133,11072788,-43214],[11072788,-182081],[-43214]],[[0,0,0],[0,0],[0]],[[15372842416,-24025385,-3116],[-24025385,-12546],[-3116]],[[0,0],[0]],[[9099314418,-17043372],[-17043372]],[[0,0],[0]],[[3765346684,-5898629],[-5898629]],[[0,0],[0]],[[949950033,-1180554],[-1180554]],[[0,0],[0]],[[45169823,-130749],[-130749]],[[0,0],[0]],[[-71809368,-6232],[-6232]],[[0]],[[-32814760]],[[0]],[[-7705909]],[[0]],[[-1086869]],[[0]],[[-87535]],[[0]],[[-3116]]]
theorem step099 : p099=NestedHorner.add p096 p098 := by decide +kernel
#print axioms step099
theorem h099 : NestedArithmetic.compile e099=p099 := StagedExprCompile.compile_plus e099 e096 e098 p096 p098 p099 rfl h096 h098 step099
#print axioms h099
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
