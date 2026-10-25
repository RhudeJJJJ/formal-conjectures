/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode089
import Proofs.RadenkovicGutmanD41Long00CompositionalNode091
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e092 : NestedArithmetic.Expr 3 := .plus e089 e091
noncomputable def p092 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,10086],[0,10086,-3198]],[[0,0,0],[0,0,0],[0,0]],[[0,0,121032],[0,408483,-13612],[121032,-13612]],[[0,0,0],[0,0,0],[0,0]],[[395199,3315465,640830],[3315465,1907730,-98646],[640830,-98646]],[[0,0,0],[0,0,0],[0,0]],[[28539567,28739934,1279856],[28739934,2892099,-115866],[1279856,-115866]],[[0,0,0],[0,0,0],[0,0]],[[308819790,108417735,1019178],[108417735,227222,-47232],[1019178,-47232]],[[0,0,0],[0,0,0],[0,0]],[[1609859055,232218260,-144566],[232218260,-4310084,-6314],[-144566,-6314]],[[0,0,0],[0,0],[0]],[[5117505241,307731937,-868298],[307731937,-5574442],[-868298]],[[0,0,0],[0,0],[0]],[[10960814950,253911934,-664692],[253911934,-3339573],[-664692]],[[0,0,0],[0,0],[0]],[[16646256824,116678866,-240178],[116678866,-1078382],[-240178]],[[0,0,0],[0,0],[0]],[[18401632997,8949480,-43214],[8949480,-181261],[-43214]],[[0,0,0],[0,0],[0]],[[14938290222,-24575113,-3116],[-24575113,-12464],[-3116]],[[0,0],[0]],[[8822414686,-17071990],[-17071990]],[[0,0],[0]],[[3638039880,-5868289],[-5868289]],[[0,0],[0]],[[910276793,-1170140],[-1170140]],[[0,0],[0]],[[38517245,-129273],[-129273]],[[0,0],[0]],[[-71380426,-6150],[-6150]],[[0]],[[-32225836]],[[0]],[[-7537645]],[[0]],[[-1060875]],[[0]],[[-85321]],[[0]],[[-3034]]]
theorem step092 : p092=NestedHorner.add p089 p091 := by decide +kernel
#print axioms step092
theorem h092 : NestedArithmetic.compile e092=p092 := StagedExprCompile.compile_plus e092 e089 e091 p089 p091 p092 rfl h089 h091 step092
#print axioms h092
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
