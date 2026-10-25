/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode043
import Proofs.RadenkovicGutmanD11Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e100 : NestedArithmetic.Expr 3 := .times e043 e057
noncomputable def p100 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-1089],[0,-2178,594],[-1089,594]],[[0,0,0],[0,0,0],[0,0]],[[0,-43659,-4092],[-43659,726,2574],[-4092,2574]],[[0,0,0],[0,0,0],[0,0]],[[-409860,-373923,5357],[-373923,70114,3168],[5357,3168]],[[0,0,0],[0,0,0],[0,0]],[[-5072760,-1264923,47938],[-1264923,250118,1386],[47938,1386]],[[0,0,0],[0,0,0],[0,0]],[[-27943542,-1994388,96162],[-1994388,401412,198],[96162,198]],[[0,0,0],[0,0],[0]],[[-90583350,-718399,95678],[-718399,355300],[95678]],[[0,0,0],[0,0],[0]],[[-191742254,2888897,53361],[2888897,183546],[53361]],[[0,0,0],[0,0],[0]],[[-276313400,6064432,16918],[6064432,55022],[16918]],[[0,0,0],[0,0],[0]],[[-270433614,6190635,2849],[6190635,8866],[2849]],[[0,0,0],[0,0],[0]],[[-166025332,3949297,198],[3949297,594],[198]],[[0,0],[0]],[[-37993384,1666962],[1666962]],[[0,0],[0]],[[37053830,466675],[466675]],[[0,0],[0]],[[47871142,83501],[83501]],[[0,0],[0]],[[29287698,8657],[8657]],[[0,0],[0]],[[11675994,396],[396]],[[0]],[[3218820]],[[0]],[[612590]],[[0]],[[77176]],[[0]],[[5808]],[[0]],[[198]]]
theorem step100 : p100=NestedArithmetic.mul p043 p057 := by decide +kernel
#print axioms step100
theorem h100 : NestedArithmetic.compile e100=p100 := StagedExprCompile.compile_times e100 e043 e057 p043 p057 p100 rfl h043 h057 step100
#print axioms h100
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
