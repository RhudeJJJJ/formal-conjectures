/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode043
import Proofs.RadenkovicGutmanD40Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e067 : NestedArithmetic.Expr 3 := .times e043 e061
noncomputable def p067 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,14400],[0,28800,-18240],[14400,-18240,5776]],[[0,0,0],[0,0,0],[0,0]],[[0,483840,-39360],[483840,-385152,24928],[-39360,24928]],[[0,0,0],[0,0,0],[0,0]],[[3254256,1190592,-257264],[1190592,-1687360,179968],[-257264,179968]],[[0,0,0],[0,0,0],[0,0]],[[17070912,-6179616,54272],[-6179616,-604032,211584],[54272,211584]],[[0,0,0],[0,0,0],[0,0]],[[-30101328,-30375296,1722112],[-30375296,6581504,86336],[1722112,86336]],[[0,0,0],[0,0,0],[0,0]],[[-506715264,-39484544,3464320],[-39484544,14137088,11552],[3464320,11552]],[[0,0,0],[0,0],[0]],[[-1984402704,31311552,3307616],[31311552,13579264],[3307616]],[[0,0,0],[0,0],[0]],[[-4275137920,172488800,1761280],[172488800,7197312],[1761280]],[[0,0,0],[0,0],[0]],[[-5678567968,269449216,534208],[269449216,2167680],[534208]],[[0,0,0],[0,0],[0]],[[-4395071552,243907072,86336],[243907072,347776],[86336]],[[0,0,0],[0,0],[0]],[[-915283008,144046400,5776],[144046400,23104],[5776]],[[0,0],[0]],[[2219929920,57314720],[57314720]],[[0,0],[0]],[[3200894080,15277440],[15277440]],[[0,0],[0]],[[2409597952,2619520],[2619520]],[[0,0],[0]],[[1215073776,261440],[261440]],[[0,0],[0]],[[434770176,11552],[11552]],[[0]],[[111387360]],[[0]],[[20057280]],[[0]],[[2416368]],[[0]],[[175104]],[[0]],[[5776]]]
theorem step067 : p067=NestedArithmetic.mul p043 p061 := by decide +kernel
#print axioms step067
theorem h067 : NestedArithmetic.compile e067=p067 := StagedExprCompile.compile_times e067 e043 e061 p043 p061 p067 rfl h043 h061 step067
#print axioms h067
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
