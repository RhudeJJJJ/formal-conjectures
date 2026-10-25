/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode043
import Proofs.RadenkovicGutmanD6Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e067 : NestedArithmetic.Expr 3 := .times e043 e061
noncomputable def p067 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,324],[0,648,-288],[324,-288,64]],[[0,0,0],[0,0,0],[0,0]],[[0,11988,216],[11988,-4896,-96],[216,-96]],[[0,0,0],[0,0,0],[0,0]],[[92664,65124,-3420],[65124,-34008,1536],[-3420,1536]],[[0,0,0],[0,0,0],[0,0]],[[814968,67068,-5976],[67068,-61120,2144],[-5976,2144]],[[0,0,0],[0,0,0],[0,0]],[[2487672,-314808,5520],[-314808,-17216,928],[5520,928]],[[0,0,0],[0,0,0],[0,0]],[[455664,-1117380,24744],[-1117380,73872,128],[24744,128]],[[0,0,0],[0,0],[0]],[[-19248944,-1491580,28996],[-1491580,106152],[28996]],[[0,0,0],[0,0],[0]],[[-67539728,-672112,17080],[-672112,66016],[17080]],[[0,0,0],[0,0],[0]],[[-127042664,684316,5508],[684316,21736],[5508]],[[0,0,0],[0,0],[0]],[[-155310584,1325300,928],[1325300,3696],[928]],[[0,0,0],[0,0],[0]],[[-128932640,1034104,64],[1034104,256],[64]],[[0,0],[0]],[[-70720120,480660],[480660]],[[0,0],[0]],[[-21222680,141932],[141932]],[[0,0],[0]],[[1456832,26204],[26204]],[[0,0],[0]],[[5068720,2768],[2768]],[[0,0],[0]],[[2761824,128],[128]],[[0]],[[874440]],[[0]],[[179656]],[[0]],[[23720]],[[0]],[[1840]],[[0]],[[64]]]
theorem step067 : p067=NestedArithmetic.mul p043 p061 := by decide +kernel
#print axioms step067
theorem h067 : NestedArithmetic.compile e067=p067 := StagedExprCompile.compile_times e067 e043 e061 p043 p061 p067 rfl h043 h061 step067
#print axioms h067
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
