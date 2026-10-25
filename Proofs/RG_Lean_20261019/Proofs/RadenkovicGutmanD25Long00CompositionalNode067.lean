/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode043
import Proofs.RadenkovicGutmanD25Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e067 : NestedArithmetic.Expr 3 := .times e043 e061
noncomputable def p067 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,5625],[0,11250,-6900],[5625,-6900,2116]],[[0,0,0],[0,0,0],[0,0]],[[0,191025,-13350],[191025,-143862,8188],[-13350,8188]],[[0,0,0],[0,0,0],[0,0]],[[1305396,532467,-97679],[532467,-660970,64768],[-97679,64768]],[[0,0,0],[0,0,0],[0,0]],[[7405992,-2097621,-238],[-2097621,-366222,77004],[-238,77004]],[[0,0,0],[0,0,0],[0,0]],[[-6659118,-11578616,593152],[-11578616,2175764,31556],[593152,31556]],[[0,0,0],[0,0,0],[0,0]],[[-180840474,-17104949,1232650],[-17104949,4965308,4232],[1232650,4232]],[[0,0,0],[0,0],[0]],[[-746898594,5696367,1191701],[5696367,4861054],[1191701]],[[0,0,0],[0,0],[0]],[[-1665505240,55707500,638950],[55707500,2601642],[638950]],[[0,0,0],[0,0],[0]],[[-2306281978,92330911,194653],[92330911,788310],[194653]],[[0,0,0],[0,0],[0]],[[-1942911752,85640137,31556],[85640137,127006],[31556]],[[0,0,0],[0,0],[0]],[[-683249508,51284240,2116],[51284240,8464],[2116]],[[0,0],[0]],[[544902870,20594345],[20594345]],[[0,0],[0]],[[1017292810,5526285],[5526285]],[[0,0],[0]],[[814929862,952435],[952435]],[[0,0],[0]],[[422921166,95450],[95450]],[[0,0],[0]],[[153900516,4232],[4232]],[[0]],[[39874410]],[[0]],[[7238460]],[[0]],[[877428]],[[0]],[[63894]],[[0]],[[2116]]]
theorem step067 : p067=NestedArithmetic.mul p043 p061 := by decide +kernel
#print axioms step067
theorem h067 : NestedArithmetic.compile e067=p067 := StagedExprCompile.compile_times e067 e043 e061 p043 p061 p067 rfl h043 h061 step067
#print axioms h067
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
