/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode033
import Proofs.RadenkovicGutmanD37Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e089 : NestedArithmetic.Expr 3 := .times e033 e061
noncomputable def p089 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,4107],[0,4107,-2590]],[[0,0,0],[0,0,0],[0,0]],[[0,-36963,36963],[-36963,135531,-28823],[36963,-28823]],[[0,0,0],[0,0,0],[0,0]],[[-344655,406593,48951],[406593,89022,-102416],[48951,-102416]],[[0,0,0],[0,0,0],[0,0]],[[124875,1940724,-404262],[1940724,-1979833,-104377],[-404262,-104377]],[[0,0,0],[0,0,0],[0,0]],[[13040946,-4337029,-1481147],[-4337029,-6551590,-40071],[-1481147,-40071]],[[0,0,0],[0,0,0],[0,0]],[[37604247,-44190654,-2237316],[-44190654,-9557100,-5180],[-2237316,-5180]],[[0,0,0],[0,0],[0]],[[-73649869,-128733841,-1858029],[-128733841,-7774366],[-1858029]],[[0,0,0],[0,0],[0]],[[-720981630,-212505134,-907314],[-212505134,-3740145],[-907314]],[[0,0,0],[0,0],[0]],[[-2226756200,-228486359,-259185],[-228486359,-1055906],[-259185]],[[0,0,0],[0,0],[0]],[[-4182948605,-168730397,-40071],[-168730397,-161653],[-40071]],[[0,0,0],[0,0],[0]],[[-5456750380,-87287070,-2590],[-87287070,-10360],[-2590]],[[0,0],[0]],[[-5213899844,-31607250],[-31607250]],[[0,0],[0]],[[-3742833272,-7849032],[-7849032]],[[0,0],[0]],[[-2041277235,-1273466],[-1273466]],[[0,0],[0]],[[-847059093,-121582],[-121582]],[[0,0],[0]],[[-265525986,-5180],[-5180]],[[0]],[[-61799916]],[[0]],[[-10346791]],[[0]],[[-1177451]],[[0]],[[-81511]],[[0]],[[-2590]]]
theorem step089 : p089=NestedArithmetic.mul p033 p061 := by decide +kernel
#print axioms step089
theorem h089 : NestedArithmetic.compile e089=p089 := StagedExprCompile.compile_times e089 e033 e061 p033 p061 p089 rfl h033 h061 step089
#print axioms h089
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
