/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode110
import Proofs.RadenkovicGutmanD7Long00CompositionalNode111
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e112 : NestedArithmetic.Expr 3 := .plus e110 e111
noncomputable def p112 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,49]],[[0,0],[0,0,0],[0,0,0]],[[0,0,441],[0,0,1050],[441,1050,128]],[[0,0,0],[0,0,0],[0,0,0]],[[3969,9450,11067],[9450,22212,5552],[11067,5552,4]],[[0,0,0],[0,0,0],[0,0]],[[191430,257742,71905],[257742,177096,9996],[71905,9996]],[[0,0,0],[0,0,0],[0,0]],[[3277071,2149110,217446],[2149110,581360,7896],[217446,7896]],[[0,0,0],[0,0,0],[0,0]],[[27184242,9143936,368092],[9143936,1043048,2770],[368092,2770]],[[0,0,0],[0,0,0],[0,0]],[[133557313,23731342,378184],[23731342,1133512,376],[378184,376]],[[0,0,0],[0,0,0],[0,0]],[[433874340,40956222,244257],[40956222,776704,8],[244257,8]],[[0,0,0],[0,0],[0]],[[994679618,49277340,99726],[49277340,337248],[99726]],[[0,0,0],[0,0],[0]],[[1676660050,42432416,25105],[42432416,90344],[25105]],[[0,0,0],[0,0],[0]],[[2134393504,26480214,3621],[26480214,13844],[3621]],[[0,0,0],[0,0],[0]],[[2088112616,11995602,248],[11995602,1000],[248]],[[0,0,0],[0,0],[0]],[[1586922128,3907694,4],[3907694,16],[4]],[[0,0],[0]],[[941928734,894264],[894264]],[[0,0],[0]],[[436881645,137410],[137410]],[[0,0],[0]],[[157625772,12994],[12994]],[[0,0],[0]],[[43778906,624],[624]],[[0,0],[0]],[[9189734,8],[8]],[[0]],[[1414613]],[[0]],[[151874]],[[0]],[[10397]],[[0]],[[376]],[[0]],[[4]]]
theorem step112 : p112=NestedHorner.add p110 p111 := by decide +kernel
#print axioms step112
theorem h112 : NestedArithmetic.compile e112=p112 := StagedExprCompile.compile_plus e112 e110 e111 p110 p111 p112 rfl h110 h111 step112
#print axioms h112
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
