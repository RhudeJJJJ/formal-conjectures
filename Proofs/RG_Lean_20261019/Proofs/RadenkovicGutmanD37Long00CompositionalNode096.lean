/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode043
import Proofs.RadenkovicGutmanD37Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e096 : NestedArithmetic.Expr 3 := .times e043 e053
noncomputable def p096 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,4107],[0,4107,-2590]],[[0,0,0],[0,0,0],[0,0]],[[0,36963,36963],[36963,150516,-28823],[36963,-28823]],[[0,0,0],[0,0,0],[0,0]],[[899100,1502496,48951],[1502496,218892,-102416],[48951,-102416]],[[0,0,0],[0,0,0],[0,0]],[[20679300,8816508,-404262],[8816508,-1538608,-104377],[-404262,-104377]],[[0,0,0],[0,0,0],[0,0]],[[164021814,19864486,-1481147],[19864486,-5789020,-40071],[-1481147,-40071]],[[0,0,0],[0,0,0],[0,0]],[[693059580,9316674,-2237316],[9316674,-8817840,-5180],[-2237316,-5180]],[[0,0,0],[0,0],[0]],[[1814187996,-49804072,-1858029],[-49804072,-7358116],[-1858029]],[[0,0,0],[0,0],[0]],[[3118266464,-132062250,-907314],[-132062250,-3605280],[-907314]],[[0,0,0],[0,0],[0]],[[3499332868,-170763251,-259185],[-170763251,-1032596],[-259185]],[[0,0,0],[0,0],[0]],[[2233480654,-139387547,-40071],[-139387547,-159988],[-40071]],[[0,0,0],[0,0],[0]],[[27587866,-76790503,-2590],[-76790503,-10360],[-2590]],[[0,0],[0]],[[-1608240890,-29025390],[-29025390]],[[0,0],[0]],[[-1914816896,-7433559],[-7433559]],[[0,0],[0]],[[-1328930776,-1234098],[-1234098]],[[0,0],[0]],[[-635821320,-119917],[-119917]],[[0,0],[0]],[[-218756580,-5180],[-5180]],[[0]],[[-54318220]],[[0]],[[-9530386]],[[0]],[[-1123098]],[[0]],[[-79846]],[[0]],[[-2590]]]
theorem step096 : p096=NestedArithmetic.mul p043 p053 := by decide +kernel
#print axioms step096
theorem h096 : NestedArithmetic.compile e096=p096 := StagedExprCompile.compile_times e096 e043 e053 p043 p053 p096 rfl h043 h053 step096
#print axioms h096
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
