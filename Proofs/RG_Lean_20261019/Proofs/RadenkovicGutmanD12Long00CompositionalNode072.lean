/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode051
import Proofs.RadenkovicGutmanD12Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e072 : NestedArithmetic.Expr 3 := .times e051 e061
noncomputable def p072 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,432],[0,432,-240]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-3888,6480],[-3888,19440,-3816],[6480,-3816,-40]],[[0,0,0],[0,0,0],[0,0]],[[-38880,115992,17928],[115992,14616,-15864],[17928,-15864]],[[0,0,0],[0,0,0],[0,0]],[[440640,706968,-41616],[706968,-365376,-18768],[-41616,-18768]],[[0,0,0],[0,0,0],[0,0]],[[5164776,234000,-247680],[234000,-1348040,-8648],[-247680,-8648]],[[0,0,0],[0,0,0],[0,0]],[[12048984,-8092968,-452616],[-8092968,-2177776,-1576],[-452616,-1576]],[[0,0,0],[0,0,0],[0,0]],[[-40270056,-30335568,-432720],[-30335568,-1957056,-80],[-432720,-80]],[[0,0,0],[0,0],[0]],[[-325095136,-57359000,-240040],[-57359000,-1044480],[-240040]],[[0,0,0],[0,0],[0]],[[-1000979728,-68228816,-78592],[-68228816,-332872],[-78592]],[[0,0,0],[0,0],[0]],[[-1912991584,-54868456,-14568],[-54868456,-60448],[-14568]],[[0,0,0],[0,0],[0]],[[-2549975272,-30686600,-1336],[-30686600,-5448],[-1336]],[[0,0,0],[0,0],[0]],[[-2491706464,-12003520,-40],[-12003520,-160],[-40]],[[0,0],[0]],[[-1829814848,-3242352],[-3242352]],[[0,0],[0]],[[-1021858672,-583904],[-583904]],[[0,0],[0]],[[-435162680,-65216],[-65216]],[[0,0],[0]],[[-140582560,-3872],[-3872]],[[0,0],[0]],[[-33973680,-80],[-80]],[[0]],[[-5985120]],[[0]],[[-735256]],[[0]],[[-58208]],[[0]],[[-2536]],[[0]],[[-40]]]
theorem step072 : p072=NestedArithmetic.mul p051 p061 := by decide +kernel
#print axioms step072
theorem h072 : NestedArithmetic.compile e072=p072 := StagedExprCompile.compile_times e072 e051 e061 p051 p061 p072 rfl h051 h061 step072
#print axioms h072
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
