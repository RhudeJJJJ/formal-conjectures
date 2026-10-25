/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode051
import Proofs.RadenkovicGutmanD13Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e101 : NestedArithmetic.Expr 3 := .times e051 e053
noncomputable def p101 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,169]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,4056],[0,4056,26]],[[0,0,0],[0,0,0],[0,0]],[[-13689,9126,22815],[9126,91728,12974],[22815,12974]],[[0,0,0],[0,0,0],[0,0]],[[-70902,615654,138996],[615654,560040,14092],[138996,14092]],[[0,0,0],[0,0,0],[0,0]],[[3400839,5098860,351936],[5098860,1421524,6214],[351936,6214]],[[0,0,0],[0,0,0],[0,0]],[[40643070,19635980,483938],[19635980,1959568,1092],[483938,1092]],[[0,0,0],[0,0,0],[0,0]],[[215153627,44821764,395902],[44821764,1606696,52],[395902,52]],[[0,0,0],[0,0],[0]],[[690411046,67037386,198458],[67037386,806832],[198458]],[[0,0,0],[0,0],[0]],[[1505404238,69076176,60424],[69076176,245908],[60424]],[[0,0,0],[0,0],[0]],[[2363973248,50296090,10582],[50296090,43056],[10582]],[[0,0,0],[0,0],[0]],[[2764755188,26125450,923],[26125450,3744],[923]],[[0,0,0],[0,0],[0]],[[2456891112,9645532,26],[9645532,104],[26]],[[0,0],[0]],[[1677571740,2485600],[2485600]],[[0,0],[0]],[[884029640,430066],[430066]],[[0,0],[0]],[[358954427,46332],[46332]],[[0,0],[0]],[[111404982,2652],[2652]],[[0,0],[0]],[[26008086,52],[52]],[[0]],[[4443920]],[[0]],[[530855]],[[0]],[[40898]],[[0]],[[1729]],[[0]],[[26]]]
theorem step101 : p101=NestedArithmetic.mul p051 p053 := by decide +kernel
#print axioms step101
theorem h101 : NestedArithmetic.compile e101=p101 := StagedExprCompile.compile_times e101 e051 e053 p051 p053 p101 rfl h051 h053 step101
#print axioms h101
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
