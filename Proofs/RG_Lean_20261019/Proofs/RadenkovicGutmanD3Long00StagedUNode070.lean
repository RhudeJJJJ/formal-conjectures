/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode050
import Proofs.RadenkovicGutmanD3Long00StagedUNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e070 : NestedArithmetic.Expr 3 := .times e050 e060
noncomputable def p070 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,27],[0,27,-6]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-243,405],[-243,1215,-9],[405,-9,-4]],[[0,0,0],[0,0,0],[0,0]],[[-3159,7857,2457],[7857,6192,-294],[2457,-294]],[[0,0,0],[0,0,0],[0,0]],[[25353,81000,5418],[81000,8655,-489],[5418,-489]],[[0,0,0],[0,0,0],[0,0]],[[540000,313029,4365],[313029,-6860,-305],[4365,-305]],[[0,0,0],[0,0,0],[0,0]],[[3195711,620760,-1914],[620760,-34048,-82],[-1914,-82]],[[0,0,0],[0,0,0],[0,0]],[[10058061,618933,-6561],[618933,-43710,-8],[-6561,-8]],[[0,0,0],[0,0],[0]],[[19146368,78730,-5554],[78730,-29361],[-5554]],[[0,0,0],[0,0],[0]],[[21673532,-608315,-2425],[-608315,-11464],[-2425]],[[0,0,0],[0,0],[0]],[[9821903,-872209,-591],[-872209,-2605],[-591]],[[0,0,0],[0,0],[0]],[[-11625622,-657506,-76],[-657506,-318],[-76]],[[0,0,0],[0,0],[0]],[[-27884644,-317182,-4],[-317182,-16],[-4]],[[0,0],[0]],[[-29695148,-102342],[-102342]],[[0,0],[0]],[[-20834095,-21980],[-21980]],[[0,0],[0]],[[-10485071,-3008],[-3008]],[[0,0],[0]],[[-3888148,-236],[-236]],[[0,0],[0]],[[-1065864,-8],[-8]],[[0]],[[-213195]],[[0]],[[-30169]],[[0]],[[-2849]],[[0]],[[-160]],[[0]],[[-4]]]
theorem step070 : p070=NestedArithmetic.mul p050 p060 := by decide +kernel
#print axioms step070
theorem h070 : NestedArithmetic.compile e070=p070 := StagedExprCompile.compile_times e070 e050 e060 p050 p060 p070 rfl h050 h060 step070
#print axioms h070
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
