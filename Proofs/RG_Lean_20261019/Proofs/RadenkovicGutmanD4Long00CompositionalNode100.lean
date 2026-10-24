/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode050
import Proofs.RadenkovicGutmanD4Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e100 : NestedArithmetic.Expr 3 := .times e050 e052
noncomputable def p100 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,16]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,384],[0,384,8]],[[0,0,0],[0,0,0],[0,0]],[[-1296,864,2160],[864,8784,1328],[2160,1328]],[[0,0,0],[0,0,0],[0,0]],[[-6264,59184,13608],[59184,55680,1600],[13608,1600]],[[0,0,0],[0,0,0],[0,0]],[[337824,500976,35712],[500976,147088,832],[35712,832]],[[0,0,0],[0,0,0],[0,0]],[[4057368,1972976,51200],[1972976,212128,192],[51200,192]],[[0,0,0],[0,0,0],[0,0]],[[21739712,4610880,44128],[4610880,183616,16],[44128,16]],[[0,0,0],[0,0],[0]],[[70737448,7074832,23696],[7074832,98784],[23696]],[[0,0,0],[0,0],[0]],[[156572672,7502064,7936],[7502064,33040],[7936]],[[0,0,0],[0,0],[0]],[[249875120,5646784,1600],[5646784,6624],[1600]],[[0,0,0],[0,0],[0]],[[297422864,3051808,176],[3051808,720],[176]],[[0,0,0],[0,0],[0]],[[269498496,1183408,8],[1183408,32],[8]],[[0,0],[0]],[[188101440,324880],[324880]],[[0,0],[0]],[[101667200,61264],[61264]],[[0,0],[0]],[[42535136,7488],[7488]],[[0,0],[0]],[[13689192,528],[528]],[[0,0],[0]],[[3344448,16],[16]],[[0]],[[606320]],[[0]],[[78560]],[[0]],[[6824]],[[0]],[[352]],[[0]],[[8]]]
theorem step100 : p100=NestedArithmetic.mul p050 p052 := by decide +kernel
#print axioms step100
theorem h100 : NestedArithmetic.compile e100=p100 := StagedExprCompile.compile_times e100 e050 e052 p050 p052 p100 rfl h050 h052 step100
#print axioms h100
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
