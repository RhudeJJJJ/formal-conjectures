/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode076
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e077 : NestedArithmetic.Expr 3 := .scaled (-1) e076
noncomputable def p077 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,6561],[0,13122],[6561]],[[0,0,0],[0,0],[0]],[[0,216513,56862],[216513,113724],[56862]],[[0,0,0],[0,0],[0]],[[1771470,2421009,193185],[2421009,386370],[193185]],[[0,0,0],[0,0],[0]],[[24210090,11567043,333882],[11567043,667764],[333882]],[[0,0,0],[0,0],[0]],[[147583134,31310550,323676],[31310550,647352],[323676]],[[0,0,0],[0,0],[0]],[[534222864,53744067,182250],[53744067,364500],[182250]],[[0,0,0],[0,0],[0]],[[1289306484,61919073,59049],[61919073,118098],[59049]],[[0,0,0],[0,0],[0]],[[2206038564,49306644,10206],[49306644,20412],[10206]],[[0,0,0],[0,0],[0]],[[2774869974,27453411,729],[27453411,1458],[729]],[[0,0],[0]],[[2622911382,10649961],[10649961]],[[0,0],[0]],[[1886453712,2818314],[2818314]],[[0,0],[0]],[[1037642562,484785],[484785]],[[0,0],[0]],[[435809322,48843],[48843]],[[0,0],[0]],[[138530412,2187],[2187]],[[0]],[[32726268]],[[0]],[[5563728]],[[0]],[[642978]],[[0]],[[45198]],[[0]],[[1458]]]
theorem step077 : p077=NestedHorner.scale (-1) p076 := by decide +kernel
#print axioms step077
theorem h077 : NestedArithmetic.compile e077=p077 := StagedExprCompile.compile_scaled (-1) e077 e076 p076 p077 rfl h076 step077
#print axioms h077
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
