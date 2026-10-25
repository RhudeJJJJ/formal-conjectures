/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode096
import Proofs.RadenkovicGutmanD13Long00CompositionalNode098
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e099 : NestedArithmetic.Expr 3 := .plus e096 e098
noncomputable def p099 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,1014],[0,1014,-286]],[[0,0,0],[0,0,0],[0,0]],[[0,0,12168],[0,42003,-676],[12168,-676]],[[0,0,0],[0,0,0],[0,0]],[[45279,342225,67782],[342225,213096,-7982],[67782,-7982]],[[0,0,0],[0,0,0],[0,0]],[[3047733,3053700,147368],[3053700,391079,-9802],[147368,-9802]],[[0,0,0],[0,0,0],[0,0]],[[33242508,11913291,146250],[11913291,238732,-4056],[146250,-4056]],[[0,0,0],[0,0,0],[0,0]],[[175730295,26623038,41522],[26623038,-174824,-546],[41522,-546]],[[0,0,0],[0,0],[0]],[[568019959,37472565,-44538],[37472565,-374946],[-44538]],[[0,0,0],[0,0],[0]],[[1240510856,34216624,-46956],[34216624,-254345],[-46956]],[[0,0,0],[0,0],[0]],[[1928661020,19759402,-18642],[19759402,-87048],[-18642]],[[0,0,0],[0,0],[0]],[[2196582141,6161532,-3510],[6161532,-15145],[-3510]],[[0,0,0],[0,0],[0]],[[1857401624,-10569,-260],[-10569,-1066],[-260]],[[0,0],[0]],[[1166540674,-902044],[-902044]],[[0,0],[0]],[[535529436,-403741],[-403741]],[[0,0],[0]],[[171301897,-89674],[-89674]],[[0,0],[0]],[[32778031,-10517],[-10517]],[[0,0],[0]],[[811824,-520],[-520]],[[0]],[[-1588600]],[[0]],[[-510861]],[[0]],[[-81445]],[[0]],[[-7007]],[[0]],[[-260]]]
theorem step099 : p099=NestedHorner.add p096 p098 := by decide +kernel
#print axioms step099
theorem h099 : NestedArithmetic.compile e099=p099 := StagedExprCompile.compile_plus e099 e096 e098 p096 p098 p099 rfl h096 h098 step099
#print axioms h099
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
