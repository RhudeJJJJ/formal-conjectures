/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode043
import Proofs.RadenkovicGutmanD41Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e100 : NestedArithmetic.Expr 3 := .times e043 e057
noncomputable def p100 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-15129],[0,-30258,9594],[-15129,9594]],[[0,0,0],[0,0,0],[0,0]],[[0,-594459,-44772],[-594459,54366,41574],[-44772,41574]],[[0,0,0],[0,0,0],[0,0]],[[-5512860,-4747923,158957],[-4747923,1277314,51168],[158957,51168]],[[0,0,0],[0,0,0],[0,0]],[[-66065760,-13958163,899458],[-13958163,4290158,22386],[899458,22386]],[[0,0,0],[0,0,0],[0,0]],[[-349707942,-13770588,1674522],[-13770588,6726132,3198],[1674522,3198]],[[0,0,0],[0,0],[0]],[[-1076477550,21756281,1613678],[21756281,5875300],[1613678]],[[0,0,0],[0,0],[0]],[[-2117537414,87132257,884001],[87132257,3008826],[884001]],[[0,0,0],[0,0],[0]],[[-2707339880,131817952,277078],[131817952,896342],[277078]],[[0,0,0],[0,0],[0]],[[-2060522814,119750955,46289],[119750955,143746],[46289]],[[0,0,0],[0,0],[0]],[[-408993532,71798257,3198],[71798257,9594],[3198]],[[0,0],[0]],[[1084540856,29133042],[29133042]],[[0,0],[0]],[[1566275030,7932475],[7932475]],[[0,0],[0]],[[1193235382,1389941],[1389941]],[[0,0],[0]],[[610685898,141737],[141737]],[[0,0],[0]],[[222034434,6396],[6396]],[[0]],[[57827220]],[[0]],[[10585790]],[[0]],[[1296256]],[[0]],[[95448]],[[0]],[[3198]]]
theorem step100 : p100=NestedArithmetic.mul p043 p057 := by decide +kernel
#print axioms step100
theorem h100 : NestedArithmetic.compile e100=p100 := StagedExprCompile.compile_times e100 e043 e057 p043 p057 p100 rfl h043 h057 step100
#print axioms h100
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
