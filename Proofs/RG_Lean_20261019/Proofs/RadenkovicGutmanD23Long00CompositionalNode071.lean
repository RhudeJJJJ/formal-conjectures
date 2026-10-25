/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode043
import Proofs.RadenkovicGutmanD23Long00CompositionalNode066
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e071 : NestedArithmetic.Expr 3 := .times e043 e066
noncomputable def p071 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-1587],[0,-1587,966]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-14283,-23805],[-14283,-77832,16169],[-23805,16169,84]],[[0,0,0],[0,0,0],[0,0]],[[-350244,-963792,-53337],[-963792,-80184,63934],[-53337,63934]],[[0,0,0],[0,0,0],[0,0]],[[-11623284,-6641442,224062],[-6641442,1256284,73009],[224062,73009]],[[0,0,0],[0,0,0],[0,0]],[[-107777574,-18136276,1074715],[-18136276,4667496,31825],[1074715,31825]],[[0,0,0],[0,0,0],[0,0]],[[-509100060,-17823118,1862354],[-17823118,7415040,5162],[1862354,5162]],[[0,0,0],[0,0,0],[0,0]],[[-1469218456,22116078,1722921],[22116078,6509772,168],[1722921,168]],[[0,0,0],[0,0],[0]],[[-2788546964,92609548,927034],[92609548,3377628],[927034]],[[0,0,0],[0,0],[0]],[[-3536780484,138707623,292465],[138707623,1039120],[292465]],[[0,0,0],[0,0],[0]],[[-2822342146,124754755,51231],[124754755,179584],[51231]],[[0,0,0],[0,0],[0]],[[-937210326,74472731,4196],[74472731,14836],[4196]],[[0,0,0],[0,0],[0]],[[807725774,30342372,84],[30342372,336],[84]],[[0,0],[0]],[[1460873336,8400489],[8400489]],[[0,0],[0]],[[1169900756,1529214],[1529214]],[[0,0],[0]],[[613471060,169699],[169699]],[[0,0],[0]],[[227573912,9674],[9674]],[[0,0],[0]],[[60719164,168],[168]],[[0]],[[11516246]],[[0]],[[1495566]],[[0]],[[123202]],[[0]],[[5478]],[[0]],[[84]]]
theorem step071 : p071=NestedArithmetic.mul p043 p066 := by decide +kernel
#print axioms step071
theorem h071 : NestedArithmetic.compile e071=p071 := StagedExprCompile.compile_times e071 e043 e066 p043 p066 p071 rfl h043 h066 step071
#print axioms h071
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
