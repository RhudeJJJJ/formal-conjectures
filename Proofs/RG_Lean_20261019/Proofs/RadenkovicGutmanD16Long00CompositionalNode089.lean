/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode033
import Proofs.RadenkovicGutmanD16Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e089 : NestedArithmetic.Expr 3 := .times e033 e061
noncomputable def p089 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,768],[0,768,-448]],[[0,0,0],[0,0,0],[0,0]],[[0,-6912,6912],[-6912,25344,-4736],[6912,-4736]],[[0,0,0],[0,0,0],[0,0]],[[-67392,76032,12096],[76032,28416,-17408],[12096,-17408]],[[0,0,0],[0,0,0],[0,0]],[[-27648,415872,-59904],[415872,-307456,-17920],[-59904,-17920]],[[0,0,0],[0,0,0],[0,0]],[[2282688,-387328,-241664],[-387328,-1083904,-6912],[-241664,-6912]],[[0,0,0],[0,0,0],[0,0]],[[7772928,-6745344,-374784],[-6745344,-1612800,-896],[-374784,-896]],[[0,0,0],[0,0],[0]],[[-6710080,-20856064,-315264],[-20856064,-1325056],[-315264]],[[0,0,0],[0,0],[0]],[[-108751872,-35255936,-155136],[-35255936,-641280],[-155136]],[[0,0,0],[0,0],[0]],[[-356842112,-38405888,-44544],[-38405888,-181760],[-44544]],[[0,0,0],[0,0],[0]],[[-687358976,-28600064,-6912],[-28600064,-27904],[-6912]],[[0,0,0],[0,0],[0]],[[-909458176,-14882304,-448],[-14882304,-1792],[-448]],[[0,0],[0]],[[-877052672,-5412480],[-5412480]],[[0,0],[0]],[[-633749504,-1348608],[-1348608]],[[0,0],[0]],[[-347347200,-219392],[-219392]],[[0,0],[0]],[[-144694080,-20992],[-20992]],[[0,0],[0]],[[-45497856,-896],[-896]],[[0]],[[-10616448]],[[0]],[[-1781248]],[[0]],[[-203072]],[[0]],[[-14080]],[[0]],[[-448]]]
theorem step089 : p089=NestedArithmetic.mul p033 p061 := by decide +kernel
#print axioms step089
theorem h089 : NestedArithmetic.compile e089=p089 := StagedExprCompile.compile_times e089 e033 e061 p033 p061 p089 rfl h033 h061 step089
#print axioms h089
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
