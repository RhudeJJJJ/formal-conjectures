/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode075
import Proofs.RadenkovicGutmanD19Long00CompositionalNode077
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e078 : NestedArithmetic.Expr 3 := .plus e075 e077
noncomputable def p078 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,361]],[[0,0],[0,0,0],[0,0]],[[0,0,3249],[0,6498,6498],[3249,6498]],[[0,0,0],[0,0,0],[0,0]],[[-29241,107217,57399],[107217,173280,17328],[57399,17328]],[[0,0,0],[0,0,0],[0,0]],[[370386,1725219,251617],[1725219,815138,15884],[251617,15884]],[[0,0,0],[0,0,0],[0,0]],[[10439037,9938691,516230],[9938691,1734244,5776],[516230,5776]],[[0,0,0],[0,0,0],[0,0]],[[80447406,30593306,593484],[30593306,2053368,722],[593484,722]],[[0,0,0],[0,0],[0]],[[334733279,58584163,410096],[58584163,1459884],[410096]],[[0,0,0],[0,0],[0]],[[897554300,75206047,173641],[75206047,636082],[173641]],[[0,0,0],[0,0],[0]],[[1684314090,67355380,44042],[67355380,166060],[44042]],[[0,0,0],[0,0],[0]],[[2316687898,42934091,6137],[42934091,23826],[6137]],[[0,0,0],[0,0],[0]],[[2401433370,19586777,361],[19586777,1444],[361]],[[0,0],[0]],[[1907473460,6344936],[6344936]],[[0,0],[0]],[[1171275330,1424145],[1424145]],[[0,0],[0]],[[557361618,210463],[210463]],[[0,0],[0]],[[204794939,18411],[18411]],[[0,0],[0]],[[57498636,722],[722]],[[0]],[[12097110]],[[0]],[[1844710]],[[0]],[[192413]],[[0]],[[12274]],[[0]],[[361]]]
theorem step078 : p078=NestedHorner.add p075 p077 := by decide +kernel
#print axioms step078
theorem h078 : NestedArithmetic.compile e078=p078 := StagedExprCompile.compile_plus e078 e075 e077 p075 p077 p078 rfl h075 h077 step078
#print axioms h078
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
