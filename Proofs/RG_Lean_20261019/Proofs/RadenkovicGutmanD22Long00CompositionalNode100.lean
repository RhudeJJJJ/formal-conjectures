/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode043
import Proofs.RadenkovicGutmanD22Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e100 : NestedArithmetic.Expr 3 := .times e043 e057
noncomputable def p100 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-4356],[0,-8712,2640],[-4356,2640]],[[0,0,0],[0,0,0],[0,0]],[[0,-172260,-13992],[-172260,11616,11440],[-13992,11440]],[[0,0,0],[0,0,0],[0,0]],[[-1603800,-1407780,38060],[-1407780,340120,14080],[38060,14080]],[[0,0,0],[0,0,0],[0,0]],[[-19423800,-4348476,237688],[-4348476,1160896,6160],[237688,6160]],[[0,0,0],[0,0,0],[0,0]],[[-104199480,-5235560,451264],[-5235560,1831808,880],[451264,880]],[[0,0,0],[0,0],[0]],[[-326533680,3370532,438680],[3370532,1606000],[438680]],[[0,0,0],[0,0],[0]],[[-659494704,20802364,241516],[20802364,824472],[241516]],[[0,0,0],[0,0],[0]],[[-882660592,33616528,75944],[33616528,246048],[75944]],[[0,0,0],[0,0],[0]],[[-747952920,31402228,12716],[31402228,39512],[12716]],[[0,0,0],[0,0],[0]],[[-290767400,19128604,880],[19128604,2640],[880]],[[0,0],[0]],[[165256256,7843352],[7843352]],[[0,0],[0]],[[355096280,2151820],[2151820]],[[0,0],[0]],[[295403416,379236],[379236]],[[0,0],[0]],[[157248960,38852],[38852]],[[0,0],[0]],[[58474416,1760],[1760]],[[0]],[[15454560]],[[0]],[[2858680]],[[0]],[[352792]],[[0]],[[26136]],[[0]],[[880]]]
theorem step100 : p100=NestedArithmetic.mul p043 p057 := by decide +kernel
#print axioms step100
theorem h100 : NestedArithmetic.compile e100=p100 := StagedExprCompile.compile_times e100 e043 e057 p043 p057 p100 rfl h043 h057 step100
#print axioms h100
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
