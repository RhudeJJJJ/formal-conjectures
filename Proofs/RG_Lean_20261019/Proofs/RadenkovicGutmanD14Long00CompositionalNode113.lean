/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode033
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .pow e033 2
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,196]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-3528,3528],[0,3528]],[[0,0,0],[0,0,0],[0,0]],[[15876,-31752,15876],[-31752,32928,9408],[15876,9408]],[[0,0,0],[0,0,0],[0,0]],[[-10584,-74088,84672],[-74088,234808,8624],[84672,8624]],[[0,0,0],[0,0,0],[0,0]],[[-587412,539784,190512],[539784,582512,3136],[190512,3136]],[[0,0,0],[0,0,0],[0,0]],[[-1617000,3382176,235200],[3382176,766752,392],[235200,392]],[[0,0,0],[0,0],[0]],[[3403540,8948968,173656],[8948968,596624],[173656]],[[0,0,0],[0,0],[0]],[[32293744,14313880,78400],[14313880,281848],[78400]],[[0,0,0],[0,0],[0]],[[100895704,15306032,21168],[15306032,79184],[21168]],[[0,0,0],[0,0],[0]],[[194003544,11389952,3136],[11389952,12152],[3136]],[[0,0,0],[0,0],[0]],[[261108064,5979176,196],[5979176,784],[196]],[[0,0],[0]],[[258922272,2205000],[2205000]],[[0,0],[0]],[[193740512,558600],[558600]],[[0,0],[0]],[[110475400,92512],[92512]],[[0,0],[0]],[[48027252,9016],[9016]],[[0,0],[0]],[[15790544,392],[392]],[[0]],[[3856888]],[[0]],[[677768]],[[0]],[[80948]],[[0]],[[5880]],[[0]],[[196]]]
theorem step113 : p113=NestedArithmetic.power p033 2 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_pow 2 e113 e033 p033 p113 rfl h033 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
