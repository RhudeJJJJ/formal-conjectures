/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode033
import Proofs.RadenkovicGutmanD14Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e075 : NestedArithmetic.Expr 3 := .times e033 e053
noncomputable def p075 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,196]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,3528],[0,3528]],[[0,0,0],[0,0,0],[0,0]],[[-15876,0,15876],[0,63504,9408],[15876,9408]],[[0,0,0],[0,0,0],[0,0]],[[-275184,285768,84672],[285768,338688,8624],[84672,8624]],[[0,0,0],[0,0,0],[0,0]],[[-841428,2286144,190512],[2286144,762048,3136],[190512,3136]],[[0,0,0],[0,0,0],[0,0]],[[3998400,8192016,235200],[8192016,940800,392],[235200,392]],[[0,0,0],[0,0],[0]],[[38106908,17357760,173656],[17357760,694624],[173656]],[[0,0,0],[0,0],[0]],[[140669984,24184440,78400],[24184440,313600],[78400]],[[0,0,0],[0,0],[0]],[[321356504,23313024,21168],[23313024,84672],[21168]],[[0,0,0],[0,0],[0]],[[511758352,15929312,3136],[15929312,12544],[3136]],[[0,0,0],[0,0],[0]],[[598625552,7771008,196],[7771008,784],[196]],[[0,0],[0]],[[528441872,2687160],[2687160]],[[0,0],[0]],[[356945792,642880],[642880]],[[0,0],[0]],[[185439520,101136],[101136]],[[0,0],[0]],[[73945116,9408],[9408]],[[0,0],[0]],[[22419264,392],[392]],[[0]],[[5072088]],[[0]],[[828688]],[[0]],[[92316]],[[0]],[[6272]],[[0]],[[196]]]
theorem step075 : p075=NestedArithmetic.mul p033 p053 := by decide +kernel
#print axioms step075
theorem h075 : NestedArithmetic.compile e075=p075 := StagedExprCompile.compile_times e075 e033 e053 p033 p053 p075 rfl h033 h053 step075
#print axioms h075
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
