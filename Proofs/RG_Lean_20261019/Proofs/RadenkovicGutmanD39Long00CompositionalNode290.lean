/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode289
import Proofs.RadenkovicGutmanD39Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e290 : NestedArithmetic.Expr 3 := .times e289 e003
noncomputable def p290 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[6084,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[182520,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[2512692,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[21038472,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[119720952,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[490163544,6084,0],[6084,0],[0]],[[0,0,0],[0,0],[0]],[[1491084972,133848,0],[133848,0],[0]],[[0,0,0],[0,0],[0]],[[3432118248,1308060,0],[1308060,0],[0]],[[0,0,0],[0,0],[0]],[[6031203048,7483320,0],[7483320,0],[0]],[[0,0,0],[0,0],[0]],[[8105603688,27809964,0],[27809964,0],[0]],[[0,0,0],[0,0],[0]],[[8290612044,70452720,1521],[70452720,3042],[1521]],[[0,0,0],[0,0],[0]],[[6375679128,124271784,21294],[124271784,42588],[21294]],[[0,0,0],[0,0],[0]],[[3607653816,153195120,123201],[153195120,246402],[123201]],[[0,0,0],[0,0],[0]],[[1449172296,130507884,380250],[130507884,760500],[380250]],[[0,0,0],[0,0],[0]],[[388822356,74650680,675324],[74650680,1350648],[675324]],[[0,0,0],[0,0],[0]],[[62093304,27104220,696618],[27104220,1393236],[696618]],[[0,0,0],[0,0],[0]],[[4435236,5585112,403065],[5585112,806130],[403065]],[[0,0,0],[0,0],[0]],[[0,492804,118638],[492804,237276],[118638]],[[0,0,0],[0,0],[0]],[[0,0,13689],[0,27378],[13689]]]
theorem step290 : p290=NestedArithmetic.mul p289 p003 := by decide +kernel
#print axioms step290
theorem h290 : NestedArithmetic.compile e290=p290 := StagedExprCompile.compile_times e290 e289 e003 p289 p003 p290 rfl h289 h003 step290
#print axioms h290
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
