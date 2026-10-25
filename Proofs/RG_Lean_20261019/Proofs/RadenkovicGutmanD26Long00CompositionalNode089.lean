/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode033
import Proofs.RadenkovicGutmanD26Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e089 : NestedArithmetic.Expr 3 := .times e033 e061
noncomputable def p089 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,2028],[0,2028,-1248]],[[0,0,0],[0,0,0],[0,0]],[[0,-18252,18252],[-18252,66924,-13676],[18252,-13676]],[[0,0,0],[0,0,0],[0,0]],[[-172692,200772,26676],[200772,53976,-49088],[26676,-49088]],[[0,0,0],[0,0,0],[0,0]],[[18252,1003392,-186264],[1003392,-924196,-50180],[-186264,-50180]],[[0,0,0],[0,0,0],[0,0]],[[6306768,-1780948,-701324],[-1780948,-3114904,-19292],[-701324,-19292]],[[0,0,0],[0,0,0],[0,0]],[[19199388,-20528664,-1067664],[-20528664,-4570800,-2496],[-1067664,-2496]],[[0,0,0],[0,0],[0]],[[-30356300,-60829444,-890084],[-60829444,-3729336],[-890084]],[[0,0,0],[0,0],[0]],[[-333823672,-101118056,-435656],[-101118056,-1797380],[-435656]],[[0,0,0],[0,0],[0]],[[-1048858512,-109146908,-124644],[-109146908,-508040],[-124644]],[[0,0,0],[0,0],[0]],[[-1984773076,-80804724,-19292],[-80804724,-77844],[-19292]],[[0,0,0],[0,0],[0]],[[-2600061776,-41875704,-1248],[-41875704,-4992],[-1248]],[[0,0],[0]],[[-2491215792,-15183480],[-15183480]],[[0,0],[0]],[[-1791869664,-3774368],[-3774368]],[[0,0],[0]],[[-978711500,-612872],[-612872]],[[0,0],[0]],[[-406605420,-58552],[-58552]],[[0,0],[0]],[[-127577736,-2496],[-2496]],[[0]],[[-29716128]],[[0]],[[-4978428]],[[0]],[[-566852]],[[0]],[[-39260]],[[0]],[[-1248]]]
theorem step089 : p089=NestedArithmetic.mul p033 p061 := by decide +kernel
#print axioms step089
theorem h089 : NestedArithmetic.compile e089=p089 := StagedExprCompile.compile_times e089 e033 e061 p033 p061 p089 rfl h033 h061 step089
#print axioms h089
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
