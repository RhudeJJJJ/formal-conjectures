/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode033
import Proofs.RadenkovicGutmanD19Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e089 : NestedArithmetic.Expr 3 := .times e033 e061
noncomputable def p089 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,1083],[0,1083,-646]],[[0,0,0],[0,0,0],[0,0]],[[0,-9747,9747],[-9747,35739,-6935],[9747,-6935]],[[0,0,0],[0,0,0],[0,0]],[[-93879,107217,15903],[107217,35454,-25232],[15903,-25232]],[[0,0,0],[0,0,0],[0,0]],[[-18981,565668,-90630],[565668,-458185,-25897],[-90630,-25897]],[[0,0,0],[0,0,0],[0,0]],[[3280122,-712405,-354635],[-712405,-1583878,-9975],[-354635,-9975]],[[0,0,0],[0,0,0],[0,0]],[[10670343,-10107582,-545604],[-10107582,-2342700,-1292],[-545604,-1292]],[[0,0,0],[0,0],[0]],[[-12232789,-30672289,-457197],[-30672289,-1919038],[-457197]],[[0,0,0],[0,0],[0]],[[-163584414,-51474686,-224466],[-51474686,-927105],[-224466]],[[0,0,0],[0,0],[0]],[[-526567064,-55853255,-64353],[-55853255,-262466],[-64353]],[[0,0,0],[0,0],[0]],[[-1006490477,-41488685,-9975],[-41488685,-40261],[-9975]],[[0,0,0],[0,0],[0]],[[-1326000652,-21551358,-646],[-21551358,-2584],[-646]],[[0,0],[0]],[[-1275201188,-7827810],[-7827810]],[[0,0],[0]],[[-919637240,-1948488],[-1948488]],[[0,0],[0]],[[-503296035,-316730],[-316730]],[[0,0],[0]],[[-209417373,-30286],[-30286]],[[0,0],[0]],[[-65789058,-1292],[-1292]],[[0]],[[-15339612]],[[0]],[[-2572087]],[[0]],[[-293075]],[[0]],[[-20311]],[[0]],[[-646]]]
theorem step089 : p089=NestedArithmetic.mul p033 p061 := by decide +kernel
#print axioms step089
theorem h089 : NestedArithmetic.compile e089=p089 := StagedExprCompile.compile_times e089 e033 e061 p033 p061 p089 rfl h033 h061 step089
#print axioms h089
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
