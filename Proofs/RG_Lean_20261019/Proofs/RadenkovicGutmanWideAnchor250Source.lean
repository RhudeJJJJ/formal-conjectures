/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerPolynomialPaymentCell
namespace Gebendorfer.RadenkovicGutman.WideAnchor250Source
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (15/8) 0 2
def source : IntegerPolynomialPaymentCell.Source := {den:=72057594037927936,length:=25,poly:=![[0,0,3137532030864000000,0,85665932454972710241,0,799887356136923863680,0,3418305215825620684800,0,7517182636254432329728,0,9544288030048305283072,0,7481127197657217892352,0,3729967137259882807296,0,1182341233988272652288,0,230047528140782174208,0,24967956334142029824,0,1152921504606846976],[0,0,3137532030864000000,0,29392334411857920000,0,101582463272642150400,0,173861279135055216640,0,163701076876555452416,0,88184694032471949312,0,26992042891668357120,0,4359484439294640128,0,288230376151711744,0,0,0,0,0,0],[0,0,0,0,96847939839947037921,0,1195259034588991404672,0,5451580112496626421760,0,11906990923171669999616,0,14595006370084366057472,0,10882232369265237819392,0,5110068749235388416000,0,1513150892816958750720,0,272957825390368260096,0,27273799343355723776,0,1152921504606846976],[0,0,2641709585173315584,0,16301468330957471744,0,24054475476715962368,0,13957358932662943744,0,3409224917919465472,0,288230376151711744,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,1534968153048612864,0,9575592976130768896,0,15432333990115147776,0,10048234456105353216,0,2832764165616041984,0,288230376151711744,0,0,0,0,0,0,0,0,0,0,0,0]]}
theorem source_checked : IntegerPolynomialPaymentCell.sourceChecks data source=true := by decide +kernel
theorem path_checked : GeneralPathPolynomials.accepts (15/8) 0 2 data.a data.b data.c data.e=true := ComputedGeneralPathData.path_checked (15/8) 0 2
theorem path_swapped : GeneralPathPolynomials.accepts (15/8) 2 0 data.a data.b data.c data.e=true := ComputedGeneralPathData.path_swapped (15/8) 0 2
theorem norms_checked : RationalMobiusPolynomials.accepts data.a data.b data.c data.e data.U data.V data.J data.N data.E=true := ComputedGeneralPathData.norms_checked (15/8) 0 2
#print axioms source_checked
#print axioms path_checked
#print axioms path_swapped
#print axioms norms_checked
end Gebendorfer.RadenkovicGutman.WideAnchor250Source
