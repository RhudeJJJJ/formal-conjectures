/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerPolynomialPaymentCell
namespace Gebendorfer.RadenkovicGutman.WideAnchor251Source
open Set MeasureTheory
open scoped Classical
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def data : ComputedGeneralPathData.Data := ComputedGeneralPathData.build (13/7) 0 2
def source : IntegerPolynomialPaymentCell.Source := {den:=79792266297612001,length:=25,poly:=![[0,0,3213668883999974400,0,88090203902261227536,0,837910715416626780292,0,3647861308241247367088,0,8108743033921292717584,0,10365714360060860656520,0,8166389564162138270864,0,4088992292243403291376,0,1300928391996571326660,0,253896399190416958304,0,27617894620561215040,0,1276676260761792016],[0,0,3213668883999974400,0,30994978710705777040,0,108462611787811216516,0,186983896164597190064,0,176986139913637834640,0,95831428102803432200,0,29497549173577847600,0,4794049632248361856,0,319169065190448004,0,0,0,0,0,0],[0,0,0,0,92778692281967158336,0,1203455216704030863104,0,5695737067268338337856,0,12677250001776765656384,0,15715100545655446254928,0,11812537004769476088736,0,5583334753113061971376,0,1662298360536688299712,0,301133420838603262896,0,30171247142084799072,0,1276676260761792016],[0,0,2720849521988844344,0,17646403880929528208,0,26293295117471912684,0,15359595850658190180,0,3771405892760599884,0,319169065190448004,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,1674387861581047984,0,10532516644031784416,0,17003893432934762760,0,11093152224132813800,0,3133067762379703876,0,319169065190448004,0,0,0,0,0,0,0,0,0,0,0,0]]}
theorem source_checked : IntegerPolynomialPaymentCell.sourceChecks data source=true := by decide +kernel
theorem path_checked : GeneralPathPolynomials.accepts (13/7) 0 2 data.a data.b data.c data.e=true := ComputedGeneralPathData.path_checked (13/7) 0 2
theorem path_swapped : GeneralPathPolynomials.accepts (13/7) 2 0 data.a data.b data.c data.e=true := ComputedGeneralPathData.path_swapped (13/7) 0 2
theorem norms_checked : RationalMobiusPolynomials.accepts data.a data.b data.c data.e data.U data.V data.J data.N data.E=true := ComputedGeneralPathData.norms_checked (13/7) 0 2
#print axioms source_checked
#print axioms path_checked
#print axioms path_swapped
#print axioms norms_checked
end Gebendorfer.RadenkovicGutman.WideAnchor251Source
