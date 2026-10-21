/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanEscapeReserveAffineRow00
import Proofs.RadenkovicGutmanEscapeReserveAffineRow01
import Proofs.RadenkovicGutmanEscapeReserveAffineRow02
import Proofs.RadenkovicGutmanEscapeReserveAffineRow03
import Proofs.RadenkovicGutmanEscapeReserveAffineRow04
import Proofs.RadenkovicGutmanEscapeReserveAffineRow05
import Proofs.RadenkovicGutmanEscapeReserveAffineRow06
import Proofs.RadenkovicGutmanEscapeReserveAffineRow07
import Proofs.RadenkovicGutmanEscapeReserveAffineRow08
import Proofs.RadenkovicGutmanEscapeReserveAffineRow09
import Proofs.RadenkovicGutmanEscapeReserveAffineRow10
import Proofs.RadenkovicGutmanEscapeReserveAffineRow11
import Proofs.RadenkovicGutmanEscapeReserveAffineRow12
import Proofs.RadenkovicGutmanEscapeReserveAffineRow13
import Proofs.RadenkovicGutmanEscapeReserveAffineRow14
import Proofs.RadenkovicGutmanEscapeReserveAffineRow15
import Proofs.RadenkovicGutmanEscapeReserveAffineRow16
import Proofs.RadenkovicGutmanEscapeReserveAffineRow17
import Proofs.RadenkovicGutmanEscapeReserveAffineRow18
import Proofs.RadenkovicGutmanEscapeReserveAffineRow19
import Proofs.RadenkovicGutmanEscapeReserveAffineRow20
import Proofs.RadenkovicGutmanEscapeReserveAffineRow21
import Proofs.RadenkovicGutmanEscapeReserveAffineRow22
import Proofs.RadenkovicGutmanEscapeReserveAffineRow23
import Proofs.RadenkovicGutmanEscapeReserveAffineRow24
namespace Gebendorfer.RadenkovicGutman.EscapeReserveRawAffine
noncomputable section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
theorem evaluation (H U a b : ℝ) :
    NestedHorner.eval (NestedInteger.castPoly 4 EscapeReducedReserve.data) ![H,U,a,b] =
      NestedHorner.eval (NestedInteger.castPoly 4 EscapeReserveRawData.data)
        ![H/46,(653/2000)+(19347/2000)*U,a,b] := by
  change (NestedHorner.eval EscapeReserveAffineRow00.unit ![U,a,b]+H*(NestedHorner.eval EscapeReserveAffineRow01.unit ![U,a,b]+H*(NestedHorner.eval EscapeReserveAffineRow02.unit ![U,a,b]+H*(NestedHorner.eval EscapeReserveAffineRow03.unit ![U,a,b]+H*(NestedHorner.eval EscapeReserveAffineRow04.unit ![U,a,b]+H*(NestedHorner.eval EscapeReserveAffineRow05.unit ![U,a,b]+H*(NestedHorner.eval EscapeReserveAffineRow06.unit ![U,a,b]+H*(NestedHorner.eval EscapeReserveAffineRow07.unit ![U,a,b]+H*(NestedHorner.eval EscapeReserveAffineRow08.unit ![U,a,b]+H*(NestedHorner.eval EscapeReserveAffineRow09.unit ![U,a,b]+H*(NestedHorner.eval EscapeReserveAffineRow10.unit ![U,a,b]+H*(NestedHorner.eval EscapeReserveAffineRow11.unit ![U,a,b]+H*(NestedHorner.eval EscapeReserveAffineRow12.unit ![U,a,b]+H*(NestedHorner.eval EscapeReserveAffineRow13.unit ![U,a,b]+H*(NestedHorner.eval EscapeReserveAffineRow14.unit ![U,a,b]+H*(NestedHorner.eval EscapeReserveAffineRow15.unit ![U,a,b]+H*(NestedHorner.eval EscapeReserveAffineRow16.unit ![U,a,b]+H*(NestedHorner.eval EscapeReserveAffineRow17.unit ![U,a,b]+H*(NestedHorner.eval EscapeReserveAffineRow18.unit ![U,a,b]+H*(NestedHorner.eval EscapeReserveAffineRow19.unit ![U,a,b]+H*(NestedHorner.eval EscapeReserveAffineRow20.unit ![U,a,b]+H*(NestedHorner.eval EscapeReserveAffineRow21.unit ![U,a,b]+H*(NestedHorner.eval EscapeReserveAffineRow22.unit ![U,a,b]+H*(NestedHorner.eval EscapeReserveAffineRow23.unit ![U,a,b]+H*(NestedHorner.eval EscapeReserveAffineRow24.unit ![U,a,b]+H*(0 : ℝ)))))))))))))))))))))))))) = (NestedHorner.eval EscapeReserveAffineRow00.raw ![(653/2000)+(19347/2000)*U,a,b]+(H/46)*(NestedHorner.eval EscapeReserveAffineRow01.raw ![(653/2000)+(19347/2000)*U,a,b]+(H/46)*(NestedHorner.eval EscapeReserveAffineRow02.raw ![(653/2000)+(19347/2000)*U,a,b]+(H/46)*(NestedHorner.eval EscapeReserveAffineRow03.raw ![(653/2000)+(19347/2000)*U,a,b]+(H/46)*(NestedHorner.eval EscapeReserveAffineRow04.raw ![(653/2000)+(19347/2000)*U,a,b]+(H/46)*(NestedHorner.eval EscapeReserveAffineRow05.raw ![(653/2000)+(19347/2000)*U,a,b]+(H/46)*(NestedHorner.eval EscapeReserveAffineRow06.raw ![(653/2000)+(19347/2000)*U,a,b]+(H/46)*(NestedHorner.eval EscapeReserveAffineRow07.raw ![(653/2000)+(19347/2000)*U,a,b]+(H/46)*(NestedHorner.eval EscapeReserveAffineRow08.raw ![(653/2000)+(19347/2000)*U,a,b]+(H/46)*(NestedHorner.eval EscapeReserveAffineRow09.raw ![(653/2000)+(19347/2000)*U,a,b]+(H/46)*(NestedHorner.eval EscapeReserveAffineRow10.raw ![(653/2000)+(19347/2000)*U,a,b]+(H/46)*(NestedHorner.eval EscapeReserveAffineRow11.raw ![(653/2000)+(19347/2000)*U,a,b]+(H/46)*(NestedHorner.eval EscapeReserveAffineRow12.raw ![(653/2000)+(19347/2000)*U,a,b]+(H/46)*(NestedHorner.eval EscapeReserveAffineRow13.raw ![(653/2000)+(19347/2000)*U,a,b]+(H/46)*(NestedHorner.eval EscapeReserveAffineRow14.raw ![(653/2000)+(19347/2000)*U,a,b]+(H/46)*(NestedHorner.eval EscapeReserveAffineRow15.raw ![(653/2000)+(19347/2000)*U,a,b]+(H/46)*(NestedHorner.eval EscapeReserveAffineRow16.raw ![(653/2000)+(19347/2000)*U,a,b]+(H/46)*(NestedHorner.eval EscapeReserveAffineRow17.raw ![(653/2000)+(19347/2000)*U,a,b]+(H/46)*(NestedHorner.eval EscapeReserveAffineRow18.raw ![(653/2000)+(19347/2000)*U,a,b]+(H/46)*(NestedHorner.eval EscapeReserveAffineRow19.raw ![(653/2000)+(19347/2000)*U,a,b]+(H/46)*(NestedHorner.eval EscapeReserveAffineRow20.raw ![(653/2000)+(19347/2000)*U,a,b]+(H/46)*(NestedHorner.eval EscapeReserveAffineRow21.raw ![(653/2000)+(19347/2000)*U,a,b]+(H/46)*(NestedHorner.eval EscapeReserveAffineRow22.raw ![(653/2000)+(19347/2000)*U,a,b]+(H/46)*(NestedHorner.eval EscapeReserveAffineRow23.raw ![(653/2000)+(19347/2000)*U,a,b]+(H/46)*(NestedHorner.eval EscapeReserveAffineRow24.raw ![(653/2000)+(19347/2000)*U,a,b]+(H/46)*(0 : ℝ))))))))))))))))))))))))))
  rw [EscapeReserveAffineRow00.evaluation,EscapeReserveAffineRow01.evaluation,EscapeReserveAffineRow02.evaluation,EscapeReserveAffineRow03.evaluation,EscapeReserveAffineRow04.evaluation,EscapeReserveAffineRow05.evaluation,EscapeReserveAffineRow06.evaluation,EscapeReserveAffineRow07.evaluation,EscapeReserveAffineRow08.evaluation,EscapeReserveAffineRow09.evaluation,EscapeReserveAffineRow10.evaluation,EscapeReserveAffineRow11.evaluation,EscapeReserveAffineRow12.evaluation,EscapeReserveAffineRow13.evaluation,EscapeReserveAffineRow14.evaluation,EscapeReserveAffineRow15.evaluation,EscapeReserveAffineRow16.evaluation,EscapeReserveAffineRow17.evaluation,EscapeReserveAffineRow18.evaluation,EscapeReserveAffineRow19.evaluation,EscapeReserveAffineRow20.evaluation,EscapeReserveAffineRow21.evaluation,EscapeReserveAffineRow22.evaluation,EscapeReserveAffineRow23.evaluation,EscapeReserveAffineRow24.evaluation]
  ring
#print axioms evaluation
end
end Gebendorfer.RadenkovicGutman.EscapeReserveRawAffine
