/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeFourToFortyfiveDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree25Class11
import Proofs.RadenkovicGutmanFixedDegree25Class12
import Proofs.RadenkovicGutmanFixedDegree25Class13
import Proofs.RadenkovicGutmanFixedDegree25Class14
import Proofs.RadenkovicGutmanFixedDegree25Class10
import Proofs.RadenkovicGutmanFixedDegree25Class22
import Proofs.RadenkovicGutmanFixedDegree25Class23
import Proofs.RadenkovicGutmanFixedDegree25Class24
import Proofs.RadenkovicGutmanFixedDegree25Class20
import Proofs.RadenkovicGutmanFixedDegree25Class33
import Proofs.RadenkovicGutmanFixedDegree25Class34
import Proofs.RadenkovicGutmanFixedDegree25Class30
import Proofs.RadenkovicGutmanFixedDegree25Class44
import Proofs.RadenkovicGutmanFixedDegree25Class40
import Proofs.RadenkovicGutmanD25UpperCompositionalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree25ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates 25 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree25Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree25Class11.reserve]
  · have hb := FixedDegree25Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree25Class12.reserve]
  · have hb := FixedDegree25Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree25Class13.reserve]
  · have hb := FixedDegree25Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree25Class14.reserve]
  · have hb := FixedDegree25Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree25Class10.reserve]
  · omega
  · have hb := FixedDegree25Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree25Class22.reserve]
  · have hb := FixedDegree25Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree25Class23.reserve]
  · have hb := FixedDegree25Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree25Class24.reserve]
  · have hb := FixedDegree25Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree25Class20.reserve]
  · omega
  · omega
  · have hb := FixedDegree25Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree25Class33.reserve]
  · have hb := FixedDegree25Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree25Class34.reserve]
  · have hb := FixedDegree25Class30.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree25Class30.reserve]
  · omega
  · omega
  · omega
  · have hb := FixedDegree25Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree25Class44.reserve]
  · have hb := FixedDegree25Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree25Class40.reserve]
  · omega
  · omega
  · omega
  · omega
  · have hb := D25UpperCompositionalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D25UpperCompositionalBothLong.reserve]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree25ClassCertificates
