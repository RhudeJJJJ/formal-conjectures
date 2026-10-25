/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeFourToFortyfiveDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree30Class11
import Proofs.RadenkovicGutmanFixedDegree30Class12
import Proofs.RadenkovicGutmanFixedDegree30Class13
import Proofs.RadenkovicGutmanFixedDegree30Class14
import Proofs.RadenkovicGutmanFixedDegree30Class10
import Proofs.RadenkovicGutmanFixedDegree30Class22
import Proofs.RadenkovicGutmanFixedDegree30Class23
import Proofs.RadenkovicGutmanFixedDegree30Class24
import Proofs.RadenkovicGutmanFixedDegree30Class20
import Proofs.RadenkovicGutmanFixedDegree30Class33
import Proofs.RadenkovicGutmanFixedDegree30Class34
import Proofs.RadenkovicGutmanFixedDegree30Class30
import Proofs.RadenkovicGutmanFixedDegree30Class44
import Proofs.RadenkovicGutmanFixedDegree30Class40
import Proofs.RadenkovicGutmanD30UpperCompositionalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree30ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates 30 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree30Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree30Class11.reserve]
  · have hb := FixedDegree30Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree30Class12.reserve]
  · have hb := FixedDegree30Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree30Class13.reserve]
  · have hb := FixedDegree30Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree30Class14.reserve]
  · have hb := FixedDegree30Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree30Class10.reserve]
  · omega
  · have hb := FixedDegree30Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree30Class22.reserve]
  · have hb := FixedDegree30Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree30Class23.reserve]
  · have hb := FixedDegree30Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree30Class24.reserve]
  · have hb := FixedDegree30Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree30Class20.reserve]
  · omega
  · omega
  · have hb := FixedDegree30Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree30Class33.reserve]
  · have hb := FixedDegree30Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree30Class34.reserve]
  · have hb := FixedDegree30Class30.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree30Class30.reserve]
  · omega
  · omega
  · omega
  · have hb := FixedDegree30Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree30Class44.reserve]
  · have hb := FixedDegree30Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree30Class40.reserve]
  · omega
  · omega
  · omega
  · omega
  · have hb := D30UpperCompositionalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D30UpperCompositionalBothLong.reserve]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree30ClassCertificates
