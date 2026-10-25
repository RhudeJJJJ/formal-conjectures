/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeFourToFortyfiveDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree15Class11
import Proofs.RadenkovicGutmanFixedDegree15Class12
import Proofs.RadenkovicGutmanFixedDegree15Class13
import Proofs.RadenkovicGutmanFixedDegree15Class14
import Proofs.RadenkovicGutmanFixedDegree15Class10
import Proofs.RadenkovicGutmanFixedDegree15Class22
import Proofs.RadenkovicGutmanFixedDegree15Class23
import Proofs.RadenkovicGutmanFixedDegree15Class24
import Proofs.RadenkovicGutmanFixedDegree15Class20
import Proofs.RadenkovicGutmanFixedDegree15Class33
import Proofs.RadenkovicGutmanFixedDegree15Class34
import Proofs.RadenkovicGutmanFixedDegree15Class30
import Proofs.RadenkovicGutmanFixedDegree15Class44
import Proofs.RadenkovicGutmanFixedDegree15Class40
import Proofs.RadenkovicGutmanD15UpperCompositionalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree15ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates 15 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree15Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree15Class11.reserve]
  · have hb := FixedDegree15Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree15Class12.reserve]
  · have hb := FixedDegree15Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree15Class13.reserve]
  · have hb := FixedDegree15Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree15Class14.reserve]
  · have hb := FixedDegree15Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree15Class10.reserve]
  · omega
  · have hb := FixedDegree15Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree15Class22.reserve]
  · have hb := FixedDegree15Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree15Class23.reserve]
  · have hb := FixedDegree15Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree15Class24.reserve]
  · have hb := FixedDegree15Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree15Class20.reserve]
  · omega
  · omega
  · have hb := FixedDegree15Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree15Class33.reserve]
  · have hb := FixedDegree15Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree15Class34.reserve]
  · have hb := FixedDegree15Class30.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree15Class30.reserve]
  · omega
  · omega
  · omega
  · have hb := FixedDegree15Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree15Class44.reserve]
  · have hb := FixedDegree15Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree15Class40.reserve]
  · omega
  · omega
  · omega
  · omega
  · have hb := D15UpperCompositionalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D15UpperCompositionalBothLong.reserve]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree15ClassCertificates
