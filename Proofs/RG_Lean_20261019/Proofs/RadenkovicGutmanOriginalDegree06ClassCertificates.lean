/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeFourToFortyfiveDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree06Class11
import Proofs.RadenkovicGutmanFixedDegree06Class12
import Proofs.RadenkovicGutmanFixedDegree06Class13
import Proofs.RadenkovicGutmanFixedDegree06Class14
import Proofs.RadenkovicGutmanFixedDegree06Class10
import Proofs.RadenkovicGutmanFixedDegree06Class22
import Proofs.RadenkovicGutmanFixedDegree06Class23
import Proofs.RadenkovicGutmanFixedDegree06Class24
import Proofs.RadenkovicGutmanFixedDegree06Class20
import Proofs.RadenkovicGutmanFixedDegree06Class33
import Proofs.RadenkovicGutmanFixedDegree06Class34
import Proofs.RadenkovicGutmanFixedDegree06Class30
import Proofs.RadenkovicGutmanFixedDegree06Class44
import Proofs.RadenkovicGutmanFixedDegree06Class40
import Proofs.RadenkovicGutmanD6UpperCompositionalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree06ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates 6 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree06Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree06Class11.reserve]
  · have hb := FixedDegree06Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree06Class12.reserve]
  · have hb := FixedDegree06Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree06Class13.reserve]
  · have hb := FixedDegree06Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree06Class14.reserve]
  · have hb := FixedDegree06Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree06Class10.reserve]
  · omega
  · have hb := FixedDegree06Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree06Class22.reserve]
  · have hb := FixedDegree06Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree06Class23.reserve]
  · have hb := FixedDegree06Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree06Class24.reserve]
  · have hb := FixedDegree06Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree06Class20.reserve]
  · omega
  · omega
  · have hb := FixedDegree06Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree06Class33.reserve]
  · have hb := FixedDegree06Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree06Class34.reserve]
  · have hb := FixedDegree06Class30.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree06Class30.reserve]
  · omega
  · omega
  · omega
  · have hb := FixedDegree06Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree06Class44.reserve]
  · have hb := FixedDegree06Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree06Class40.reserve]
  · omega
  · omega
  · omega
  · omega
  · have hb := D6UpperCompositionalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D6UpperCompositionalBothLong.reserve]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree06ClassCertificates
