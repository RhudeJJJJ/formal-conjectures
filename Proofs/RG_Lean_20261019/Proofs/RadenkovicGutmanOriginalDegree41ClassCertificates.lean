/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeFourToFortyfiveDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree41Class11
import Proofs.RadenkovicGutmanFixedDegree41Class12
import Proofs.RadenkovicGutmanFixedDegree41Class13
import Proofs.RadenkovicGutmanFixedDegree41Class14
import Proofs.RadenkovicGutmanFixedDegree41Class10
import Proofs.RadenkovicGutmanFixedDegree41Class22
import Proofs.RadenkovicGutmanFixedDegree41Class23
import Proofs.RadenkovicGutmanFixedDegree41Class24
import Proofs.RadenkovicGutmanFixedDegree41Class20
import Proofs.RadenkovicGutmanFixedDegree41Class33
import Proofs.RadenkovicGutmanFixedDegree41Class34
import Proofs.RadenkovicGutmanFixedDegree41Class30
import Proofs.RadenkovicGutmanFixedDegree41Class44
import Proofs.RadenkovicGutmanFixedDegree41Class40
import Proofs.RadenkovicGutmanD41UpperCompositionalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree41ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates 41 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree41Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree41Class11.reserve]
  · have hb := FixedDegree41Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree41Class12.reserve]
  · have hb := FixedDegree41Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree41Class13.reserve]
  · have hb := FixedDegree41Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree41Class14.reserve]
  · have hb := FixedDegree41Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree41Class10.reserve]
  · omega
  · have hb := FixedDegree41Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree41Class22.reserve]
  · have hb := FixedDegree41Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree41Class23.reserve]
  · have hb := FixedDegree41Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree41Class24.reserve]
  · have hb := FixedDegree41Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree41Class20.reserve]
  · omega
  · omega
  · have hb := FixedDegree41Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree41Class33.reserve]
  · have hb := FixedDegree41Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree41Class34.reserve]
  · have hb := FixedDegree41Class30.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree41Class30.reserve]
  · omega
  · omega
  · omega
  · have hb := FixedDegree41Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree41Class44.reserve]
  · have hb := FixedDegree41Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree41Class40.reserve]
  · omega
  · omega
  · omega
  · omega
  · have hb := D41UpperCompositionalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D41UpperCompositionalBothLong.reserve]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree41ClassCertificates
