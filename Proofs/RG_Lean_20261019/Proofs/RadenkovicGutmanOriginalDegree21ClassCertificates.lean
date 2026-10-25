/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeFourToFortyfiveDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree21Class11
import Proofs.RadenkovicGutmanFixedDegree21Class12
import Proofs.RadenkovicGutmanFixedDegree21Class13
import Proofs.RadenkovicGutmanFixedDegree21Class14
import Proofs.RadenkovicGutmanFixedDegree21Class10
import Proofs.RadenkovicGutmanFixedDegree21Class22
import Proofs.RadenkovicGutmanFixedDegree21Class23
import Proofs.RadenkovicGutmanFixedDegree21Class24
import Proofs.RadenkovicGutmanFixedDegree21Class20
import Proofs.RadenkovicGutmanFixedDegree21Class33
import Proofs.RadenkovicGutmanFixedDegree21Class34
import Proofs.RadenkovicGutmanFixedDegree21Class30
import Proofs.RadenkovicGutmanFixedDegree21Class44
import Proofs.RadenkovicGutmanFixedDegree21Class40
import Proofs.RadenkovicGutmanD21UpperCompositionalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree21ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates 21 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree21Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree21Class11.reserve]
  · have hb := FixedDegree21Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree21Class12.reserve]
  · have hb := FixedDegree21Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree21Class13.reserve]
  · have hb := FixedDegree21Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree21Class14.reserve]
  · have hb := FixedDegree21Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree21Class10.reserve]
  · omega
  · have hb := FixedDegree21Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree21Class22.reserve]
  · have hb := FixedDegree21Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree21Class23.reserve]
  · have hb := FixedDegree21Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree21Class24.reserve]
  · have hb := FixedDegree21Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree21Class20.reserve]
  · omega
  · omega
  · have hb := FixedDegree21Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree21Class33.reserve]
  · have hb := FixedDegree21Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree21Class34.reserve]
  · have hb := FixedDegree21Class30.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree21Class30.reserve]
  · omega
  · omega
  · omega
  · have hb := FixedDegree21Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree21Class44.reserve]
  · have hb := FixedDegree21Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree21Class40.reserve]
  · omega
  · omega
  · omega
  · omega
  · have hb := D21UpperCompositionalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D21UpperCompositionalBothLong.reserve]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree21ClassCertificates
