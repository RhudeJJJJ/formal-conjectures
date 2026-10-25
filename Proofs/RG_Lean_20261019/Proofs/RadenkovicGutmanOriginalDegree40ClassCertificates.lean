/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeFourToFortyfiveDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree40Class11
import Proofs.RadenkovicGutmanFixedDegree40Class12
import Proofs.RadenkovicGutmanFixedDegree40Class13
import Proofs.RadenkovicGutmanFixedDegree40Class14
import Proofs.RadenkovicGutmanFixedDegree40Class10
import Proofs.RadenkovicGutmanFixedDegree40Class22
import Proofs.RadenkovicGutmanFixedDegree40Class23
import Proofs.RadenkovicGutmanFixedDegree40Class24
import Proofs.RadenkovicGutmanFixedDegree40Class20
import Proofs.RadenkovicGutmanFixedDegree40Class33
import Proofs.RadenkovicGutmanFixedDegree40Class34
import Proofs.RadenkovicGutmanFixedDegree40Class30
import Proofs.RadenkovicGutmanFixedDegree40Class44
import Proofs.RadenkovicGutmanFixedDegree40Class40
import Proofs.RadenkovicGutmanD40UpperCompositionalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree40ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates 40 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree40Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree40Class11.reserve]
  · have hb := FixedDegree40Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree40Class12.reserve]
  · have hb := FixedDegree40Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree40Class13.reserve]
  · have hb := FixedDegree40Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree40Class14.reserve]
  · have hb := FixedDegree40Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree40Class10.reserve]
  · omega
  · have hb := FixedDegree40Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree40Class22.reserve]
  · have hb := FixedDegree40Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree40Class23.reserve]
  · have hb := FixedDegree40Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree40Class24.reserve]
  · have hb := FixedDegree40Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree40Class20.reserve]
  · omega
  · omega
  · have hb := FixedDegree40Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree40Class33.reserve]
  · have hb := FixedDegree40Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree40Class34.reserve]
  · have hb := FixedDegree40Class30.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree40Class30.reserve]
  · omega
  · omega
  · omega
  · have hb := FixedDegree40Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree40Class44.reserve]
  · have hb := FixedDegree40Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree40Class40.reserve]
  · omega
  · omega
  · omega
  · omega
  · have hb := D40UpperCompositionalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D40UpperCompositionalBothLong.reserve]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree40ClassCertificates
