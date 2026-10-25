/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeFourToFortyfiveDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree29Class11
import Proofs.RadenkovicGutmanFixedDegree29Class12
import Proofs.RadenkovicGutmanFixedDegree29Class13
import Proofs.RadenkovicGutmanFixedDegree29Class14
import Proofs.RadenkovicGutmanFixedDegree29Class10
import Proofs.RadenkovicGutmanFixedDegree29Class22
import Proofs.RadenkovicGutmanFixedDegree29Class23
import Proofs.RadenkovicGutmanFixedDegree29Class24
import Proofs.RadenkovicGutmanFixedDegree29Class20
import Proofs.RadenkovicGutmanFixedDegree29Class33
import Proofs.RadenkovicGutmanFixedDegree29Class34
import Proofs.RadenkovicGutmanFixedDegree29Class30
import Proofs.RadenkovicGutmanFixedDegree29Class44
import Proofs.RadenkovicGutmanFixedDegree29Class40
import Proofs.RadenkovicGutmanD29UpperCompositionalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree29ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates 29 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree29Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree29Class11.reserve]
  · have hb := FixedDegree29Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree29Class12.reserve]
  · have hb := FixedDegree29Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree29Class13.reserve]
  · have hb := FixedDegree29Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree29Class14.reserve]
  · have hb := FixedDegree29Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree29Class10.reserve]
  · omega
  · have hb := FixedDegree29Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree29Class22.reserve]
  · have hb := FixedDegree29Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree29Class23.reserve]
  · have hb := FixedDegree29Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree29Class24.reserve]
  · have hb := FixedDegree29Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree29Class20.reserve]
  · omega
  · omega
  · have hb := FixedDegree29Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree29Class33.reserve]
  · have hb := FixedDegree29Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree29Class34.reserve]
  · have hb := FixedDegree29Class30.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree29Class30.reserve]
  · omega
  · omega
  · omega
  · have hb := FixedDegree29Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree29Class44.reserve]
  · have hb := FixedDegree29Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree29Class40.reserve]
  · omega
  · omega
  · omega
  · omega
  · have hb := D29UpperCompositionalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D29UpperCompositionalBothLong.reserve]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree29ClassCertificates
