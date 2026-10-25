/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeFourToFortyfiveDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree17Class11
import Proofs.RadenkovicGutmanFixedDegree17Class12
import Proofs.RadenkovicGutmanFixedDegree17Class13
import Proofs.RadenkovicGutmanFixedDegree17Class14
import Proofs.RadenkovicGutmanFixedDegree17Class10
import Proofs.RadenkovicGutmanFixedDegree17Class22
import Proofs.RadenkovicGutmanFixedDegree17Class23
import Proofs.RadenkovicGutmanFixedDegree17Class24
import Proofs.RadenkovicGutmanFixedDegree17Class20
import Proofs.RadenkovicGutmanFixedDegree17Class33
import Proofs.RadenkovicGutmanFixedDegree17Class34
import Proofs.RadenkovicGutmanFixedDegree17Class30
import Proofs.RadenkovicGutmanFixedDegree17Class44
import Proofs.RadenkovicGutmanFixedDegree17Class40
import Proofs.RadenkovicGutmanD17UpperCompositionalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree17ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates 17 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree17Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree17Class11.reserve]
  · have hb := FixedDegree17Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree17Class12.reserve]
  · have hb := FixedDegree17Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree17Class13.reserve]
  · have hb := FixedDegree17Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree17Class14.reserve]
  · have hb := FixedDegree17Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree17Class10.reserve]
  · omega
  · have hb := FixedDegree17Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree17Class22.reserve]
  · have hb := FixedDegree17Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree17Class23.reserve]
  · have hb := FixedDegree17Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree17Class24.reserve]
  · have hb := FixedDegree17Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree17Class20.reserve]
  · omega
  · omega
  · have hb := FixedDegree17Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree17Class33.reserve]
  · have hb := FixedDegree17Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree17Class34.reserve]
  · have hb := FixedDegree17Class30.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree17Class30.reserve]
  · omega
  · omega
  · omega
  · have hb := FixedDegree17Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree17Class44.reserve]
  · have hb := FixedDegree17Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree17Class40.reserve]
  · omega
  · omega
  · omega
  · omega
  · have hb := D17UpperCompositionalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D17UpperCompositionalBothLong.reserve]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree17ClassCertificates
