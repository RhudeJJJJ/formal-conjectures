/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeFourToFortyfiveDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree08Class11
import Proofs.RadenkovicGutmanFixedDegree08Class12
import Proofs.RadenkovicGutmanFixedDegree08Class13
import Proofs.RadenkovicGutmanFixedDegree08Class14
import Proofs.RadenkovicGutmanFixedDegree08Class10
import Proofs.RadenkovicGutmanFixedDegree08Class22
import Proofs.RadenkovicGutmanFixedDegree08Class23
import Proofs.RadenkovicGutmanFixedDegree08Class24
import Proofs.RadenkovicGutmanFixedDegree08Class20
import Proofs.RadenkovicGutmanFixedDegree08Class33
import Proofs.RadenkovicGutmanFixedDegree08Class34
import Proofs.RadenkovicGutmanFixedDegree08Class30
import Proofs.RadenkovicGutmanFixedDegree08Class44
import Proofs.RadenkovicGutmanFixedDegree08Class40
import Proofs.RadenkovicGutmanD8UpperCompositionalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree08ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates 8 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree08Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree08Class11.reserve]
  · have hb := FixedDegree08Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree08Class12.reserve]
  · have hb := FixedDegree08Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree08Class13.reserve]
  · have hb := FixedDegree08Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree08Class14.reserve]
  · have hb := FixedDegree08Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree08Class10.reserve]
  · omega
  · have hb := FixedDegree08Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree08Class22.reserve]
  · have hb := FixedDegree08Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree08Class23.reserve]
  · have hb := FixedDegree08Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree08Class24.reserve]
  · have hb := FixedDegree08Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree08Class20.reserve]
  · omega
  · omega
  · have hb := FixedDegree08Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree08Class33.reserve]
  · have hb := FixedDegree08Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree08Class34.reserve]
  · have hb := FixedDegree08Class30.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree08Class30.reserve]
  · omega
  · omega
  · omega
  · have hb := FixedDegree08Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree08Class44.reserve]
  · have hb := FixedDegree08Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree08Class40.reserve]
  · omega
  · omega
  · omega
  · omega
  · have hb := D8UpperCompositionalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D8UpperCompositionalBothLong.reserve]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree08ClassCertificates
