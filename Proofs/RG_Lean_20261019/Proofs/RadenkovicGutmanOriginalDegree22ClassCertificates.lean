/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeFourToFortyfiveDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree22Class11
import Proofs.RadenkovicGutmanFixedDegree22Class12
import Proofs.RadenkovicGutmanFixedDegree22Class13
import Proofs.RadenkovicGutmanFixedDegree22Class14
import Proofs.RadenkovicGutmanFixedDegree22Class10
import Proofs.RadenkovicGutmanFixedDegree22Class22
import Proofs.RadenkovicGutmanFixedDegree22Class23
import Proofs.RadenkovicGutmanFixedDegree22Class24
import Proofs.RadenkovicGutmanFixedDegree22Class20
import Proofs.RadenkovicGutmanFixedDegree22Class33
import Proofs.RadenkovicGutmanFixedDegree22Class34
import Proofs.RadenkovicGutmanFixedDegree22Class30
import Proofs.RadenkovicGutmanFixedDegree22Class44
import Proofs.RadenkovicGutmanFixedDegree22Class40
import Proofs.RadenkovicGutmanD22UpperCompositionalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree22ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates 22 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree22Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree22Class11.reserve]
  · have hb := FixedDegree22Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree22Class12.reserve]
  · have hb := FixedDegree22Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree22Class13.reserve]
  · have hb := FixedDegree22Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree22Class14.reserve]
  · have hb := FixedDegree22Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree22Class10.reserve]
  · omega
  · have hb := FixedDegree22Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree22Class22.reserve]
  · have hb := FixedDegree22Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree22Class23.reserve]
  · have hb := FixedDegree22Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree22Class24.reserve]
  · have hb := FixedDegree22Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree22Class20.reserve]
  · omega
  · omega
  · have hb := FixedDegree22Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree22Class33.reserve]
  · have hb := FixedDegree22Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree22Class34.reserve]
  · have hb := FixedDegree22Class30.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree22Class30.reserve]
  · omega
  · omega
  · omega
  · have hb := FixedDegree22Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree22Class44.reserve]
  · have hb := FixedDegree22Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree22Class40.reserve]
  · omega
  · omega
  · omega
  · omega
  · have hb := D22UpperCompositionalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D22UpperCompositionalBothLong.reserve]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree22ClassCertificates
