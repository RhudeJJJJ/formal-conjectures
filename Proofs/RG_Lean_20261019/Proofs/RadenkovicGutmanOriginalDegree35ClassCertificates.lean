/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeFourToFortyfiveDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree35Class11
import Proofs.RadenkovicGutmanFixedDegree35Class12
import Proofs.RadenkovicGutmanFixedDegree35Class13
import Proofs.RadenkovicGutmanFixedDegree35Class14
import Proofs.RadenkovicGutmanFixedDegree35Class10
import Proofs.RadenkovicGutmanFixedDegree35Class22
import Proofs.RadenkovicGutmanFixedDegree35Class23
import Proofs.RadenkovicGutmanFixedDegree35Class24
import Proofs.RadenkovicGutmanFixedDegree35Class20
import Proofs.RadenkovicGutmanFixedDegree35Class33
import Proofs.RadenkovicGutmanFixedDegree35Class34
import Proofs.RadenkovicGutmanFixedDegree35Class30
import Proofs.RadenkovicGutmanFixedDegree35Class44
import Proofs.RadenkovicGutmanFixedDegree35Class40
import Proofs.RadenkovicGutmanD35UpperCompositionalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree35ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates 35 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree35Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree35Class11.reserve]
  · have hb := FixedDegree35Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree35Class12.reserve]
  · have hb := FixedDegree35Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree35Class13.reserve]
  · have hb := FixedDegree35Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree35Class14.reserve]
  · have hb := FixedDegree35Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree35Class10.reserve]
  · omega
  · have hb := FixedDegree35Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree35Class22.reserve]
  · have hb := FixedDegree35Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree35Class23.reserve]
  · have hb := FixedDegree35Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree35Class24.reserve]
  · have hb := FixedDegree35Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree35Class20.reserve]
  · omega
  · omega
  · have hb := FixedDegree35Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree35Class33.reserve]
  · have hb := FixedDegree35Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree35Class34.reserve]
  · have hb := FixedDegree35Class30.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree35Class30.reserve]
  · omega
  · omega
  · omega
  · have hb := FixedDegree35Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree35Class44.reserve]
  · have hb := FixedDegree35Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree35Class40.reserve]
  · omega
  · omega
  · omega
  · omega
  · have hb := D35UpperCompositionalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D35UpperCompositionalBothLong.reserve]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree35ClassCertificates
