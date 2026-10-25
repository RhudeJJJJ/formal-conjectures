/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeFourToFortyfiveDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree44Class11
import Proofs.RadenkovicGutmanFixedDegree44Class12
import Proofs.RadenkovicGutmanFixedDegree44Class13
import Proofs.RadenkovicGutmanFixedDegree44Class14
import Proofs.RadenkovicGutmanFixedDegree44Class10
import Proofs.RadenkovicGutmanFixedDegree44Class22
import Proofs.RadenkovicGutmanFixedDegree44Class23
import Proofs.RadenkovicGutmanFixedDegree44Class24
import Proofs.RadenkovicGutmanFixedDegree44Class20
import Proofs.RadenkovicGutmanFixedDegree44Class33
import Proofs.RadenkovicGutmanFixedDegree44Class34
import Proofs.RadenkovicGutmanFixedDegree44Class30
import Proofs.RadenkovicGutmanFixedDegree44Class44
import Proofs.RadenkovicGutmanFixedDegree44Class40
import Proofs.RadenkovicGutmanD44UpperCompositionalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree44ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates 44 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree44Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree44Class11.reserve]
  · have hb := FixedDegree44Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree44Class12.reserve]
  · have hb := FixedDegree44Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree44Class13.reserve]
  · have hb := FixedDegree44Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree44Class14.reserve]
  · have hb := FixedDegree44Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree44Class10.reserve]
  · omega
  · have hb := FixedDegree44Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree44Class22.reserve]
  · have hb := FixedDegree44Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree44Class23.reserve]
  · have hb := FixedDegree44Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree44Class24.reserve]
  · have hb := FixedDegree44Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree44Class20.reserve]
  · omega
  · omega
  · have hb := FixedDegree44Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree44Class33.reserve]
  · have hb := FixedDegree44Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree44Class34.reserve]
  · have hb := FixedDegree44Class30.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree44Class30.reserve]
  · omega
  · omega
  · omega
  · have hb := FixedDegree44Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree44Class44.reserve]
  · have hb := FixedDegree44Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree44Class40.reserve]
  · omega
  · omega
  · omega
  · omega
  · have hb := D44UpperCompositionalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D44UpperCompositionalBothLong.reserve]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree44ClassCertificates
