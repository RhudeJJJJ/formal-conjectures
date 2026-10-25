/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeFourToFortyfiveDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree31Class11
import Proofs.RadenkovicGutmanFixedDegree31Class12
import Proofs.RadenkovicGutmanFixedDegree31Class13
import Proofs.RadenkovicGutmanFixedDegree31Class14
import Proofs.RadenkovicGutmanFixedDegree31Class10
import Proofs.RadenkovicGutmanFixedDegree31Class22
import Proofs.RadenkovicGutmanFixedDegree31Class23
import Proofs.RadenkovicGutmanFixedDegree31Class24
import Proofs.RadenkovicGutmanFixedDegree31Class20
import Proofs.RadenkovicGutmanFixedDegree31Class33
import Proofs.RadenkovicGutmanFixedDegree31Class34
import Proofs.RadenkovicGutmanFixedDegree31Class30
import Proofs.RadenkovicGutmanFixedDegree31Class44
import Proofs.RadenkovicGutmanFixedDegree31Class40
import Proofs.RadenkovicGutmanD31UpperCompositionalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree31ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates 31 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree31Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree31Class11.reserve]
  · have hb := FixedDegree31Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree31Class12.reserve]
  · have hb := FixedDegree31Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree31Class13.reserve]
  · have hb := FixedDegree31Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree31Class14.reserve]
  · have hb := FixedDegree31Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree31Class10.reserve]
  · omega
  · have hb := FixedDegree31Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree31Class22.reserve]
  · have hb := FixedDegree31Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree31Class23.reserve]
  · have hb := FixedDegree31Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree31Class24.reserve]
  · have hb := FixedDegree31Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree31Class20.reserve]
  · omega
  · omega
  · have hb := FixedDegree31Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree31Class33.reserve]
  · have hb := FixedDegree31Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree31Class34.reserve]
  · have hb := FixedDegree31Class30.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree31Class30.reserve]
  · omega
  · omega
  · omega
  · have hb := FixedDegree31Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree31Class44.reserve]
  · have hb := FixedDegree31Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree31Class40.reserve]
  · omega
  · omega
  · omega
  · omega
  · have hb := D31UpperCompositionalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D31UpperCompositionalBothLong.reserve]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree31ClassCertificates
