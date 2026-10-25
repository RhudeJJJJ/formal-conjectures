/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeFourToFortyfiveDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree23Class11
import Proofs.RadenkovicGutmanFixedDegree23Class12
import Proofs.RadenkovicGutmanFixedDegree23Class13
import Proofs.RadenkovicGutmanFixedDegree23Class14
import Proofs.RadenkovicGutmanFixedDegree23Class10
import Proofs.RadenkovicGutmanFixedDegree23Class22
import Proofs.RadenkovicGutmanFixedDegree23Class23
import Proofs.RadenkovicGutmanFixedDegree23Class24
import Proofs.RadenkovicGutmanFixedDegree23Class20
import Proofs.RadenkovicGutmanFixedDegree23Class33
import Proofs.RadenkovicGutmanFixedDegree23Class34
import Proofs.RadenkovicGutmanFixedDegree23Class30
import Proofs.RadenkovicGutmanFixedDegree23Class44
import Proofs.RadenkovicGutmanFixedDegree23Class40
import Proofs.RadenkovicGutmanD23UpperCompositionalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree23ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates 23 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree23Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree23Class11.reserve]
  · have hb := FixedDegree23Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree23Class12.reserve]
  · have hb := FixedDegree23Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree23Class13.reserve]
  · have hb := FixedDegree23Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree23Class14.reserve]
  · have hb := FixedDegree23Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree23Class10.reserve]
  · omega
  · have hb := FixedDegree23Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree23Class22.reserve]
  · have hb := FixedDegree23Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree23Class23.reserve]
  · have hb := FixedDegree23Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree23Class24.reserve]
  · have hb := FixedDegree23Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree23Class20.reserve]
  · omega
  · omega
  · have hb := FixedDegree23Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree23Class33.reserve]
  · have hb := FixedDegree23Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree23Class34.reserve]
  · have hb := FixedDegree23Class30.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree23Class30.reserve]
  · omega
  · omega
  · omega
  · have hb := FixedDegree23Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree23Class44.reserve]
  · have hb := FixedDegree23Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree23Class40.reserve]
  · omega
  · omega
  · omega
  · omega
  · have hb := D23UpperCompositionalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D23UpperCompositionalBothLong.reserve]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree23ClassCertificates
