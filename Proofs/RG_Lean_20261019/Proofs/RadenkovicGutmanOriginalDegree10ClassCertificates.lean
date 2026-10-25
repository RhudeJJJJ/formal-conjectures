/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeFourToFortyfiveDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree10Class11
import Proofs.RadenkovicGutmanFixedDegree10Class12
import Proofs.RadenkovicGutmanFixedDegree10Class13
import Proofs.RadenkovicGutmanFixedDegree10Class14
import Proofs.RadenkovicGutmanFixedDegree10Class10
import Proofs.RadenkovicGutmanFixedDegree10Class22
import Proofs.RadenkovicGutmanFixedDegree10Class23
import Proofs.RadenkovicGutmanFixedDegree10Class24
import Proofs.RadenkovicGutmanFixedDegree10Class20
import Proofs.RadenkovicGutmanFixedDegree10Class33
import Proofs.RadenkovicGutmanFixedDegree10Class34
import Proofs.RadenkovicGutmanFixedDegree10Class30
import Proofs.RadenkovicGutmanFixedDegree10Class44
import Proofs.RadenkovicGutmanFixedDegree10Class40
import Proofs.RadenkovicGutmanD10UpperCompositionalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree10ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates 10 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree10Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree10Class11.reserve]
  · have hb := FixedDegree10Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree10Class12.reserve]
  · have hb := FixedDegree10Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree10Class13.reserve]
  · have hb := FixedDegree10Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree10Class14.reserve]
  · have hb := FixedDegree10Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree10Class10.reserve]
  · omega
  · have hb := FixedDegree10Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree10Class22.reserve]
  · have hb := FixedDegree10Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree10Class23.reserve]
  · have hb := FixedDegree10Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree10Class24.reserve]
  · have hb := FixedDegree10Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree10Class20.reserve]
  · omega
  · omega
  · have hb := FixedDegree10Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree10Class33.reserve]
  · have hb := FixedDegree10Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree10Class34.reserve]
  · have hb := FixedDegree10Class30.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree10Class30.reserve]
  · omega
  · omega
  · omega
  · have hb := FixedDegree10Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree10Class44.reserve]
  · have hb := FixedDegree10Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree10Class40.reserve]
  · omega
  · omega
  · omega
  · omega
  · have hb := D10UpperCompositionalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D10UpperCompositionalBothLong.reserve]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree10ClassCertificates
