/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeFourToFortyfiveDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree45Class11
import Proofs.RadenkovicGutmanFixedDegree45Class12
import Proofs.RadenkovicGutmanFixedDegree45Class13
import Proofs.RadenkovicGutmanFixedDegree45Class14
import Proofs.RadenkovicGutmanFixedDegree45Class10
import Proofs.RadenkovicGutmanFixedDegree45Class22
import Proofs.RadenkovicGutmanFixedDegree45Class23
import Proofs.RadenkovicGutmanFixedDegree45Class24
import Proofs.RadenkovicGutmanFixedDegree45Class20
import Proofs.RadenkovicGutmanFixedDegree45Class33
import Proofs.RadenkovicGutmanFixedDegree45Class34
import Proofs.RadenkovicGutmanFixedDegree45Class30
import Proofs.RadenkovicGutmanFixedDegree45Class44
import Proofs.RadenkovicGutmanFixedDegree45Class40
import Proofs.RadenkovicGutmanD45UpperCompositionalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree45ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates 45 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree45Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree45Class11.reserve]
  · have hb := FixedDegree45Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree45Class12.reserve]
  · have hb := FixedDegree45Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree45Class13.reserve]
  · have hb := FixedDegree45Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree45Class14.reserve]
  · have hb := FixedDegree45Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree45Class10.reserve]
  · omega
  · have hb := FixedDegree45Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree45Class22.reserve]
  · have hb := FixedDegree45Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree45Class23.reserve]
  · have hb := FixedDegree45Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree45Class24.reserve]
  · have hb := FixedDegree45Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree45Class20.reserve]
  · omega
  · omega
  · have hb := FixedDegree45Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree45Class33.reserve]
  · have hb := FixedDegree45Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree45Class34.reserve]
  · have hb := FixedDegree45Class30.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree45Class30.reserve]
  · omega
  · omega
  · omega
  · have hb := FixedDegree45Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree45Class44.reserve]
  · have hb := FixedDegree45Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree45Class40.reserve]
  · omega
  · omega
  · omega
  · omega
  · have hb := D45UpperCompositionalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D45UpperCompositionalBothLong.reserve]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree45ClassCertificates
