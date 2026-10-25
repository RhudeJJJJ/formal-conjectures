/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeFourToFortyfiveDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree12Class11
import Proofs.RadenkovicGutmanFixedDegree12Class12
import Proofs.RadenkovicGutmanFixedDegree12Class13
import Proofs.RadenkovicGutmanFixedDegree12Class14
import Proofs.RadenkovicGutmanFixedDegree12Class10
import Proofs.RadenkovicGutmanFixedDegree12Class22
import Proofs.RadenkovicGutmanFixedDegree12Class23
import Proofs.RadenkovicGutmanFixedDegree12Class24
import Proofs.RadenkovicGutmanFixedDegree12Class20
import Proofs.RadenkovicGutmanFixedDegree12Class33
import Proofs.RadenkovicGutmanFixedDegree12Class34
import Proofs.RadenkovicGutmanFixedDegree12Class30
import Proofs.RadenkovicGutmanFixedDegree12Class44
import Proofs.RadenkovicGutmanFixedDegree12Class40
import Proofs.RadenkovicGutmanD12UpperCompositionalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree12ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates 12 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree12Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree12Class11.reserve]
  · have hb := FixedDegree12Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree12Class12.reserve]
  · have hb := FixedDegree12Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree12Class13.reserve]
  · have hb := FixedDegree12Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree12Class14.reserve]
  · have hb := FixedDegree12Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree12Class10.reserve]
  · omega
  · have hb := FixedDegree12Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree12Class22.reserve]
  · have hb := FixedDegree12Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree12Class23.reserve]
  · have hb := FixedDegree12Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree12Class24.reserve]
  · have hb := FixedDegree12Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree12Class20.reserve]
  · omega
  · omega
  · have hb := FixedDegree12Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree12Class33.reserve]
  · have hb := FixedDegree12Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree12Class34.reserve]
  · have hb := FixedDegree12Class30.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree12Class30.reserve]
  · omega
  · omega
  · omega
  · have hb := FixedDegree12Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree12Class44.reserve]
  · have hb := FixedDegree12Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree12Class40.reserve]
  · omega
  · omega
  · omega
  · omega
  · have hb := D12UpperCompositionalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D12UpperCompositionalBothLong.reserve]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree12ClassCertificates
