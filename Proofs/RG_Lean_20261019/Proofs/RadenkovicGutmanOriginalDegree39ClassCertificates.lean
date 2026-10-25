/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeFourToFortyfiveDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree39Class11
import Proofs.RadenkovicGutmanFixedDegree39Class12
import Proofs.RadenkovicGutmanFixedDegree39Class13
import Proofs.RadenkovicGutmanFixedDegree39Class14
import Proofs.RadenkovicGutmanFixedDegree39Class10
import Proofs.RadenkovicGutmanFixedDegree39Class22
import Proofs.RadenkovicGutmanFixedDegree39Class23
import Proofs.RadenkovicGutmanFixedDegree39Class24
import Proofs.RadenkovicGutmanFixedDegree39Class20
import Proofs.RadenkovicGutmanFixedDegree39Class33
import Proofs.RadenkovicGutmanFixedDegree39Class34
import Proofs.RadenkovicGutmanFixedDegree39Class30
import Proofs.RadenkovicGutmanFixedDegree39Class44
import Proofs.RadenkovicGutmanFixedDegree39Class40
import Proofs.RadenkovicGutmanD39UpperCompositionalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree39ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates 39 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree39Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree39Class11.reserve]
  · have hb := FixedDegree39Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree39Class12.reserve]
  · have hb := FixedDegree39Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree39Class13.reserve]
  · have hb := FixedDegree39Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree39Class14.reserve]
  · have hb := FixedDegree39Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree39Class10.reserve]
  · omega
  · have hb := FixedDegree39Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree39Class22.reserve]
  · have hb := FixedDegree39Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree39Class23.reserve]
  · have hb := FixedDegree39Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree39Class24.reserve]
  · have hb := FixedDegree39Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree39Class20.reserve]
  · omega
  · omega
  · have hb := FixedDegree39Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree39Class33.reserve]
  · have hb := FixedDegree39Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree39Class34.reserve]
  · have hb := FixedDegree39Class30.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree39Class30.reserve]
  · omega
  · omega
  · omega
  · have hb := FixedDegree39Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree39Class44.reserve]
  · have hb := FixedDegree39Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree39Class40.reserve]
  · omega
  · omega
  · omega
  · omega
  · have hb := D39UpperCompositionalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D39UpperCompositionalBothLong.reserve]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree39ClassCertificates
