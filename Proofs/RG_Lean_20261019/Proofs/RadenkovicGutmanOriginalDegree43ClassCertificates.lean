/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeFourToFortyfiveDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree43Class11
import Proofs.RadenkovicGutmanFixedDegree43Class12
import Proofs.RadenkovicGutmanFixedDegree43Class13
import Proofs.RadenkovicGutmanFixedDegree43Class14
import Proofs.RadenkovicGutmanFixedDegree43Class10
import Proofs.RadenkovicGutmanFixedDegree43Class22
import Proofs.RadenkovicGutmanFixedDegree43Class23
import Proofs.RadenkovicGutmanFixedDegree43Class24
import Proofs.RadenkovicGutmanFixedDegree43Class20
import Proofs.RadenkovicGutmanFixedDegree43Class33
import Proofs.RadenkovicGutmanFixedDegree43Class34
import Proofs.RadenkovicGutmanFixedDegree43Class30
import Proofs.RadenkovicGutmanFixedDegree43Class44
import Proofs.RadenkovicGutmanFixedDegree43Class40
import Proofs.RadenkovicGutmanD43UpperCompositionalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree43ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates 43 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree43Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree43Class11.reserve]
  · have hb := FixedDegree43Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree43Class12.reserve]
  · have hb := FixedDegree43Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree43Class13.reserve]
  · have hb := FixedDegree43Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree43Class14.reserve]
  · have hb := FixedDegree43Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree43Class10.reserve]
  · omega
  · have hb := FixedDegree43Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree43Class22.reserve]
  · have hb := FixedDegree43Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree43Class23.reserve]
  · have hb := FixedDegree43Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree43Class24.reserve]
  · have hb := FixedDegree43Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree43Class20.reserve]
  · omega
  · omega
  · have hb := FixedDegree43Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree43Class33.reserve]
  · have hb := FixedDegree43Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree43Class34.reserve]
  · have hb := FixedDegree43Class30.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree43Class30.reserve]
  · omega
  · omega
  · omega
  · have hb := FixedDegree43Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree43Class44.reserve]
  · have hb := FixedDegree43Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree43Class40.reserve]
  · omega
  · omega
  · omega
  · omega
  · have hb := D43UpperCompositionalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D43UpperCompositionalBothLong.reserve]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree43ClassCertificates
