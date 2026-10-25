/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeFourToFortyfiveDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree28Class11
import Proofs.RadenkovicGutmanFixedDegree28Class12
import Proofs.RadenkovicGutmanFixedDegree28Class13
import Proofs.RadenkovicGutmanFixedDegree28Class14
import Proofs.RadenkovicGutmanFixedDegree28Class10
import Proofs.RadenkovicGutmanFixedDegree28Class22
import Proofs.RadenkovicGutmanFixedDegree28Class23
import Proofs.RadenkovicGutmanFixedDegree28Class24
import Proofs.RadenkovicGutmanFixedDegree28Class20
import Proofs.RadenkovicGutmanFixedDegree28Class33
import Proofs.RadenkovicGutmanFixedDegree28Class34
import Proofs.RadenkovicGutmanFixedDegree28Class30
import Proofs.RadenkovicGutmanFixedDegree28Class44
import Proofs.RadenkovicGutmanFixedDegree28Class40
import Proofs.RadenkovicGutmanD28UpperCompositionalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree28ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates 28 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree28Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree28Class11.reserve]
  · have hb := FixedDegree28Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree28Class12.reserve]
  · have hb := FixedDegree28Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree28Class13.reserve]
  · have hb := FixedDegree28Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree28Class14.reserve]
  · have hb := FixedDegree28Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree28Class10.reserve]
  · omega
  · have hb := FixedDegree28Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree28Class22.reserve]
  · have hb := FixedDegree28Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree28Class23.reserve]
  · have hb := FixedDegree28Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree28Class24.reserve]
  · have hb := FixedDegree28Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree28Class20.reserve]
  · omega
  · omega
  · have hb := FixedDegree28Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree28Class33.reserve]
  · have hb := FixedDegree28Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree28Class34.reserve]
  · have hb := FixedDegree28Class30.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree28Class30.reserve]
  · omega
  · omega
  · omega
  · have hb := FixedDegree28Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree28Class44.reserve]
  · have hb := FixedDegree28Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree28Class40.reserve]
  · omega
  · omega
  · omega
  · omega
  · have hb := D28UpperCompositionalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D28UpperCompositionalBothLong.reserve]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree28ClassCertificates
