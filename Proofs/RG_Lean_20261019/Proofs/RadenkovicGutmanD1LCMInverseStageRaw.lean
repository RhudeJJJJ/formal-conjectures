/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1LCMInverseStageData
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseStages
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem leaf01753_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 168684840550400000000000 168685162242004389465867 107374387168685161977000000000000 raw01753=true := by decide +kernel
#print axioms leaf01753_raw
theorem leaf01753_rectangular : NestedInteger.rectangular 3 ![88,4,4] raw01753=true := by decide +kernel
#print axioms leaf01753_rectangular
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseStages
