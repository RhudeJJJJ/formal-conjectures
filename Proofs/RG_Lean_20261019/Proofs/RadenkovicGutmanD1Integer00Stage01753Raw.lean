/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerAffineStages
import Proofs.RadenkovicGutmanD1IntegerNorm00
namespace Gebendorfer.RadenkovicGutman.DegreeOneInteger00Stages
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01753 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 90561984186867829964800000000000 90562156893732861280543209160704 57646185164693100751459713024000000000000))
theorem leaf01753_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack
    true 90561984186867829964800000000000 90562156893732861280543209160704 57646185164693100751459713024000000000000 raw01753=true := by decide +kernel
#print axioms leaf01753_raw
theorem leaf01753_rectangular : NestedInteger.rectangular 3 ![88,4,4] raw01753=true := by decide +kernel
#print axioms leaf01753_rectangular
end Gebendorfer.RadenkovicGutman.DegreeOneInteger00Stages
