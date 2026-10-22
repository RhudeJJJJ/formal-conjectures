/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01281 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 9825517731235155259462516736000000000000 10289582507415333585674351925373754671104 4829498565154707401196863225856000000000000))
theorem leaf01281_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 9825517731235155259462516736000000000000 10289582507415333585674351925373754671104 4829498565154707401196863225856000000000000 raw01281=true := by decide +kernel
#print axioms leaf01281_raw
theorem leaf01281_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01281=true := by decide +kernel
#print axioms leaf01281_rectangular
def affine01281 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01281 (IntegerComputedClassCell.leftNumerator ![(21/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(21/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(21/128),0,(1/2)] ![(1/128),1,(1/4)]))
theorem leaf01281_transform : affine01281=(NestedInteger.clearedAll 3 raw01281 (IntegerComputedClassCell.leftNumerator ![(21/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(21/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(21/128),0,(1/2)] ![(1/128),1,(1/4)])) := by decide +kernel
#print axioms leaf01281_transform
theorem leaf01281_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01281=true := by decide +kernel
#print axioms leaf01281_sign
theorem leaf01281_log : RationalLog.accepts (4488258491/4294967296) (47266997/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01281_log
def leaf01281 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (1065284767/500000000000) (4488258491/4294967296) (47266997/2147483648) 0 8 ![60,0,4] ![(21/128),0,(1/2)] ![(1/128),1,(1/4)] affine01281
theorem leaf01281_checked : FastNestedCellData.accepts 1 2 4 leaf01281=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (1065284767/500000000000) (4488258491/4294967296) (47266997/2147483648) 0 8 ![60,0,4] ![(21/128),0,(1/2)] ![(1/128),1,(1/4)] 9825517731235155259462516736000000000000 10289582507415333585674351925373754671104 4829498565154707401196863225856000000000000 raw01281 affine01281
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01281_raw leaf01281_rectangular
    leaf01281_transform leaf01281_sign leaf01281_log
#print axioms leaf01281_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
