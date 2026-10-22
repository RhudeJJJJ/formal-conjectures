/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00039 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 78149402298059700501374566400000000000 77127135269469556384020820399050719232 14223002707965113547028955136000000000000))
theorem leaf00039_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 78149402298059700501374566400000000000 77127135269469556384020820399050719232 14223002707965113547028955136000000000000 raw00039=true := by decide +kernel
#print axioms leaf00039_raw
theorem leaf00039_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00039=true := by decide +kernel
#print axioms leaf00039_rectangular
def affine00039 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00039 (IntegerComputedClassCell.leftNumerator ![(23/16000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(23/16000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(23/16000),0,(1/2)] ![(1/16000),1,(1/2)]))
theorem leaf00039_transform : affine00039=(NestedInteger.clearedAll 3 raw00039 (IntegerComputedClassCell.leftNumerator ![(23/16000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(23/16000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(23/16000),0,(1/2)] ![(1/16000),1,(1/2)])) := by decide +kernel
#print axioms leaf00039_transform
theorem leaf00039_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00039=true := by decide +kernel
#print axioms leaf00039_sign
theorem leaf00039_log : RationalLog.accepts (4215923415/4294967296) (-9972545/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00039_log
def leaf00039 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (338919007/62500000000) (4215923415/4294967296) (-9972545/1073741824) 1 8 ![60,0,4] ![(23/16000),0,(1/2)] ![(1/16000),1,(1/2)] affine00039
theorem leaf00039_checked : FastNestedCellData.accepts 1 2 4 leaf00039=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (338919007/62500000000) (4215923415/4294967296) (-9972545/1073741824) 1 8 ![60,0,4] ![(23/16000),0,(1/2)] ![(1/16000),1,(1/2)] 78149402298059700501374566400000000000 77127135269469556384020820399050719232 14223002707965113547028955136000000000000 raw00039 affine00039
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00039_raw leaf00039_rectangular
    leaf00039_transform leaf00039_sign leaf00039_log
#print axioms leaf00039_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
