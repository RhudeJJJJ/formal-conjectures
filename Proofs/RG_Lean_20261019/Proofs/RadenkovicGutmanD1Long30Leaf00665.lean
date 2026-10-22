/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00665 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 637176790244843600156052569456640000000000 15500153235283381496737857392350926471168 17949640615420551343812640768000000000000))
theorem leaf00665_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 637176790244843600156052569456640000000000 15500153235283381496737857392350926471168 17949640615420551343812640768000000000000 raw00665=true := by decide +kernel
#print axioms leaf00665_raw
theorem leaf00665_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00665=true := by decide +kernel
#print axioms leaf00665_rectangular
def affine00665 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00665 (IntegerComputedClassCell.leftNumerator ![(41/1600),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(41/1600),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(41/1600),0,0] ![(3/6400),1,(1/16)]))
theorem leaf00665_transform : affine00665=(NestedInteger.clearedAll 3 raw00665 (IntegerComputedClassCell.leftNumerator ![(41/1600),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(41/1600),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(41/1600),0,0] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00665_transform
theorem leaf00665_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00665=true := by decide +kernel
#print axioms leaf00665_sign
theorem leaf00665_log : RationalLog.accepts (56065825/4294967296) (-9317229081/4294967296) 7 8=true := by decide +kernel
#print axioms leaf00665_log
def leaf00665 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (863535575301/1000000000000) (56065825/4294967296) (-9317229081/4294967296) 7 8 ![60,0,4] ![(41/1600),0,0] ![(3/6400),1,(1/16)] affine00665
theorem leaf00665_checked : FastNestedCellData.accepts 1 2 4 leaf00665=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (863535575301/1000000000000) (56065825/4294967296) (-9317229081/4294967296) 7 8 ![60,0,4] ![(41/1600),0,0] ![(3/6400),1,(1/16)] 637176790244843600156052569456640000000000 15500153235283381496737857392350926471168 17949640615420551343812640768000000000000 raw00665 affine00665
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00665_raw leaf00665_rectangular
    leaf00665_transform leaf00665_sign leaf00665_log
#print axioms leaf00665_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
