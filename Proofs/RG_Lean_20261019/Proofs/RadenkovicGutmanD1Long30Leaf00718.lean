/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00718 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 12480231396770151756741790924800000000000 8024464202153593617872659033990367281152 37064927113470767947854118912000000000000))
theorem leaf00718_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 12480231396770151756741790924800000000000 8024464202153593617872659033990367281152 37064927113470767947854118912000000000000 raw00718=true := by decide +kernel
#print axioms leaf00718_raw
theorem leaf00718_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00718=true := by decide +kernel
#print axioms leaf00718_rectangular
def affine00718 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00718 (IntegerComputedClassCell.leftNumerator ![(97/3200),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(97/3200),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(97/3200),0,(1/4)] ![(3/6400),1,(1/4)]))
theorem leaf00718_transform : affine00718=(NestedInteger.clearedAll 3 raw00718 (IntegerComputedClassCell.leftNumerator ![(97/3200),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(97/3200),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(97/3200),0,(1/4)] ![(3/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00718_transform
theorem leaf00718_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00718=true := by decide +kernel
#print axioms leaf00718_sign
theorem leaf00718_log : RationalLog.accepts (2270084615/4294967296) (-1369293237/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00718_log
def leaf00718 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (27062187987/125000000000) (2270084615/4294967296) (-1369293237/4294967296) 1 8 ![60,0,4] ![(97/3200),0,(1/4)] ![(3/6400),1,(1/4)] affine00718
theorem leaf00718_checked : FastNestedCellData.accepts 1 2 4 leaf00718=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (27062187987/125000000000) (2270084615/4294967296) (-1369293237/4294967296) 1 8 ![60,0,4] ![(97/3200),0,(1/4)] ![(3/6400),1,(1/4)] 12480231396770151756741790924800000000000 8024464202153593617872659033990367281152 37064927113470767947854118912000000000000 raw00718 affine00718
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00718_raw leaf00718_rectangular
    leaf00718_transform leaf00718_sign leaf00718_log
#print axioms leaf00718_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
