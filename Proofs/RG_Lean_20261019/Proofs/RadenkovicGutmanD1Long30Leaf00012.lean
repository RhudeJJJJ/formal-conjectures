/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00012 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 46308476675088259500474368000000000000 44353454552109142340371856140422610944 2464839710139831491751837696000000000000))
theorem leaf00012_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 46308476675088259500474368000000000000 44353454552109142340371856140422610944 2464839710139831491751837696000000000000 raw00012=true := by decide +kernel
#print axioms leaf00012_raw
theorem leaf00012_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00012=true := by decide +kernel
#print axioms leaf00012_rectangular
def affine00012 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00012 (IntegerComputedClassCell.leftNumerator ![(9/8000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(9/8000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(9/8000),0,(1/8)] ![(1/16000),1,(1/8)]))
theorem leaf00012_transform : affine00012=(NestedInteger.clearedAll 3 raw00012 (IntegerComputedClassCell.leftNumerator ![(9/8000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(9/8000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(9/8000),0,(1/8)] ![(1/16000),1,(1/8)])) := by decide +kernel
#print axioms leaf00012_transform
theorem leaf00012_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00012=true := by decide +kernel
#print axioms leaf00012_sign
theorem leaf00012_log : RationalLog.accepts (505116339/536870912) (-130929755/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00012_log
def leaf00012 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (4498614491/250000000000) (505116339/536870912) (-130929755/4294967296) 1 8 ![60,0,4] ![(9/8000),0,(1/8)] ![(1/16000),1,(1/8)] affine00012
theorem leaf00012_checked : FastNestedCellData.accepts 1 2 4 leaf00012=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (4498614491/250000000000) (505116339/536870912) (-130929755/4294967296) 1 8 ![60,0,4] ![(9/8000),0,(1/8)] ![(1/16000),1,(1/8)] 46308476675088259500474368000000000000 44353454552109142340371856140422610944 2464839710139831491751837696000000000000 raw00012 affine00012
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00012_raw leaf00012_rectangular
    leaf00012_transform leaf00012_sign leaf00012_log
#print axioms leaf00012_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
