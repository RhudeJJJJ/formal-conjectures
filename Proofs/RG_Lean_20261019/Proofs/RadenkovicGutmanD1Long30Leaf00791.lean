/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00791 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3168704102440757800112031268864000000000000 795009682783933208670360602091093602861056 1157045568181954768143401353216000000000000))
theorem leaf00791_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3168704102440757800112031268864000000000000 795009682783933208670360602091093602861056 1157045568181954768143401353216000000000000 raw00791=true := by decide +kernel
#print axioms leaf00791_raw
theorem leaf00791_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00791=true := by decide +kernel
#print axioms leaf00791_rectangular
def affine00791 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00791 (IntegerComputedClassCell.leftNumerator ![(13/320),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/320),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/320),0,(1/16)] ![(3/3200),1,(1/16)]))
theorem leaf00791_transform : affine00791=(NestedInteger.clearedAll 3 raw00791 (IntegerComputedClassCell.leftNumerator ![(13/320),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/320),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/320),0,(1/16)] ![(3/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00791_transform
theorem leaf00791_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00791=true := by decide +kernel
#print axioms leaf00791_sign
theorem leaf00791_log : RationalLog.accepts (638717699/4294967296) (-4092538397/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00791_log
def leaf00791 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (343551587183/500000000000) (638717699/4294967296) (-4092538397/4294967296) 3 8 ![60,0,4] ![(13/320),0,(1/16)] ![(3/3200),1,(1/16)] affine00791
theorem leaf00791_checked : FastNestedCellData.accepts 1 2 4 leaf00791=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (343551587183/500000000000) (638717699/4294967296) (-4092538397/4294967296) 3 8 ![60,0,4] ![(13/320),0,(1/16)] ![(3/3200),1,(1/16)] 3168704102440757800112031268864000000000000 795009682783933208670360602091093602861056 1157045568181954768143401353216000000000000 raw00791 affine00791
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00791_raw leaf00791_rectangular
    leaf00791_transform leaf00791_sign leaf00791_log
#print axioms leaf00791_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
