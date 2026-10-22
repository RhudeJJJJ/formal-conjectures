/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00632 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 22764587553652255369537257472000000000000 11777219418978889311605723770149085904896 37278869814280047104043778048000000000000))
theorem leaf00632_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 22764587553652255369537257472000000000000 11777219418978889311605723770149085904896 37278869814280047104043778048000000000000 raw00632=true := by decide +kernel
#print axioms leaf00632_raw
theorem leaf00632_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00632=true := by decide +kernel
#print axioms leaf00632_rectangular
def affine00632 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00632 (IntegerComputedClassCell.leftNumerator ![(143/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(143/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(143/6400),0,(1/8)] ![(3/6400),1,(1/8)]))
theorem leaf00632_transform : affine00632=(NestedInteger.clearedAll 3 raw00632 (IntegerComputedClassCell.leftNumerator ![(143/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(143/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(143/6400),0,(1/8)] ![(3/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00632_transform
theorem leaf00632_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00632=true := by decide +kernel
#print axioms leaf00632_sign
theorem leaf00632_log : RationalLog.accepts (211068133/536870912) (-2004840751/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00632_log
def leaf00632 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (157961057801/500000000000) (211068133/536870912) (-2004840751/4294967296) 2 8 ![60,0,4] ![(143/6400),0,(1/8)] ![(3/6400),1,(1/8)] affine00632
theorem leaf00632_checked : FastNestedCellData.accepts 1 2 4 leaf00632=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (157961057801/500000000000) (211068133/536870912) (-2004840751/4294967296) 2 8 ![60,0,4] ![(143/6400),0,(1/8)] ![(3/6400),1,(1/8)] 22764587553652255369537257472000000000000 11777219418978889311605723770149085904896 37278869814280047104043778048000000000000 raw00632 affine00632
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00632_raw leaf00632_rectangular
    leaf00632_transform leaf00632_sign leaf00632_log
#print axioms leaf00632_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
