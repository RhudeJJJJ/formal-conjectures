/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00394 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 4605088351330298927341633536000000000000 4239520212817930427021470289666041184256 117933170384866198335671762944000000000000))
theorem leaf00394_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 4605088351330298927341633536000000000000 4239520212817930427021470289666041184256 117933170384866198335671762944000000000000 raw00394=true := by decide +kernel
#print axioms leaf00394_raw
theorem leaf00394_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00394=true := by decide +kernel
#print axioms leaf00394_rectangular
def affine00394 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00394 (IntegerComputedClassCell.leftNumerator ![(31/3200),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(31/3200),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(31/3200),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00394_transform : affine00394=(NestedInteger.clearedAll 3 raw00394 (IntegerComputedClassCell.leftNumerator ![(31/3200),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(31/3200),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(31/3200),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00394_transform
theorem leaf00394_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00394=true := by decide +kernel
#print axioms leaf00394_sign
theorem leaf00394_log : RationalLog.accepts (3816809109/4294967296) (-31683221/536870912) 1 8=true := by decide +kernel
#print axioms leaf00394_log
def leaf00394 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (8987124231/250000000000) (3816809109/4294967296) (-31683221/536870912) 1 8 ![60,0,4] ![(31/3200),0,(1/2)] ![(1/6400),1,(1/2)] affine00394
theorem leaf00394_checked : FastNestedCellData.accepts 1 2 4 leaf00394=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (8987124231/250000000000) (3816809109/4294967296) (-31683221/536870912) 1 8 ![60,0,4] ![(31/3200),0,(1/2)] ![(1/6400),1,(1/2)] 4605088351330298927341633536000000000000 4239520212817930427021470289666041184256 117933170384866198335671762944000000000000 raw00394 affine00394
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00394_raw leaf00394_rectangular
    leaf00394_transform leaf00394_sign leaf00394_log
#print axioms leaf00394_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
