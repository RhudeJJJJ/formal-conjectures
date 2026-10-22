/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00990 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 12764168355145980713972422148096000000000000 5950238074834366341843795580559407089451008 8599269132944341469948666707968000000000000))
theorem leaf00990_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 12764168355145980713972422148096000000000000 5950238074834366341843795580559407089451008 8599269132944341469948666707968000000000000 raw00990=true := by decide +kernel
#print axioms leaf00990_raw
theorem leaf00990_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00990=true := by decide +kernel
#print axioms leaf00990_rectangular
def affine00990 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00990 (IntegerComputedClassCell.leftNumerator ![(11/80),0,0] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/80),0,0] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/80),0,0] ![(1/160),1,(1/16)]))
theorem leaf00990_transform : affine00990=(NestedInteger.clearedAll 3 raw00990 (IntegerComputedClassCell.leftNumerator ![(11/80),0,0] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/80),0,0] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/80),0,0] ![(1/160),1,(1/16)])) := by decide +kernel
#print axioms leaf00990_transform
theorem leaf00990_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00990=true := by decide +kernel
#print axioms leaf00990_sign
theorem leaf00990_log : RationalLog.accepts (1183354693/4294967296) (-692075251/1073741824) 2 8=true := by decide +kernel
#print axioms leaf00990_log
def leaf00990 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (691946953031/1000000000000) (1183354693/4294967296) (-692075251/1073741824) 2 8 ![60,0,4] ![(11/80),0,0] ![(1/160),1,(1/16)] affine00990
theorem leaf00990_checked : FastNestedCellData.accepts 1 2 4 leaf00990=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (691946953031/1000000000000) (1183354693/4294967296) (-692075251/1073741824) 2 8 ![60,0,4] ![(11/80),0,0] ![(1/160),1,(1/16)] 12764168355145980713972422148096000000000000 5950238074834366341843795580559407089451008 8599269132944341469948666707968000000000000 raw00990 affine00990
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00990_raw leaf00990_rectangular
    leaf00990_transform leaf00990_sign leaf00990_log
#print axioms leaf00990_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
