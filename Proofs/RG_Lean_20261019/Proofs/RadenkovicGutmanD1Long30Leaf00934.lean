/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00934 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 4771751654213890851619469262848000000000000 3156167242587188389538099019069906638340096 12201181787492437051817204908032000000000000))
theorem leaf00934_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 4771751654213890851619469262848000000000000 3156167242587188389538099019069906638340096 12201181787492437051817204908032000000000000 raw00934=true := by decide +kernel
#print axioms leaf00934_raw
theorem leaf00934_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00934=true := by decide +kernel
#print axioms leaf00934_rectangular
def affine00934 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00934 (IntegerComputedClassCell.leftNumerator ![(27/320),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(27/320),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(27/320),0,(1/2)] ![(1/320),1,(1/2)]))
theorem leaf00934_transform : affine00934=(NestedInteger.clearedAll 3 raw00934 (IntegerComputedClassCell.leftNumerator ![(27/320),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(27/320),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(27/320),0,(1/2)] ![(1/320),1,(1/2)])) := by decide +kernel
#print axioms leaf00934_transform
theorem leaf00934_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00934=true := by decide +kernel
#print axioms leaf00934_sign
theorem leaf00934_log : RationalLog.accepts (2256979839/4294967296) (-690863091/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00934_log
def leaf00934 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (258677175503/1000000000000) (2256979839/4294967296) (-690863091/2147483648) 1 8 ![60,0,4] ![(27/320),0,(1/2)] ![(1/320),1,(1/2)] affine00934
theorem leaf00934_checked : FastNestedCellData.accepts 1 2 4 leaf00934=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (258677175503/1000000000000) (2256979839/4294967296) (-690863091/2147483648) 1 8 ![60,0,4] ![(27/320),0,(1/2)] ![(1/320),1,(1/2)] 4771751654213890851619469262848000000000000 3156167242587188389538099019069906638340096 12201181787492437051817204908032000000000000 raw00934 affine00934
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00934_raw leaf00934_rectangular
    leaf00934_transform leaf00934_sign leaf00934_log
#print axioms leaf00934_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
