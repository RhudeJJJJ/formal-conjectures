/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00127 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 51781855703208902495131664384000000000000 46645349671287012457058547900901327110144 1038557347851094647913228271616000000000000))
theorem leaf00127_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 51781855703208902495131664384000000000000 46645349671287012457058547900901327110144 1038557347851094647913228271616000000000000 raw00127=true := by decide +kernel
#print axioms leaf00127_raw
theorem leaf00127_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00127=true := by decide +kernel
#print axioms leaf00127_rectangular
def affine00127 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00127 (IntegerComputedClassCell.leftNumerator ![(91/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(91/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(91/32000),0,(1/8)] ![(3/32000),1,(1/8)]))
theorem leaf00127_transform : affine00127=(NestedInteger.clearedAll 3 raw00127 (IntegerComputedClassCell.leftNumerator ![(91/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(91/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(91/32000),0,(1/8)] ![(3/32000),1,(1/8)])) := by decide +kernel
#print axioms leaf00127_transform
theorem leaf00127_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00127=true := by decide +kernel
#print axioms leaf00127_sign
theorem leaf00127_log : RationalLog.accepts (925657301/1073741824) (-39836035/536870912) 1 8=true := by decide +kernel
#print axioms leaf00127_log
def leaf00127 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (44913600359/1000000000000) (925657301/1073741824) (-39836035/536870912) 1 8 ![60,0,4] ![(91/32000),0,(1/8)] ![(3/32000),1,(1/8)] affine00127
theorem leaf00127_checked : FastNestedCellData.accepts 1 2 4 leaf00127=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (44913600359/1000000000000) (925657301/1073741824) (-39836035/536870912) 1 8 ![60,0,4] ![(91/32000),0,(1/8)] ![(3/32000),1,(1/8)] 51781855703208902495131664384000000000000 46645349671287012457058547900901327110144 1038557347851094647913228271616000000000000 raw00127 affine00127
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00127_raw leaf00127_rectangular
    leaf00127_transform leaf00127_sign leaf00127_log
#print axioms leaf00127_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
