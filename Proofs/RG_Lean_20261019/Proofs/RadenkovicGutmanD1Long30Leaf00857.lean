/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00857 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 611892721824395584606306304000000000000 233795247621668429064389738612492599296 430189865198344252189310976000000000000))
theorem leaf00857_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 611892721824395584606306304000000000000 233795247621668429064389738612492599296 430189865198344252189310976000000000000 raw00857=true := by decide +kernel
#print axioms leaf00857_raw
theorem leaf00857_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00857=true := by decide +kernel
#print axioms leaf00857_rectangular
def affine00857 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00857 (IntegerComputedClassCell.leftNumerator ![(7/128),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(7/128),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.denominator ![(7/128),0,(1/8)] ![(1/640),1,(1/8)]))
theorem leaf00857_transform : affine00857=(NestedInteger.clearedAll 3 raw00857 (IntegerComputedClassCell.leftNumerator ![(7/128),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(7/128),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.denominator ![(7/128),0,(1/8)] ![(1/640),1,(1/8)])) := by decide +kernel
#print axioms leaf00857_transform
theorem leaf00857_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00857=true := by decide +kernel
#print axioms leaf00857_sign
theorem leaf00857_log : RationalLog.accepts (66451089/268435456) (-2998197215/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00857_log
def leaf00857 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (67933738837/125000000000) (66451089/268435456) (-2998197215/4294967296) 3 8 ![60,0,4] ![(7/128),0,(1/8)] ![(1/640),1,(1/8)] affine00857
theorem leaf00857_checked : FastNestedCellData.accepts 1 2 4 leaf00857=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (67933738837/125000000000) (66451089/268435456) (-2998197215/4294967296) 3 8 ![60,0,4] ![(7/128),0,(1/8)] ![(1/640),1,(1/8)] 611892721824395584606306304000000000000 233795247621668429064389738612492599296 430189865198344252189310976000000000000 raw00857 affine00857
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00857_raw leaf00857_rectangular
    leaf00857_transform leaf00857_sign leaf00857_log
#print axioms leaf00857_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
