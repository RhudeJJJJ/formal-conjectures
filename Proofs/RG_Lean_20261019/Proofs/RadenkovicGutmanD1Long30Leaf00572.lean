/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00572 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1202981077523562969614902099968000000000000 690619268086613162608695421473859162865664 2647522294571758439853816020992000000000000))
theorem leaf00572_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1202981077523562969614902099968000000000000 690619268086613162608695421473859162865664 2647522294571758439853816020992000000000000 raw00572=true := by decide +kernel
#print axioms leaf00572_raw
theorem leaf00572_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00572=true := by decide +kernel
#print axioms leaf00572_rectangular
def affine00572 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00572 (IntegerComputedClassCell.leftNumerator ![(57/3200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(57/3200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(57/3200),0,(1/8)] ![(1/3200),1,(1/8)]))
theorem leaf00572_transform : affine00572=(NestedInteger.clearedAll 3 raw00572 (IntegerComputedClassCell.leftNumerator ![(57/3200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(57/3200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(57/3200),0,(1/8)] ![(1/3200),1,(1/8)])) := by decide +kernel
#print axioms leaf00572_transform
theorem leaf00572_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00572=true := by decide +kernel
#print axioms leaf00572_sign
theorem leaf00572_log : RationalLog.accepts (1955575699/4294967296) (-1689552837/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00572_log
def leaf00572 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (130427469771/500000000000) (1955575699/4294967296) (-1689552837/4294967296) 2 8 ![60,0,4] ![(57/3200),0,(1/8)] ![(1/3200),1,(1/8)] affine00572
theorem leaf00572_checked : FastNestedCellData.accepts 1 2 4 leaf00572=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (130427469771/500000000000) (1955575699/4294967296) (-1689552837/4294967296) 2 8 ![60,0,4] ![(57/3200),0,(1/8)] ![(1/3200),1,(1/8)] 1202981077523562969614902099968000000000000 690619268086613162608695421473859162865664 2647522294571758439853816020992000000000000 raw00572 affine00572
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00572_raw leaf00572_rectangular
    leaf00572_transform leaf00572_sign leaf00572_log
#print axioms leaf00572_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
