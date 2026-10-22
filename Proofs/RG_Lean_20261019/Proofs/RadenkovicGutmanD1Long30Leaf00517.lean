/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00517 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 995684290209659220486829113344000000000000 623329954367321146723954821896299761106944 2887061756108914336568394645504000000000000))
theorem leaf00517_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 995684290209659220486829113344000000000000 623329954367321146723954821896299761106944 2887061756108914336568394645504000000000000 raw00517=true := by decide +kernel
#print axioms leaf00517_raw
theorem leaf00517_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00517=true := by decide +kernel
#print axioms leaf00517_rectangular
def affine00517 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00517 (IntegerComputedClassCell.leftNumerator ![(23/1600),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(23/1600),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(23/1600),0,(1/8)] ![(1/3200),1,(1/8)]))
theorem leaf00517_transform : affine00517=(NestedInteger.clearedAll 3 raw00517 (IntegerComputedClassCell.leftNumerator ![(23/1600),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(23/1600),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(23/1600),0,(1/8)] ![(1/3200),1,(1/8)])) := by decide +kernel
#print axioms leaf00517_transform
theorem leaf00517_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00517=true := by decide +kernel
#print axioms leaf00517_sign
theorem leaf00517_log : RationalLog.accepts (1105672993/2147483648) (-712795547/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00517_log
def leaf00517 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (215904614111/1000000000000) (1105672993/2147483648) (-712795547/2147483648) 1 8 ![60,0,4] ![(23/1600),0,(1/8)] ![(1/3200),1,(1/8)] affine00517
theorem leaf00517_checked : FastNestedCellData.accepts 1 2 4 leaf00517=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (215904614111/1000000000000) (1105672993/2147483648) (-712795547/2147483648) 1 8 ![60,0,4] ![(23/1600),0,(1/8)] ![(1/3200),1,(1/8)] 995684290209659220486829113344000000000000 623329954367321146723954821896299761106944 2887061756108914336568394645504000000000000 raw00517 affine00517
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00517_raw leaf00517_rectangular
    leaf00517_transform leaf00517_sign leaf00517_log
#print axioms leaf00517_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
