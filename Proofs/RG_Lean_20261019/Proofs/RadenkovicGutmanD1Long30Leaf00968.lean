/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00968 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 699056512746595902816306331648000000000000 387251013861760625274741535908208557686784 851566863662844597712237625344000000000000))
theorem leaf00968_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 699056512746595902816306331648000000000000 387251013861760625274741535908208557686784 851566863662844597712237625344000000000000 raw00968=true := by decide +kernel
#print axioms leaf00968_raw
theorem leaf00968_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00968=true := by decide +kernel
#print axioms leaf00968_rectangular
def affine00968 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00968 (IntegerComputedClassCell.leftNumerator ![(17/160),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/160),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/160),0,(1/4)] ![(1/160),1,(1/4)]))
theorem leaf00968_transform : affine00968=(NestedInteger.clearedAll 3 raw00968 (IntegerComputedClassCell.leftNumerator ![(17/160),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/160),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/160),0,(1/4)] ![(1/160),1,(1/4)])) := by decide +kernel
#print axioms leaf00968_transform
theorem leaf00968_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00968=true := by decide +kernel
#print axioms leaf00968_sign
theorem leaf00968_log : RationalLog.accepts (1635503313/4294967296) (-2073381247/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00968_log
def leaf00968 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (227375576943/500000000000) (1635503313/4294967296) (-2073381247/4294967296) 2 8 ![60,0,4] ![(17/160),0,(1/4)] ![(1/160),1,(1/4)] affine00968
theorem leaf00968_checked : FastNestedCellData.accepts 1 2 4 leaf00968=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (227375576943/500000000000) (1635503313/4294967296) (-2073381247/4294967296) 2 8 ![60,0,4] ![(17/160),0,(1/4)] ![(1/160),1,(1/4)] 699056512746595902816306331648000000000000 387251013861760625274741535908208557686784 851566863662844597712237625344000000000000 raw00968 affine00968
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00968_raw leaf00968_rectangular
    leaf00968_transform leaf00968_sign leaf00968_log
#print axioms leaf00968_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
