/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00567 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 4738984686113690908745372008448000000000000 2741054516831051095608621767831285831565312 10669697100357952632316760162304000000000000))
theorem leaf00567_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 4738984686113690908745372008448000000000000 2741054516831051095608621767831285831565312 10669697100357952632316760162304000000000000 raw00567=true := by decide +kernel
#print axioms leaf00567_raw
theorem leaf00567_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00567=true := by decide +kernel
#print axioms leaf00567_rectangular
def affine00567 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00567 (IntegerComputedClassCell.leftNumerator ![(7/400),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(7/400),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(7/400),0,(1/8)] ![(1/3200),1,(1/8)]))
theorem leaf00567_transform : affine00567=(NestedInteger.clearedAll 3 raw00567 (IntegerComputedClassCell.leftNumerator ![(7/400),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(7/400),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(7/400),0,(1/8)] ![(1/3200),1,(1/8)])) := by decide +kernel
#print axioms leaf00567_transform
theorem leaf00567_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00567=true := by decide +kernel
#print axioms leaf00567_sign
theorem leaf00567_log : RationalLog.accepts (1976474433/4294967296) (-1666724993/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00567_log
def leaf00567 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (256900874603/1000000000000) (1976474433/4294967296) (-1666724993/4294967296) 2 8 ![60,0,4] ![(7/400),0,(1/8)] ![(1/3200),1,(1/8)] affine00567
theorem leaf00567_checked : FastNestedCellData.accepts 1 2 4 leaf00567=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (256900874603/1000000000000) (1976474433/4294967296) (-1666724993/4294967296) 2 8 ![60,0,4] ![(7/400),0,(1/8)] ![(1/3200),1,(1/8)] 4738984686113690908745372008448000000000000 2741054516831051095608621767831285831565312 10669697100357952632316760162304000000000000 raw00567 affine00567
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00567_raw leaf00567_rectangular
    leaf00567_transform leaf00567_sign leaf00567_log
#print axioms leaf00567_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
