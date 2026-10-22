/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00427 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3036846520415933596688975921152000000000000 2115166820133613695595649891847194508525568 12848176798497813829571150086144000000000000))
theorem leaf00427_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3036846520415933596688975921152000000000000 2115166820133613695595649891847194508525568 12848176798497813829571150086144000000000000 raw00427=true := by decide +kernel
#print axioms leaf00427_raw
theorem leaf00427_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00427=true := by decide +kernel
#print axioms leaf00427_rectangular
def affine00427 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00427 (IntegerComputedClassCell.leftNumerator ![(69/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(69/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(69/6400),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00427_transform : affine00427=(NestedInteger.clearedAll 3 raw00427 (IntegerComputedClassCell.leftNumerator ![(69/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(69/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(69/6400),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00427_transform
theorem leaf00427_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00427=true := by decide +kernel
#print axioms leaf00427_sign
theorem leaf00427_log : RationalLog.accepts (2568588287/4294967296) (-1103994531/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00427_log
def leaf00427 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (164627779747/1000000000000) (2568588287/4294967296) (-1103994531/4294967296) 1 8 ![60,0,4] ![(69/6400),0,(1/8)] ![(1/6400),1,(1/8)] affine00427
theorem leaf00427_checked : FastNestedCellData.accepts 1 2 4 leaf00427=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (164627779747/1000000000000) (2568588287/4294967296) (-1103994531/4294967296) 1 8 ![60,0,4] ![(69/6400),0,(1/8)] ![(1/6400),1,(1/8)] 3036846520415933596688975921152000000000000 2115166820133613695595649891847194508525568 12848176798497813829571150086144000000000000 raw00427 affine00427
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00427_raw leaf00427_rectangular
    leaf00427_transform leaf00427_sign leaf00427_log
#print axioms leaf00427_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
