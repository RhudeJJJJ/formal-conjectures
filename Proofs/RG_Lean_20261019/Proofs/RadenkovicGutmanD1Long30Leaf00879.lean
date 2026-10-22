/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00879 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 939309897669122986939149975552000000000000 647610434640772897236198737097036945948672 3179542762438316924136161542144000000000000))
theorem leaf00879_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 939309897669122986939149975552000000000000 647610434640772897236198737097036945948672 3179542762438316924136161542144000000000000 raw00879=true := by decide +kernel
#print axioms leaf00879_raw
theorem leaf00879_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00879=true := by decide +kernel
#print axioms leaf00879_rectangular
def affine00879 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00879 (IntegerComputedClassCell.leftNumerator ![(39/640),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(39/640),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(39/640),0,(1/2)] ![(1/640),1,(1/2)]))
theorem leaf00879_transform : affine00879=(NestedInteger.clearedAll 3 raw00879 (IntegerComputedClassCell.leftNumerator ![(39/640),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(39/640),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(39/640),0,(1/2)] ![(1/640),1,(1/2)])) := by decide +kernel
#print axioms leaf00879_transform
theorem leaf00879_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00879=true := by decide +kernel
#print axioms leaf00879_sign
theorem leaf00879_log : RationalLog.accepts (2460104887/4294967296) (-1196663727/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00879_log
def leaf00879 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (101840183169/500000000000) (2460104887/4294967296) (-1196663727/4294967296) 1 8 ![60,0,4] ![(39/640),0,(1/2)] ![(1/640),1,(1/2)] affine00879
theorem leaf00879_checked : FastNestedCellData.accepts 1 2 4 leaf00879=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (101840183169/500000000000) (2460104887/4294967296) (-1196663727/4294967296) 1 8 ![60,0,4] ![(39/640),0,(1/2)] ![(1/640),1,(1/2)] 939309897669122986939149975552000000000000 647610434640772897236198737097036945948672 3179542762438316924136161542144000000000000 raw00879 affine00879
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00879_raw leaf00879_rectangular
    leaf00879_transform leaf00879_sign leaf00879_log
#print axioms leaf00879_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
