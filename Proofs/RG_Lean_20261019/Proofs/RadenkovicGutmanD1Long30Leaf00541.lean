/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00541 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 319337002369481020931738645299200000000000 125220174630362657008046661644437319319552 289337533343398683993249834598400000000000))
theorem leaf00541_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 319337002369481020931738645299200000000000 125220174630362657008046661644437319319552 289337533343398683993249834598400000000000 raw00541=true := by decide +kernel
#print axioms leaf00541_raw
theorem leaf00541_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00541=true := by decide +kernel
#print axioms leaf00541_rectangular
def affine00541 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00541 (IntegerComputedClassCell.leftNumerator ![(51/3200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(51/3200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(51/3200),0,(1/16)] ![(1/3200),1,(1/16)]))
theorem leaf00541_transform : affine00541=(NestedInteger.clearedAll 3 raw00541 (IntegerComputedClassCell.leftNumerator ![(51/3200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(51/3200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(51/3200),0,(1/16)] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00541_transform
theorem leaf00541_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00541=true := by decide +kernel
#print axioms leaf00541_sign
theorem leaf00541_log : RationalLog.accepts (1175451467/4294967296) (-2782691429/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00541_log
def leaf00541 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (86556467931/200000000000) (1175451467/4294967296) (-2782691429/4294967296) 2 8 ![60,0,4] ![(51/3200),0,(1/16)] ![(1/3200),1,(1/16)] affine00541
theorem leaf00541_checked : FastNestedCellData.accepts 1 2 4 leaf00541=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (86556467931/200000000000) (1175451467/4294967296) (-2782691429/4294967296) 2 8 ![60,0,4] ![(51/3200),0,(1/16)] ![(1/3200),1,(1/16)] 319337002369481020931738645299200000000000 125220174630362657008046661644437319319552 289337533343398683993249834598400000000000 raw00541 affine00541
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00541_raw leaf00541_rectangular
    leaf00541_transform leaf00541_sign leaf00541_log
#print axioms leaf00541_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
