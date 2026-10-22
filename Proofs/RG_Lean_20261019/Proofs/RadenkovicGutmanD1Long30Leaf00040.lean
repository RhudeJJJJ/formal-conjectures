/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00040 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 533082284193382142877031517388800000000000 12265476816415671495709586688095289344 84886749563172419551625216000000000000))
theorem leaf00040_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 533082284193382142877031517388800000000000 12265476816415671495709586688095289344 84886749563172419551625216000000000000 raw00040=true := by decide +kernel
#print axioms leaf00040_raw
theorem leaf00040_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00040=true := by decide +kernel
#print axioms leaf00040_rectangular
def affine00040 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00040 (IntegerComputedClassCell.leftNumerator ![(3/2000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/2000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/2000),0,0] ![(1/16000),1,(1/16)]))
theorem leaf00040_transform : affine00040=(NestedInteger.clearedAll 3 raw00040 (IntegerComputedClassCell.leftNumerator ![(3/2000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/2000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/2000),0,0] ![(1/16000),1,(1/16)])) := by decide +kernel
#print axioms leaf00040_transform
theorem leaf00040_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00040=true := by decide +kernel
#print axioms leaf00040_sign
theorem leaf00040_log : RationalLog.accepts (86345/4294967296) (-23224184955/4294967296) 16 8=true := by decide +kernel
#print axioms leaf00040_log
def leaf00040 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (144492242659/1000000000000) (86345/4294967296) (-23224184955/4294967296) 16 8 ![60,0,4] ![(3/2000),0,0] ![(1/16000),1,(1/16)] affine00040
theorem leaf00040_checked : FastNestedCellData.accepts 1 2 4 leaf00040=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (144492242659/1000000000000) (86345/4294967296) (-23224184955/4294967296) 16 8 ![60,0,4] ![(3/2000),0,0] ![(1/16000),1,(1/16)] 533082284193382142877031517388800000000000 12265476816415671495709586688095289344 84886749563172419551625216000000000000 raw00040 affine00040
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00040_raw leaf00040_rectangular
    leaf00040_transform leaf00040_sign leaf00040_log
#print axioms leaf00040_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
