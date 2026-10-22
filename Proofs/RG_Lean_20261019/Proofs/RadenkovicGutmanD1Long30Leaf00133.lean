/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00133 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 6549019202961366266809417728000000000000 6207530644517714976086251643145075818496 273201045407466551068388753408000000000000))
theorem leaf00133_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 6549019202961366266809417728000000000000 6207530644517714976086251643145075818496 273201045407466551068388753408000000000000 raw00133=true := by decide +kernel
#print axioms leaf00133_raw
theorem leaf00133_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00133=true := by decide +kernel
#print axioms leaf00133_rectangular
def affine00133 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00133 (IntegerComputedClassCell.leftNumerator ![(47/16000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(47/16000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(47/16000),0,(1/4)] ![(3/32000),1,(1/4)]))
theorem leaf00133_transform : affine00133=(NestedInteger.clearedAll 3 raw00133 (IntegerComputedClassCell.leftNumerator ![(47/16000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(47/16000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(47/16000),0,(1/4)] ![(3/32000),1,(1/4)])) := by decide +kernel
#print axioms leaf00133_transform
theorem leaf00133_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00133=true := by decide +kernel
#print axioms leaf00133_sign
theorem leaf00133_log : RationalLog.accepts (3980568431/4294967296) (-163250261/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00133_log
def leaf00133 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (2840184339/125000000000) (3980568431/4294967296) (-163250261/4294967296) 1 8 ![60,0,4] ![(47/16000),0,(1/4)] ![(3/32000),1,(1/4)] affine00133
theorem leaf00133_checked : FastNestedCellData.accepts 1 2 4 leaf00133=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (2840184339/125000000000) (3980568431/4294967296) (-163250261/4294967296) 1 8 ![60,0,4] ![(47/16000),0,(1/4)] ![(3/32000),1,(1/4)] 6549019202961366266809417728000000000000 6207530644517714976086251643145075818496 273201045407466551068388753408000000000000 raw00133 affine00133
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00133_raw leaf00133_rectangular
    leaf00133_transform leaf00133_sign leaf00133_log
#print axioms leaf00133_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
