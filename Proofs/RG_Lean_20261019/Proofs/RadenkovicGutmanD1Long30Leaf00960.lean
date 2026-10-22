/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00960 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 11164363978339297023326001561600000000000 3486560120451800194573848973704626700288 4500625995995446917355012096000000000000))
theorem leaf00960_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 11164363978339297023326001561600000000000 3486560120451800194573848973704626700288 4500625995995446917355012096000000000000 raw00960=true := by decide +kernel
#print axioms leaf00960_raw
theorem leaf00960_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00960=true := by decide +kernel
#print axioms leaf00960_rectangular
def affine00960 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00960 (IntegerComputedClassCell.leftNumerator ![(33/320),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(33/320),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(33/320),0,0] ![(1/320),1,(1/16)]))
theorem leaf00960_transform : affine00960=(NestedInteger.clearedAll 3 raw00960 (IntegerComputedClassCell.leftNumerator ![(33/320),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(33/320),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(33/320),0,0] ![(1/320),1,(1/16)])) := by decide +kernel
#print axioms leaf00960_transform
theorem leaf00960_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00960=true := by decide +kernel
#print axioms leaf00960_sign
theorem leaf00960_log : RationalLog.accepts (47236985/268435456) (-3731109775/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00960_log
def leaf00960 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (774683371503/1000000000000) (47236985/268435456) (-3731109775/4294967296) 3 8 ![60,0,4] ![(33/320),0,0] ![(1/320),1,(1/16)] affine00960
theorem leaf00960_checked : FastNestedCellData.accepts 1 2 4 leaf00960=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (774683371503/1000000000000) (47236985/268435456) (-3731109775/4294967296) 3 8 ![60,0,4] ![(33/320),0,0] ![(1/320),1,(1/16)] 11164363978339297023326001561600000000000 3486560120451800194573848973704626700288 4500625995995446917355012096000000000000 raw00960 affine00960
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00960_raw leaf00960_rectangular
    leaf00960_transform leaf00960_sign leaf00960_log
#print axioms leaf00960_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
