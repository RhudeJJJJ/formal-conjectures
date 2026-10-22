/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00893 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 280033603419162347766364818636800000000000 148146396515472979203746602722280354086912 390355818529773373374833727897600000000000))
theorem leaf00893_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 280033603419162347766364818636800000000000 148146396515472979203746602722280354086912 390355818529773373374833727897600000000000 raw00893=true := by decide +kernel
#print axioms leaf00893_raw
theorem leaf00893_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00893=true := by decide +kernel
#print axioms leaf00893_rectangular
def affine00893 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00893 (IntegerComputedClassCell.leftNumerator ![(21/320),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(21/320),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(21/320),0,(1/4)] ![(1/640),1,(1/4)]))
theorem leaf00893_transform : affine00893=(NestedInteger.clearedAll 3 raw00893 (IntegerComputedClassCell.leftNumerator ![(21/320),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(21/320),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(21/320),0,(1/4)] ![(1/640),1,(1/4)])) := by decide +kernel
#print axioms leaf00893_transform
theorem leaf00893_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00893=true := by decide +kernel
#print axioms leaf00893_sign
theorem leaf00893_log : RationalLog.accepts (1647077247/4294967296) (-2058237711/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00893_log
def leaf00893 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (75903260299/200000000000) (1647077247/4294967296) (-2058237711/4294967296) 2 8 ![60,0,4] ![(21/320),0,(1/4)] ![(1/640),1,(1/4)] affine00893
theorem leaf00893_checked : FastNestedCellData.accepts 1 2 4 leaf00893=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (75903260299/200000000000) (1647077247/4294967296) (-2058237711/4294967296) 2 8 ![60,0,4] ![(21/320),0,(1/4)] ![(1/640),1,(1/4)] 280033603419162347766364818636800000000000 148146396515472979203746602722280354086912 390355818529773373374833727897600000000000 raw00893 affine00893
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00893_raw leaf00893_rectangular
    leaf00893_transform leaf00893_sign leaf00893_log
#print axioms leaf00893_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
