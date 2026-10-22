/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00307 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 825270868016050547370631993753600000000 424283937464149734392536232658034753536 948374347419075362596847616000000000000))
theorem leaf00307_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 825270868016050547370631993753600000000 424283937464149734392536232658034753536 948374347419075362596847616000000000000 raw00307=true := by decide +kernel
#print axioms leaf00307_raw
theorem leaf00307_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00307=true := by decide +kernel
#print axioms leaf00307_rectangular
def affine00307 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00307 (IntegerComputedClassCell.leftNumerator ![(7/80),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/80),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/80),0,(1/4)] ![(1/320),1,(1/4)]))
theorem leaf00307_transform : affine00307=(NestedInteger.clearedAll 3 raw00307 (IntegerComputedClassCell.leftNumerator ![(7/80),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/80),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/80),0,(1/4)] ![(1/320),1,(1/4)])) := by decide +kernel
#print axioms leaf00307_transform
theorem leaf00307_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00307=true := by decide +kernel
#print axioms leaf00307_sign
theorem leaf00307_log : RationalLog.accepts (1525588125/4294967296) (-2222782977/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00307_log
def leaf00307 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (111845058499/250000000000) (1525588125/4294967296) (-2222782977/4294967296) 2 8 ![52,0,4] ![(7/80),0,(1/4)] ![(1/320),1,(1/4)] affine00307
theorem leaf00307_checked : FastNestedCellData.accepts 1 0 4 leaf00307=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (111845058499/250000000000) (1525588125/4294967296) (-2222782977/4294967296) 2 8 ![52,0,4] ![(7/80),0,(1/4)] ![(1/320),1,(1/4)] 825270868016050547370631993753600000000 424283937464149734392536232658034753536 948374347419075362596847616000000000000 raw00307 affine00307
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00307_raw leaf00307_rectangular
    leaf00307_transform leaf00307_sign leaf00307_log
#print axioms leaf00307_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
