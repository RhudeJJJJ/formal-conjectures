/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00626 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3930382635215548897882999357440000000000 1256774638293101606861595038302511038464 2359403881261074227501297827840000000000))
theorem leaf00626_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3930382635215548897882999357440000000000 1256774638293101606861595038302511038464 2359403881261074227501297827840000000000 raw00626=true := by decide +kernel
#print axioms leaf00626_raw
theorem leaf00626_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00626=true := by decide +kernel
#print axioms leaf00626_rectangular
def affine00626 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00626 (IntegerComputedClassCell.leftNumerator ![(7/320),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/320),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/320),0,(1/16)] ![(3/6400),1,(1/16)]))
theorem leaf00626_transform : affine00626=(NestedInteger.clearedAll 3 raw00626 (IntegerComputedClassCell.leftNumerator ![(7/320),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/320),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/320),0,(1/16)] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00626_transform
theorem leaf00626_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00626=true := by decide +kernel
#print axioms leaf00626_sign
theorem leaf00626_log : RationalLog.accepts (448027703/2147483648) (-420691247/536870912) 3 8=true := by decide +kernel
#print axioms leaf00626_log
def leaf00626 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (21306646959/40000000000) (448027703/2147483648) (-420691247/536870912) 3 8 ![60,0,4] ![(7/320),0,(1/16)] ![(3/6400),1,(1/16)] affine00626
theorem leaf00626_checked : FastNestedCellData.accepts 1 2 4 leaf00626=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (21306646959/40000000000) (448027703/2147483648) (-420691247/536870912) 3 8 ![60,0,4] ![(7/320),0,(1/16)] ![(3/6400),1,(1/16)] 3930382635215548897882999357440000000000 1256774638293101606861595038302511038464 2359403881261074227501297827840000000000 raw00626 affine00626
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00626_raw leaf00626_rectangular
    leaf00626_transform leaf00626_sign leaf00626_log
#print axioms leaf00626_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
