/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00468 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1681745933675831902250035314688000000000000 1372754274650171234301104935279309411581952 15057474659810090729267594788864000000000000))
theorem leaf00468_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1681745933675831902250035314688000000000000 1372754274650171234301104935279309411581952 15057474659810090729267594788864000000000000 raw00468=true := by decide +kernel
#print axioms leaf00468_raw
theorem leaf00468_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00468=true := by decide +kernel
#print axioms leaf00468_rectangular
def affine00468 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00468 (IntegerComputedClassCell.leftNumerator ![(77/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(77/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(77/6400),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00468_transform : affine00468=(NestedInteger.clearedAll 3 raw00468 (IntegerComputedClassCell.leftNumerator ![(77/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(77/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(77/6400),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00468_transform
theorem leaf00468_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00468=true := by decide +kernel
#print axioms leaf00468_sign
theorem leaf00468_log : RationalLog.accepts (3212926613/4294967296) (-311666147/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00468_log
def leaf00468 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (91167629743/1000000000000) (3212926613/4294967296) (-311666147/2147483648) 1 8 ![60,0,4] ![(77/6400),0,(1/4)] ![(1/6400),1,(1/4)] affine00468
theorem leaf00468_checked : FastNestedCellData.accepts 1 2 4 leaf00468=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (91167629743/1000000000000) (3212926613/4294967296) (-311666147/2147483648) 1 8 ![60,0,4] ![(77/6400),0,(1/4)] ![(1/6400),1,(1/4)] 1681745933675831902250035314688000000000000 1372754274650171234301104935279309411581952 15057474659810090729267594788864000000000000 raw00468 affine00468
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00468_raw leaf00468_rectangular
    leaf00468_transform leaf00468_sign leaf00468_log
#print axioms leaf00468_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
