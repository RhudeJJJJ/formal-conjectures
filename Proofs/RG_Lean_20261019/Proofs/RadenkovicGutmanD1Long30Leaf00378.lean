/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00378 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 4054536554789805867317749350400000000000 3457984910026966257510341054199094050816 49164498969263135528218263552000000000000))
theorem leaf00378_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 4054536554789805867317749350400000000000 3457984910026966257510341054199094050816 49164498969263135528218263552000000000000 raw00378=true := by decide +kernel
#print axioms leaf00378_raw
theorem leaf00378_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00378=true := by decide +kernel
#print axioms leaf00378_rectangular
def affine00378 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00378 (IntegerComputedClassCell.leftNumerator ![(59/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(59/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(59/6400),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00378_transform : affine00378=(NestedInteger.clearedAll 3 raw00378 (IntegerComputedClassCell.leftNumerator ![(59/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(59/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(59/6400),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00378_transform
theorem leaf00378_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00378=true := by decide +kernel
#print axioms leaf00378_sign
theorem leaf00378_log : RationalLog.accepts (855582745/1073741824) (-243870461/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00378_log
def leaf00378 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (35167498729/500000000000) (855582745/1073741824) (-243870461/2147483648) 1 8 ![60,0,4] ![(59/6400),0,(1/4)] ![(1/6400),1,(1/4)] affine00378
theorem leaf00378_checked : FastNestedCellData.accepts 1 2 4 leaf00378=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (35167498729/500000000000) (855582745/1073741824) (-243870461/2147483648) 1 8 ![60,0,4] ![(59/6400),0,(1/4)] ![(1/6400),1,(1/4)] 4054536554789805867317749350400000000000 3457984910026966257510341054199094050816 49164498969263135528218263552000000000000 raw00378 affine00378
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00378_raw leaf00378_rectangular
    leaf00378_transform leaf00378_sign leaf00378_log
#print axioms leaf00378_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
