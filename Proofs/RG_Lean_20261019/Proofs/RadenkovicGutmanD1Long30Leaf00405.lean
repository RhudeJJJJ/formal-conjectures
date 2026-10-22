/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00405 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3037681757274539625935798272000000000000 10205094285392448578915002609708302336 15129846538700619773902848000000000000))
theorem leaf00405_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3037681757274539625935798272000000000000 10205094285392448578915002609708302336 15129846538700619773902848000000000000 raw00405=true := by decide +kernel
#print axioms leaf00405_raw
theorem leaf00405_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00405=true := by decide +kernel
#print axioms leaf00405_rectangular
def affine00405 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00405 (IntegerComputedClassCell.leftNumerator ![(13/1280),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/1280),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/1280),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00405_transform : affine00405=(NestedInteger.clearedAll 3 raw00405 (IntegerComputedClassCell.leftNumerator ![(13/1280),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/1280),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/1280),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00405_transform
theorem leaf00405_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00405=true := by decide +kernel
#print axioms leaf00405_sign
theorem leaf00405_log : RationalLog.accepts (269277/134217728) (-13339047767/4294967296) 9 8=true := by decide +kernel
#print axioms leaf00405_log
def leaf00405 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (337250422841/500000000000) (269277/134217728) (-13339047767/4294967296) 9 8 ![60,0,4] ![(13/1280),0,0] ![(1/6400),1,(1/16)] affine00405
theorem leaf00405_checked : FastNestedCellData.accepts 1 2 4 leaf00405=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (337250422841/500000000000) (269277/134217728) (-13339047767/4294967296) 9 8 ![60,0,4] ![(13/1280),0,0] ![(1/6400),1,(1/16)] 3037681757274539625935798272000000000000 10205094285392448578915002609708302336 15129846538700619773902848000000000000 raw00405 affine00405
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00405_raw leaf00405_rectangular
    leaf00405_transform leaf00405_sign leaf00405_log
#print axioms leaf00405_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
