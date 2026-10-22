/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00357 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2390798326918301046775218176000000000000 1778869759051918771850631432651631755264 13403585059946597665499774976000000000000))
theorem leaf00357_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2390798326918301046775218176000000000000 1778869759051918771850631432651631755264 13403585059946597665499774976000000000000 raw00357=true := by decide +kernel
#print axioms leaf00357_raw
theorem leaf00357_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00357=true := by decide +kernel
#print axioms leaf00357_rectangular
def affine00357 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00357 (IntegerComputedClassCell.leftNumerator ![(11/1280),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(11/1280),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(11/1280),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00357_transform : affine00357=(NestedInteger.clearedAll 3 raw00357 (IntegerComputedClassCell.leftNumerator ![(11/1280),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(11/1280),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(11/1280),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00357_transform
theorem leaf00357_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00357=true := by decide +kernel
#print axioms leaf00357_sign
theorem leaf00357_log : RationalLog.accepts (88163753/134217728) (-451258705/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00357_log
def leaf00357 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (132715967489/1000000000000) (88163753/134217728) (-451258705/2147483648) 1 8 ![60,0,4] ![(11/1280),0,(1/8)] ![(1/6400),1,(1/8)] affine00357
theorem leaf00357_checked : FastNestedCellData.accepts 1 2 4 leaf00357=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (132715967489/1000000000000) (88163753/134217728) (-451258705/2147483648) 1 8 ![60,0,4] ![(11/1280),0,(1/8)] ![(1/6400),1,(1/8)] 2390798326918301046775218176000000000000 1778869759051918771850631432651631755264 13403585059946597665499774976000000000000 raw00357 affine00357
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00357_raw leaf00357_rectangular
    leaf00357_transform leaf00357_sign leaf00357_log
#print axioms leaf00357_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
