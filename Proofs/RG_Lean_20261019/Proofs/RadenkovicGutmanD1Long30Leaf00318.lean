/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00318 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1038426869998780218476735758336000000000000 912817853856334176417493263319826247450624 16215409888247964252916515078144000000000000))
theorem leaf00318_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1038426869998780218476735758336000000000000 912817853856334176417493263319826247450624 16215409888247964252916515078144000000000000 raw00318=true := by decide +kernel
#print axioms leaf00318_raw
theorem leaf00318_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00318=true := by decide +kernel
#print axioms leaf00318_rectangular
def affine00318 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00318 (IntegerComputedClassCell.leftNumerator ![(47/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(47/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(47/6400),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00318_transform : affine00318=(NestedInteger.clearedAll 3 raw00318 (IntegerComputedClassCell.leftNumerator ![(47/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(47/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(47/6400),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00318_transform
theorem leaf00318_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00318=true := by decide +kernel
#print axioms leaf00318_sign
theorem leaf00318_log : RationalLog.accepts (3574238859/4294967296) (-394474945/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00318_log
def leaf00318 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (56293233421/1000000000000) (3574238859/4294967296) (-394474945/4294967296) 1 8 ![60,0,4] ![(47/6400),0,(1/4)] ![(1/6400),1,(1/4)] affine00318
theorem leaf00318_checked : FastNestedCellData.accepts 1 2 4 leaf00318=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (56293233421/1000000000000) (3574238859/4294967296) (-394474945/4294967296) 1 8 ![60,0,4] ![(47/6400),0,(1/4)] ![(1/6400),1,(1/4)] 1038426869998780218476735758336000000000000 912817853856334176417493263319826247450624 16215409888247964252916515078144000000000000 raw00318 affine00318
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00318_raw leaf00318_rectangular
    leaf00318_transform leaf00318_sign leaf00318_log
#print axioms leaf00318_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
