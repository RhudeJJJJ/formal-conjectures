/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00364 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 149950958032390055931016118272000000000000 139090609475200030205900552537783933075456 4277680032379450657458662408192000000000000))
theorem leaf00364_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 149950958032390055931016118272000000000000 139090609475200030205900552537783933075456 4277680032379450657458662408192000000000000 raw00364=true := by decide +kernel
#print axioms leaf00364_raw
theorem leaf00364_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00364=true := by decide +kernel
#print axioms leaf00364_rectangular
def affine00364 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00364 (IntegerComputedClassCell.leftNumerator ![(7/800),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/800),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/800),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00364_transform : affine00364=(NestedInteger.clearedAll 3 raw00364 (IntegerComputedClassCell.leftNumerator ![(7/800),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/800),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/800),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00364_transform
theorem leaf00364_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00364=true := by decide +kernel
#print axioms leaf00364_sign
theorem leaf00364_log : RationalLog.accepts (1929220553/2147483648) (-230168831/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00364_log
def leaf00364 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (32515430893/1000000000000) (1929220553/2147483648) (-230168831/4294967296) 1 8 ![60,0,4] ![(7/800),0,(1/2)] ![(1/6400),1,(1/2)] affine00364
theorem leaf00364_checked : FastNestedCellData.accepts 1 2 4 leaf00364=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (32515430893/1000000000000) (1929220553/2147483648) (-230168831/4294967296) 1 8 ![60,0,4] ![(7/800),0,(1/2)] ![(1/6400),1,(1/2)] 149950958032390055931016118272000000000000 139090609475200030205900552537783933075456 4277680032379450657458662408192000000000000 raw00364 affine00364
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00364_raw leaf00364_rectangular
    leaf00364_transform leaf00364_sign leaf00364_log
#print axioms leaf00364_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
