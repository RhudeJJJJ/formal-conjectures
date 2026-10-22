/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00186 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 959377355715367483984199024640000000000 16847723851371655857064303585640054784 32394515907564372507974696960000000000))
theorem leaf00186_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 959377355715367483984199024640000000000 16847723851371655857064303585640054784 32394515907564372507974696960000000000 raw00186=true := by decide +kernel
#print axioms leaf00186_raw
theorem leaf00186_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00186=true := by decide +kernel
#print axioms leaf00186_rectangular
def affine00186 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00186 (IntegerComputedClassCell.leftNumerator ![(91/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(91/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(91/3200),0,0] ![(3/3200),1,(1/4)]))
theorem leaf00186_transform : affine00186=(NestedInteger.clearedAll 3 raw00186 (IntegerComputedClassCell.leftNumerator ![(91/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(91/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(91/3200),0,0] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00186_transform
theorem leaf00186_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00186=true := by decide +kernel
#print axioms leaf00186_sign
theorem leaf00186_log : RationalLog.accepts (24809347/2147483648) (-9579563083/4294967296) 7 8=true := by decide +kernel
#print axioms leaf00186_log
def leaf00186 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (10401590133/20000000000) (24809347/2147483648) (-9579563083/4294967296) 7 8 ![52,0,4] ![(91/3200),0,0] ![(3/3200),1,(1/4)] affine00186
theorem leaf00186_checked : FastNestedCellData.accepts 1 0 4 leaf00186=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (10401590133/20000000000) (24809347/2147483648) (-9579563083/4294967296) 7 8 ![52,0,4] ![(91/3200),0,0] ![(3/3200),1,(1/4)] 959377355715367483984199024640000000000 16847723851371655857064303585640054784 32394515907564372507974696960000000000 raw00186 affine00186
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00186_raw leaf00186_rectangular
    leaf00186_transform leaf00186_sign leaf00186_log
#print axioms leaf00186_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
