/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00133 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 22702224937046122364002736537600000000000 17237169437164293760195195682669677510656 140061009017519738970009344409600000000000))
theorem leaf00133_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 22702224937046122364002736537600000000000 17237169437164293760195195682669677510656 140061009017519738970009344409600000000000 raw00133=true := by decide +kernel
#print axioms leaf00133_raw
theorem leaf00133_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00133=true := by decide +kernel
#print axioms leaf00133_rectangular
def affine00133 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00133 (IntegerComputedClassCell.leftNumerator ![(13/800),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/800),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/800),0,(1/4)] ![(1/1600),1,(1/4)]))
theorem leaf00133_transform : affine00133=(NestedInteger.clearedAll 3 raw00133 (IntegerComputedClassCell.leftNumerator ![(13/800),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/800),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/800),0,(1/4)] ![(1/1600),1,(1/4)])) := by decide +kernel
#print axioms leaf00133_transform
theorem leaf00133_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00133=true := by decide +kernel
#print axioms leaf00133_sign
theorem leaf00133_log : RationalLog.accepts (1451847333/2147483648) (-52540873/268435456) 1 8=true := by decide +kernel
#print axioms leaf00133_log
def leaf00133 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (24613801597/200000000000) (1451847333/2147483648) (-52540873/268435456) 1 8 ![52,0,4] ![(13/800),0,(1/4)] ![(1/1600),1,(1/4)] affine00133
theorem leaf00133_checked : FastNestedCellData.accepts 1 0 4 leaf00133=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (24613801597/200000000000) (1451847333/2147483648) (-52540873/268435456) 1 8 ![52,0,4] ![(13/800),0,(1/4)] ![(1/1600),1,(1/4)] 22702224937046122364002736537600000000000 17237169437164293760195195682669677510656 140061009017519738970009344409600000000000 raw00133 affine00133
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00133_raw leaf00133_rectangular
    leaf00133_transform leaf00133_sign leaf00133_log
#print axioms leaf00133_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
