/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00295 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 9599479055803496724820918272000000000000 12193812943037275615451276399704276992 22882929837026084676173824000000000000))
theorem leaf00295_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 9599479055803496724820918272000000000000 12193812943037275615451276399704276992 22882929837026084676173824000000000000 raw00295=true := by decide +kernel
#print axioms leaf00295_raw
theorem leaf00295_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00295=true := by decide +kernel
#print axioms leaf00295_rectangular
def affine00295 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00295 (IntegerComputedClassCell.leftNumerator ![(43/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(43/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(43/6400),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00295_transform : affine00295=(NestedInteger.clearedAll 3 raw00295 (IntegerComputedClassCell.leftNumerator ![(43/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(43/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(43/6400),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00295_transform
theorem leaf00295_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00295=true := by decide +kernel
#print axioms leaf00295_sign
theorem leaf00295_log : RationalLog.accepts (889783/1073741824) (-7618931291/2147483648) 11 8=true := by decide +kernel
#print axioms leaf00295_log
def leaf00295 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (66609766701/125000000000) (889783/1073741824) (-7618931291/2147483648) 11 8 ![60,0,4] ![(43/6400),0,0] ![(1/6400),1,(1/16)] affine00295
theorem leaf00295_checked : FastNestedCellData.accepts 1 2 4 leaf00295=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (66609766701/125000000000) (889783/1073741824) (-7618931291/2147483648) 11 8 ![60,0,4] ![(43/6400),0,0] ![(1/6400),1,(1/16)] 9599479055803496724820918272000000000000 12193812943037275615451276399704276992 22882929837026084676173824000000000000 raw00295 affine00295
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00295_raw leaf00295_rectangular
    leaf00295_transform leaf00295_sign leaf00295_log
#print axioms leaf00295_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
