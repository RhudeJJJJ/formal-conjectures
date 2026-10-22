/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00462 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 6649053081044607284924280471552000000000 4486372051111681945720419708751614836736 24893456568194110880246398976000000000000))
theorem leaf00462_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 6649053081044607284924280471552000000000 4486372051111681945720419708751614836736 24893456568194110880246398976000000000000 raw00462=true := by decide +kernel
#print axioms leaf00462_raw
theorem leaf00462_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00462=true := by decide +kernel
#print axioms leaf00462_rectangular
def affine00462 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00462 (IntegerComputedClassCell.leftNumerator ![(19/1600),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(19/1600),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(19/1600),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00462_transform : affine00462=(NestedInteger.clearedAll 3 raw00462 (IntegerComputedClassCell.leftNumerator ![(19/1600),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(19/1600),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(19/1600),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00462_transform
theorem leaf00462_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00462=true := by decide +kernel
#print axioms leaf00462_sign
theorem leaf00462_log : RationalLog.accepts (2455451125/4294967296) (-1200729953/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00462_log
def leaf00462 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (90111472443/500000000000) (2455451125/4294967296) (-1200729953/4294967296) 1 8 ![60,0,4] ![(19/1600),0,(1/8)] ![(1/6400),1,(1/8)] affine00462
theorem leaf00462_checked : FastNestedCellData.accepts 1 2 4 leaf00462=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (90111472443/500000000000) (2455451125/4294967296) (-1200729953/4294967296) 1 8 ![60,0,4] ![(19/1600),0,(1/8)] ![(1/6400),1,(1/8)] 6649053081044607284924280471552000000000 4486372051111681945720419708751614836736 24893456568194110880246398976000000000000 raw00462 affine00462
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00462_raw leaf00462_rectangular
    leaf00462_transform leaf00462_sign leaf00462_log
#print axioms leaf00462_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
