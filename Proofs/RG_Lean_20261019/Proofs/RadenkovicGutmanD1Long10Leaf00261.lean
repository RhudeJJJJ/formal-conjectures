/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00261 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 498060490476668611091521286963200000000000 37052495814780799696885226353693678370816 54892762678952049158214857523200000000000))
theorem leaf00261_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 498060490476668611091521286963200000000000 37052495814780799696885226353693678370816 54892762678952049158214857523200000000000 raw00261=true := by decide +kernel
#print axioms leaf00261_raw
theorem leaf00261_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00261=true := by decide +kernel
#print axioms leaf00261_rectangular
def affine00261 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00261 (IntegerComputedClassCell.leftNumerator ![(7/128),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/128),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/128),0,0] ![(1/640),1,(1/4)]))
theorem leaf00261_transform : affine00261=(NestedInteger.clearedAll 3 raw00261 (IntegerComputedClassCell.leftNumerator ![(7/128),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/128),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/128),0,0] ![(1/640),1,(1/4)])) := by decide +kernel
#print axioms leaf00261_transform
theorem leaf00261_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00261=true := by decide +kernel
#print axioms leaf00261_sign
theorem leaf00261_log : RationalLog.accepts (190757221/4294967296) (-6687688803/4294967296) 5 8=true := by decide +kernel
#print axioms leaf00261_log
def leaf00261 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (134999566451/200000000000) (190757221/4294967296) (-6687688803/4294967296) 5 8 ![52,0,4] ![(7/128),0,0] ![(1/640),1,(1/4)] affine00261
theorem leaf00261_checked : FastNestedCellData.accepts 1 0 4 leaf00261=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (134999566451/200000000000) (190757221/4294967296) (-6687688803/4294967296) 5 8 ![52,0,4] ![(7/128),0,0] ![(1/640),1,(1/4)] 498060490476668611091521286963200000000000 37052495814780799696885226353693678370816 54892762678952049158214857523200000000000 raw00261 affine00261
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00261_raw leaf00261_rectangular
    leaf00261_transform leaf00261_sign leaf00261_log
#print axioms leaf00261_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
