/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2390 : Family 9 := level9.get ⟨517,by decide⟩
def sourceMap2390 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2390 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2390_checked : acceptsGraphIso
    (source (graph core2390) (root 9) 0 4) DegreeTwoThreeSpectrum4607.graph sourceMap2390=true := by decide +kernel
theorem fusedMap2390_checked : acceptsGraphIso
    (fused (graph core2390) (root 9) 0 4) DegreeTwoThreeSpectrum4608.graph fusedMap2390=true := by decide +kernel
theorem certified2390 : Certified (graph core2390) (root 9) 0 4 :=
  of_native_maps core2390 DegreeTwoThreeSpectrum4607.graph DegreeTwoThreeSpectrum4608.graph
    sourceMap2390 fusedMap2390 sourceMap2390_checked fusedMap2390_checked
    DegreeTwoThreeFiniteComparisons.comparison2390
#print axioms sourceMap2390_checked
#print axioms fusedMap2390_checked
#print axioms certified2390
def sourceMap2390swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2390swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2390swap_checked : acceptsGraphIso
    (source (graph core2390) (root 9) 4 0) DegreeTwoThreeSpectrum4607.graph sourceMap2390swap=true := by decide +kernel
theorem fusedMap2390swap_checked : acceptsGraphIso
    (fused (graph core2390) (root 9) 4 0) DegreeTwoThreeSpectrum4608.graph fusedMap2390swap=true := by decide +kernel
theorem certified2390swap : Certified (graph core2390) (root 9) 4 0 :=
  of_native_maps core2390 DegreeTwoThreeSpectrum4607.graph DegreeTwoThreeSpectrum4608.graph
    sourceMap2390swap fusedMap2390swap sourceMap2390swap_checked fusedMap2390swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2390
#print axioms sourceMap2390swap_checked
#print axioms fusedMap2390swap_checked
#print axioms certified2390swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
