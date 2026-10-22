/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5064 : Family 5 := level5.get ⟨14,by decide⟩
def sourceMap5064 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 5) → Fin 14 :=
  fun v => ![1,5,6,7,8,9,2,3,4,0,10,11,12,13] (sourceLabel 5 2 4 v)
def fusedMap5064 : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13] (fusedLabel 5 2 4 v)
theorem sourceMap5064_checked : acceptsGraphIso
    (source (graph core5064) (root 5) 2 4) DegreeTwoThreeSpectrum2193.graph sourceMap5064=true := by decide +kernel
theorem fusedMap5064_checked : acceptsGraphIso
    (fused (graph core5064) (root 5) 2 4) DegreeTwoThreeSpectrum1746.graph fusedMap5064=true := by decide +kernel
theorem certified5064 : Certified (graph core5064) (root 5) 2 4 :=
  of_native_maps core5064 DegreeTwoThreeSpectrum2193.graph DegreeTwoThreeSpectrum1746.graph
    sourceMap5064 fusedMap5064 sourceMap5064_checked fusedMap5064_checked
    DegreeTwoThreeFiniteComparisons.comparison5064
#print axioms sourceMap5064_checked
#print axioms fusedMap5064_checked
#print axioms certified5064
def sourceMap5064swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,5,6,7,8,9,0,10,11,12,13,2,3,4] (sourceLabel 5 4 2 v)
def fusedMap5064swap : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13] (fusedLabel 5 4 2 v)
theorem sourceMap5064swap_checked : acceptsGraphIso
    (source (graph core5064) (root 5) 4 2) DegreeTwoThreeSpectrum2193.graph sourceMap5064swap=true := by decide +kernel
theorem fusedMap5064swap_checked : acceptsGraphIso
    (fused (graph core5064) (root 5) 4 2) DegreeTwoThreeSpectrum1746.graph fusedMap5064swap=true := by decide +kernel
theorem certified5064swap : Certified (graph core5064) (root 5) 4 2 :=
  of_native_maps core5064 DegreeTwoThreeSpectrum2193.graph DegreeTwoThreeSpectrum1746.graph
    sourceMap5064swap fusedMap5064swap sourceMap5064swap_checked fusedMap5064swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5064
#print axioms sourceMap5064swap_checked
#print axioms fusedMap5064swap_checked
#print axioms certified5064swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
