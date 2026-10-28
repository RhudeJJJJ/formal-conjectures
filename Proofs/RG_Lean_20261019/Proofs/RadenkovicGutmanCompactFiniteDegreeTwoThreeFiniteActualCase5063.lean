/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5063 : Family 5 := level5.get ⟨11,by decide⟩
def sourceMap5063 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 5) → Fin 14 :=
  fun v => ![1,2,3,4,8,9,5,6,7,0,10,11,12,13] (sourceLabel 5 2 4 v)
def fusedMap5063 : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13] (fusedLabel 5 2 4 v)
theorem sourceMap5063_checked : acceptsGraphIso
    (source (graph core5063) (root 5) 2 4) DegreeTwoThreeSpectrum2182.graph sourceMap5063=true := by decide +kernel
theorem fusedMap5063_checked : acceptsGraphIso
    (fused (graph core5063) (root 5) 2 4) DegreeTwoThreeSpectrum1723.graph fusedMap5063=true := by decide +kernel
theorem certified5063 : Certified (graph core5063) (root 5) 2 4 :=
  of_native_maps core5063 DegreeTwoThreeSpectrum2182.graph DegreeTwoThreeSpectrum1723.graph
    sourceMap5063 fusedMap5063 sourceMap5063_checked fusedMap5063_checked
    DegreeTwoThreeFiniteComparisons.comparison5063
#print axioms sourceMap5063_checked
#print axioms fusedMap5063_checked
#print axioms certified5063
def sourceMap5063swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,2,3,4,8,9,0,10,11,12,13,5,6,7] (sourceLabel 5 4 2 v)
def fusedMap5063swap : (Vertices 5 ⊕ Fin 8) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13] (fusedLabel 5 4 2 v)
theorem sourceMap5063swap_checked : acceptsGraphIso
    (source (graph core5063) (root 5) 4 2) DegreeTwoThreeSpectrum2182.graph sourceMap5063swap=true := by decide +kernel
theorem fusedMap5063swap_checked : acceptsGraphIso
    (fused (graph core5063) (root 5) 4 2) DegreeTwoThreeSpectrum1723.graph fusedMap5063swap=true := by decide +kernel
theorem certified5063swap : Certified (graph core5063) (root 5) 4 2 :=
  of_native_maps core5063 DegreeTwoThreeSpectrum2182.graph DegreeTwoThreeSpectrum1723.graph
    sourceMap5063swap fusedMap5063swap sourceMap5063swap_checked fusedMap5063swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5063
#print axioms sourceMap5063swap_checked
#print axioms fusedMap5063swap_checked
#print axioms certified5063swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
