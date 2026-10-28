/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5300 : Family 6 := level6.get ⟨31,by decide⟩
def sourceMap5300 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,10,11,7,8,9,1,0,12,13,14,15,16] (sourceLabel 6 2 6 v)
def fusedMap5300 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 2 6 v)
theorem sourceMap5300_checked : acceptsGraphIso
    (source (graph core5300) (root 6) 2 6) DegreeTwoThreeSpectrum6678.graph sourceMap5300=true := by decide +kernel
theorem fusedMap5300_checked : acceptsGraphIso
    (fused (graph core5300) (root 6) 2 6) DegreeTwoThreeSpectrum5021.graph fusedMap5300=true := by decide +kernel
theorem certified5300 : Certified (graph core5300) (root 6) 2 6 :=
  of_native_maps core5300 DegreeTwoThreeSpectrum6678.graph DegreeTwoThreeSpectrum5021.graph
    sourceMap5300 fusedMap5300 sourceMap5300_checked fusedMap5300_checked
    DegreeTwoThreeFiniteComparisons.comparison5300
#print axioms sourceMap5300_checked
#print axioms fusedMap5300_checked
#print axioms certified5300
def sourceMap5300swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,3,4,5,6,10,11,1,0,12,13,14,15,16,7,8,9] (sourceLabel 6 6 2 v)
def fusedMap5300swap : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 6 2 v)
theorem sourceMap5300swap_checked : acceptsGraphIso
    (source (graph core5300) (root 6) 6 2) DegreeTwoThreeSpectrum6678.graph sourceMap5300swap=true := by decide +kernel
theorem fusedMap5300swap_checked : acceptsGraphIso
    (fused (graph core5300) (root 6) 6 2) DegreeTwoThreeSpectrum5021.graph fusedMap5300swap=true := by decide +kernel
theorem certified5300swap : Certified (graph core5300) (root 6) 6 2 :=
  of_native_maps core5300 DegreeTwoThreeSpectrum6678.graph DegreeTwoThreeSpectrum5021.graph
    sourceMap5300swap fusedMap5300swap sourceMap5300swap_checked fusedMap5300swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5300
#print axioms sourceMap5300swap_checked
#print axioms fusedMap5300swap_checked
#print axioms certified5300swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
