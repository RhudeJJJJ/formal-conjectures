/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5295 : Family 6 := level6.get ⟨21,by decide⟩
def sourceMap5295 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,11,8,9,10,1,0,12,13,14,15,16] (sourceLabel 6 2 6 v)
def fusedMap5295 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 2 6 v)
theorem sourceMap5295_checked : acceptsGraphIso
    (source (graph core5295) (root 6) 2 6) DegreeTwoThreeSpectrum6123.graph sourceMap5295=true := by decide +kernel
theorem fusedMap5295_checked : acceptsGraphIso
    (fused (graph core5295) (root 6) 2 6) DegreeTwoThreeSpectrum4967.graph fusedMap5295=true := by decide +kernel
theorem certified5295 : Certified (graph core5295) (root 6) 2 6 :=
  of_native_maps core5295 DegreeTwoThreeSpectrum6123.graph DegreeTwoThreeSpectrum4967.graph
    sourceMap5295 fusedMap5295 sourceMap5295_checked fusedMap5295_checked
    DegreeTwoThreeFiniteComparisons.comparison5295
#print axioms sourceMap5295_checked
#print axioms fusedMap5295_checked
#print axioms certified5295
def sourceMap5295swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,11,1,0,12,13,14,15,16,8,9,10] (sourceLabel 6 6 2 v)
def fusedMap5295swap : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 6 2 v)
theorem sourceMap5295swap_checked : acceptsGraphIso
    (source (graph core5295) (root 6) 6 2) DegreeTwoThreeSpectrum6123.graph sourceMap5295swap=true := by decide +kernel
theorem fusedMap5295swap_checked : acceptsGraphIso
    (fused (graph core5295) (root 6) 6 2) DegreeTwoThreeSpectrum4967.graph fusedMap5295swap=true := by decide +kernel
theorem certified5295swap : Certified (graph core5295) (root 6) 6 2 :=
  of_native_maps core5295 DegreeTwoThreeSpectrum6123.graph DegreeTwoThreeSpectrum4967.graph
    sourceMap5295swap fusedMap5295swap sourceMap5295swap_checked fusedMap5295swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5295
#print axioms sourceMap5295swap_checked
#print axioms fusedMap5295swap_checked
#print axioms certified5295swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
