/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5203 : Family 8 := level8.get ⟨237,by decide⟩
def sourceMap5203 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,10,11,12,7,8,9,0,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5203 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5203_checked : acceptsGraphIso
    (source (graph core5203) (root 8) 2 4) DegreeTwoThreeSpectrum7356.graph sourceMap5203=true := by decide +kernel
theorem fusedMap5203_checked : acceptsGraphIso
    (fused (graph core5203) (root 8) 2 4) DegreeTwoThreeSpectrum5442.graph fusedMap5203=true := by decide +kernel
theorem certified5203 : Certified (graph core5203) (root 8) 2 4 :=
  of_native_maps core5203 DegreeTwoThreeSpectrum7356.graph DegreeTwoThreeSpectrum5442.graph
    sourceMap5203 fusedMap5203 sourceMap5203_checked fusedMap5203_checked
    DegreeTwoThreeFiniteComparisons.comparison5203
#print axioms sourceMap5203_checked
#print axioms fusedMap5203_checked
#print axioms certified5203
def sourceMap5203swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,10,11,12,0,13,14,15,16,7,8,9] (sourceLabel 8 4 2 v)
def fusedMap5203swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5203swap_checked : acceptsGraphIso
    (source (graph core5203) (root 8) 4 2) DegreeTwoThreeSpectrum7356.graph sourceMap5203swap=true := by decide +kernel
theorem fusedMap5203swap_checked : acceptsGraphIso
    (fused (graph core5203) (root 8) 4 2) DegreeTwoThreeSpectrum5442.graph fusedMap5203swap=true := by decide +kernel
theorem certified5203swap : Certified (graph core5203) (root 8) 4 2 :=
  of_native_maps core5203 DegreeTwoThreeSpectrum7356.graph DegreeTwoThreeSpectrum5442.graph
    sourceMap5203swap fusedMap5203swap sourceMap5203swap_checked fusedMap5203swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5203
#print axioms sourceMap5203swap_checked
#print axioms fusedMap5203swap_checked
#print axioms certified5203swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
