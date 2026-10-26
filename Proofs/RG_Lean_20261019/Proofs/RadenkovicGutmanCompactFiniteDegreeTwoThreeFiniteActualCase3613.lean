/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3613 : Family 8 := level8.get ⟨216,by decide⟩
def sourceMap3613 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3613 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3613_checked : acceptsGraphIso
    (source (graph core3613) (root 8) 0 6) DegreeTwoThreeSpectrum6261.graph sourceMap3613=true := by decide +kernel
theorem fusedMap3613_checked : acceptsGraphIso
    (fused (graph core3613) (root 8) 0 6) DegreeTwoThreeSpectrum5250.graph fusedMap3613=true := by decide +kernel
theorem certified3613 : Certified (graph core3613) (root 8) 0 6 :=
  of_native_maps core3613 DegreeTwoThreeSpectrum6261.graph DegreeTwoThreeSpectrum5250.graph
    sourceMap3613 fusedMap3613 sourceMap3613_checked fusedMap3613_checked
    DegreeTwoThreeFiniteComparisons.comparison3613
#print axioms sourceMap3613_checked
#print axioms fusedMap3613_checked
#print axioms certified3613
def sourceMap3613swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,12,13,14,15,16,11] (sourceLabel 8 6 0 v)
def fusedMap3613swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3613swap_checked : acceptsGraphIso
    (source (graph core3613) (root 8) 6 0) DegreeTwoThreeSpectrum6261.graph sourceMap3613swap=true := by decide +kernel
theorem fusedMap3613swap_checked : acceptsGraphIso
    (fused (graph core3613) (root 8) 6 0) DegreeTwoThreeSpectrum5250.graph fusedMap3613swap=true := by decide +kernel
theorem certified3613swap : Certified (graph core3613) (root 8) 6 0 :=
  of_native_maps core3613 DegreeTwoThreeSpectrum6261.graph DegreeTwoThreeSpectrum5250.graph
    sourceMap3613swap fusedMap3613swap sourceMap3613swap_checked fusedMap3613swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3613
#print axioms sourceMap3613swap_checked
#print axioms fusedMap3613swap_checked
#print axioms certified3613swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
