/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5161 : Family 8 := level8.get ⟨143,by decide⟩
def sourceMap5161 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,11,8,9,10,12,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5161 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5161_checked : acceptsGraphIso
    (source (graph core5161) (root 8) 2 4) DegreeTwoThreeSpectrum6612.graph sourceMap5161=true := by decide +kernel
theorem fusedMap5161_checked : acceptsGraphIso
    (fused (graph core5161) (root 8) 2 4) DegreeTwoThreeSpectrum5493.graph fusedMap5161=true := by decide +kernel
theorem certified5161 : Certified (graph core5161) (root 8) 2 4 :=
  of_native_maps core5161 DegreeTwoThreeSpectrum6612.graph DegreeTwoThreeSpectrum5493.graph
    sourceMap5161 fusedMap5161 sourceMap5161_checked fusedMap5161_checked
    DegreeTwoThreeFiniteComparisons.comparison5161
#print axioms sourceMap5161_checked
#print axioms fusedMap5161_checked
#print axioms certified5161
def sourceMap5161swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,14,15,16,8,9,10] (sourceLabel 8 4 2 v)
def fusedMap5161swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5161swap_checked : acceptsGraphIso
    (source (graph core5161) (root 8) 4 2) DegreeTwoThreeSpectrum6612.graph sourceMap5161swap=true := by decide +kernel
theorem fusedMap5161swap_checked : acceptsGraphIso
    (fused (graph core5161) (root 8) 4 2) DegreeTwoThreeSpectrum5493.graph fusedMap5161swap=true := by decide +kernel
theorem certified5161swap : Certified (graph core5161) (root 8) 4 2 :=
  of_native_maps core5161 DegreeTwoThreeSpectrum6612.graph DegreeTwoThreeSpectrum5493.graph
    sourceMap5161swap fusedMap5161swap sourceMap5161swap_checked fusedMap5161swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5161
#print axioms sourceMap5161swap_checked
#print axioms fusedMap5161swap_checked
#print axioms certified5161swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
