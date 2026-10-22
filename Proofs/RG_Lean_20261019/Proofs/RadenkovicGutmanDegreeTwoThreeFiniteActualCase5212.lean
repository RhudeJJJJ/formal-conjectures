/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5212 : Family 8 := level8.get ⟨266,by decide⟩
def sourceMap5212 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,5,6,7,8,9,10,11,12,2,3,4,0,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5212 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,11,2,1,0,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5212_checked : acceptsGraphIso
    (source (graph core5212) (root 8) 2 4) DegreeTwoThreeSpectrum7554.graph sourceMap5212=true := by decide +kernel
theorem fusedMap5212_checked : acceptsGraphIso
    (fused (graph core5212) (root 8) 2 4) DegreeTwoThreeSpectrum5974.graph fusedMap5212=true := by decide +kernel
theorem certified5212 : Certified (graph core5212) (root 8) 2 4 :=
  of_native_maps core5212 DegreeTwoThreeSpectrum7554.graph DegreeTwoThreeSpectrum5974.graph
    sourceMap5212 fusedMap5212 sourceMap5212_checked fusedMap5212_checked
    DegreeTwoThreeFiniteComparisons.comparison5212
#print axioms sourceMap5212_checked
#print axioms fusedMap5212_checked
#print axioms certified5212
def sourceMap5212swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,5,6,7,8,9,10,11,12,0,13,14,15,16,2,3,4] (sourceLabel 8 4 2 v)
def fusedMap5212swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,11,2,1,0,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5212swap_checked : acceptsGraphIso
    (source (graph core5212) (root 8) 4 2) DegreeTwoThreeSpectrum7554.graph sourceMap5212swap=true := by decide +kernel
theorem fusedMap5212swap_checked : acceptsGraphIso
    (fused (graph core5212) (root 8) 4 2) DegreeTwoThreeSpectrum5974.graph fusedMap5212swap=true := by decide +kernel
theorem certified5212swap : Certified (graph core5212) (root 8) 4 2 :=
  of_native_maps core5212 DegreeTwoThreeSpectrum7554.graph DegreeTwoThreeSpectrum5974.graph
    sourceMap5212swap fusedMap5212swap sourceMap5212swap_checked fusedMap5212swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5212
#print axioms sourceMap5212swap_checked
#print axioms fusedMap5212swap_checked
#print axioms certified5212swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
