/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5177 : Family 8 := level8.get ⟨179,by decide⟩
def sourceMap5177 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5177 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5177_checked : acceptsGraphIso
    (source (graph core5177) (root 8) 2 4) DegreeTwoThreeSpectrum6993.graph sourceMap5177=true := by decide +kernel
theorem fusedMap5177_checked : acceptsGraphIso
    (fused (graph core5177) (root 8) 2 4) DegreeTwoThreeSpectrum5820.graph fusedMap5177=true := by decide +kernel
theorem certified5177 : Certified (graph core5177) (root 8) 2 4 :=
  of_native_maps core5177 DegreeTwoThreeSpectrum6993.graph DegreeTwoThreeSpectrum5820.graph
    sourceMap5177 fusedMap5177 sourceMap5177_checked fusedMap5177_checked
    DegreeTwoThreeFiniteComparisons.comparison5177
#print axioms sourceMap5177_checked
#print axioms fusedMap5177_checked
#print axioms certified5177
def sourceMap5177swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,14,15,16,9,10,11] (sourceLabel 8 4 2 v)
def fusedMap5177swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5177swap_checked : acceptsGraphIso
    (source (graph core5177) (root 8) 4 2) DegreeTwoThreeSpectrum6993.graph sourceMap5177swap=true := by decide +kernel
theorem fusedMap5177swap_checked : acceptsGraphIso
    (fused (graph core5177) (root 8) 4 2) DegreeTwoThreeSpectrum5820.graph fusedMap5177swap=true := by decide +kernel
theorem certified5177swap : Certified (graph core5177) (root 8) 4 2 :=
  of_native_maps core5177 DegreeTwoThreeSpectrum6993.graph DegreeTwoThreeSpectrum5820.graph
    sourceMap5177swap fusedMap5177swap sourceMap5177swap_checked fusedMap5177swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5177
#print axioms sourceMap5177swap_checked
#print axioms fusedMap5177swap_checked
#print axioms certified5177swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
