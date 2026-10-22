/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5178 : Family 8 := level8.get ⟨180,by decide⟩
def sourceMap5178 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5178 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5178_checked : acceptsGraphIso
    (source (graph core5178) (root 8) 2 4) DegreeTwoThreeSpectrum7005.graph sourceMap5178=true := by decide +kernel
theorem fusedMap5178_checked : acceptsGraphIso
    (fused (graph core5178) (root 8) 2 4) DegreeTwoThreeSpectrum5825.graph fusedMap5178=true := by decide +kernel
theorem certified5178 : Certified (graph core5178) (root 8) 2 4 :=
  of_native_maps core5178 DegreeTwoThreeSpectrum7005.graph DegreeTwoThreeSpectrum5825.graph
    sourceMap5178 fusedMap5178 sourceMap5178_checked fusedMap5178_checked
    DegreeTwoThreeFiniteComparisons.comparison5178
#print axioms sourceMap5178_checked
#print axioms fusedMap5178_checked
#print axioms certified5178
def sourceMap5178swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,14,15,16,9,10,11] (sourceLabel 8 4 2 v)
def fusedMap5178swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5178swap_checked : acceptsGraphIso
    (source (graph core5178) (root 8) 4 2) DegreeTwoThreeSpectrum7005.graph sourceMap5178swap=true := by decide +kernel
theorem fusedMap5178swap_checked : acceptsGraphIso
    (fused (graph core5178) (root 8) 4 2) DegreeTwoThreeSpectrum5825.graph fusedMap5178swap=true := by decide +kernel
theorem certified5178swap : Certified (graph core5178) (root 8) 4 2 :=
  of_native_maps core5178 DegreeTwoThreeSpectrum7005.graph DegreeTwoThreeSpectrum5825.graph
    sourceMap5178swap fusedMap5178swap sourceMap5178swap_checked fusedMap5178swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5178
#print axioms sourceMap5178swap_checked
#print axioms fusedMap5178swap_checked
#print axioms certified5178swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
