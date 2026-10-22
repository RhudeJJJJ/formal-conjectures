/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5193 : Family 8 := level8.get ⟨216,by decide⟩
def sourceMap5193 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,11,12,8,9,10,0,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5193 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5193_checked : acceptsGraphIso
    (source (graph core5193) (root 8) 2 4) DegreeTwoThreeSpectrum7218.graph sourceMap5193=true := by decide +kernel
theorem fusedMap5193_checked : acceptsGraphIso
    (fused (graph core5193) (root 8) 2 4) DegreeTwoThreeSpectrum5250.graph fusedMap5193=true := by decide +kernel
theorem certified5193 : Certified (graph core5193) (root 8) 2 4 :=
  of_native_maps core5193 DegreeTwoThreeSpectrum7218.graph DegreeTwoThreeSpectrum5250.graph
    sourceMap5193 fusedMap5193 sourceMap5193_checked fusedMap5193_checked
    DegreeTwoThreeFiniteComparisons.comparison5193
#print axioms sourceMap5193_checked
#print axioms fusedMap5193_checked
#print axioms certified5193
def sourceMap5193swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,11,12,0,13,14,15,16,8,9,10] (sourceLabel 8 4 2 v)
def fusedMap5193swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5193swap_checked : acceptsGraphIso
    (source (graph core5193) (root 8) 4 2) DegreeTwoThreeSpectrum7218.graph sourceMap5193swap=true := by decide +kernel
theorem fusedMap5193swap_checked : acceptsGraphIso
    (fused (graph core5193) (root 8) 4 2) DegreeTwoThreeSpectrum5250.graph fusedMap5193swap=true := by decide +kernel
theorem certified5193swap : Certified (graph core5193) (root 8) 4 2 :=
  of_native_maps core5193 DegreeTwoThreeSpectrum7218.graph DegreeTwoThreeSpectrum5250.graph
    sourceMap5193swap fusedMap5193swap sourceMap5193swap_checked fusedMap5193swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5193
#print axioms sourceMap5193swap_checked
#print axioms fusedMap5193swap_checked
#print axioms certified5193swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
