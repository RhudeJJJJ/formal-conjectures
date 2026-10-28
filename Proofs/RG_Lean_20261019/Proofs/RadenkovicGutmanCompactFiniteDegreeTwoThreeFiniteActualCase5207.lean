/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5207 : Family 8 := level8.get ⟨245,by decide⟩
def sourceMap5207 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,10,11,12,7,8,9,0,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5207 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5207_checked : acceptsGraphIso
    (source (graph core5207) (root 8) 2 4) DegreeTwoThreeSpectrum7402.graph sourceMap5207=true := by decide +kernel
theorem fusedMap5207_checked : acceptsGraphIso
    (fused (graph core5207) (root 8) 2 4) DegreeTwoThreeSpectrum5500.graph fusedMap5207=true := by decide +kernel
theorem certified5207 : Certified (graph core5207) (root 8) 2 4 :=
  of_native_maps core5207 DegreeTwoThreeSpectrum7402.graph DegreeTwoThreeSpectrum5500.graph
    sourceMap5207 fusedMap5207 sourceMap5207_checked fusedMap5207_checked
    DegreeTwoThreeFiniteComparisons.comparison5207
#print axioms sourceMap5207_checked
#print axioms fusedMap5207_checked
#print axioms certified5207
def sourceMap5207swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,10,11,12,0,13,14,15,16,7,8,9] (sourceLabel 8 4 2 v)
def fusedMap5207swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5207swap_checked : acceptsGraphIso
    (source (graph core5207) (root 8) 4 2) DegreeTwoThreeSpectrum7402.graph sourceMap5207swap=true := by decide +kernel
theorem fusedMap5207swap_checked : acceptsGraphIso
    (fused (graph core5207) (root 8) 4 2) DegreeTwoThreeSpectrum5500.graph fusedMap5207swap=true := by decide +kernel
theorem certified5207swap : Certified (graph core5207) (root 8) 4 2 :=
  of_native_maps core5207 DegreeTwoThreeSpectrum7402.graph DegreeTwoThreeSpectrum5500.graph
    sourceMap5207swap fusedMap5207swap sourceMap5207swap_checked fusedMap5207swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5207
#print axioms sourceMap5207swap_checked
#print axioms fusedMap5207swap_checked
#print axioms certified5207swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
