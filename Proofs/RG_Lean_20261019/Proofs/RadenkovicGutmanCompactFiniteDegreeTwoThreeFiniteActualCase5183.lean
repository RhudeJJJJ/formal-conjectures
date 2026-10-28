/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5183 : Family 8 := level8.get ⟨194,by decide⟩
def sourceMap5183 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,11,12,8,9,10,0,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5183 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5183_checked : acceptsGraphIso
    (source (graph core5183) (root 8) 2 4) DegreeTwoThreeSpectrum7099.graph sourceMap5183=true := by decide +kernel
theorem fusedMap5183_checked : acceptsGraphIso
    (fused (graph core5183) (root 8) 2 4) DegreeTwoThreeSpectrum5145.graph fusedMap5183=true := by decide +kernel
theorem certified5183 : Certified (graph core5183) (root 8) 2 4 :=
  of_native_maps core5183 DegreeTwoThreeSpectrum7099.graph DegreeTwoThreeSpectrum5145.graph
    sourceMap5183 fusedMap5183 sourceMap5183_checked fusedMap5183_checked
    DegreeTwoThreeFiniteComparisons.comparison5183
#print axioms sourceMap5183_checked
#print axioms fusedMap5183_checked
#print axioms certified5183
def sourceMap5183swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,11,12,0,13,14,15,16,8,9,10] (sourceLabel 8 4 2 v)
def fusedMap5183swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5183swap_checked : acceptsGraphIso
    (source (graph core5183) (root 8) 4 2) DegreeTwoThreeSpectrum7099.graph sourceMap5183swap=true := by decide +kernel
theorem fusedMap5183swap_checked : acceptsGraphIso
    (fused (graph core5183) (root 8) 4 2) DegreeTwoThreeSpectrum5145.graph fusedMap5183swap=true := by decide +kernel
theorem certified5183swap : Certified (graph core5183) (root 8) 4 2 :=
  of_native_maps core5183 DegreeTwoThreeSpectrum7099.graph DegreeTwoThreeSpectrum5145.graph
    sourceMap5183swap fusedMap5183swap sourceMap5183swap_checked fusedMap5183swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5183
#print axioms sourceMap5183swap_checked
#print axioms fusedMap5183swap_checked
#print axioms certified5183swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
