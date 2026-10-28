/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5189 : Family 8 := level8.get ⟨208,by decide⟩
def sourceMap5189 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,12,9,10,11,0,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5189 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5189_checked : acceptsGraphIso
    (source (graph core5189) (root 8) 2 4) DegreeTwoThreeSpectrum7178.graph sourceMap5189=true := by decide +kernel
theorem fusedMap5189_checked : acceptsGraphIso
    (fused (graph core5189) (root 8) 2 4) DegreeTwoThreeSpectrum5225.graph fusedMap5189=true := by decide +kernel
theorem certified5189 : Certified (graph core5189) (root 8) 2 4 :=
  of_native_maps core5189 DegreeTwoThreeSpectrum7178.graph DegreeTwoThreeSpectrum5225.graph
    sourceMap5189 fusedMap5189 sourceMap5189_checked fusedMap5189_checked
    DegreeTwoThreeFiniteComparisons.comparison5189
#print axioms sourceMap5189_checked
#print axioms fusedMap5189_checked
#print axioms certified5189
def sourceMap5189swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,12,0,13,14,15,16,9,10,11] (sourceLabel 8 4 2 v)
def fusedMap5189swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5189swap_checked : acceptsGraphIso
    (source (graph core5189) (root 8) 4 2) DegreeTwoThreeSpectrum7178.graph sourceMap5189swap=true := by decide +kernel
theorem fusedMap5189swap_checked : acceptsGraphIso
    (fused (graph core5189) (root 8) 4 2) DegreeTwoThreeSpectrum5225.graph fusedMap5189swap=true := by decide +kernel
theorem certified5189swap : Certified (graph core5189) (root 8) 4 2 :=
  of_native_maps core5189 DegreeTwoThreeSpectrum7178.graph DegreeTwoThreeSpectrum5225.graph
    sourceMap5189swap fusedMap5189swap sourceMap5189swap_checked fusedMap5189swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5189
#print axioms sourceMap5189swap_checked
#print axioms fusedMap5189swap_checked
#print axioms certified5189swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
