/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5198 : Family 8 := level8.get ⟨225,by decide⟩
def sourceMap5198 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,9,10,11,12,6,7,8,0,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5198 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5198_checked : acceptsGraphIso
    (source (graph core5198) (root 8) 2 4) DegreeTwoThreeSpectrum7274.graph sourceMap5198=true := by decide +kernel
theorem fusedMap5198_checked : acceptsGraphIso
    (fused (graph core5198) (root 8) 2 4) DegreeTwoThreeSpectrum5311.graph fusedMap5198=true := by decide +kernel
theorem certified5198 : Certified (graph core5198) (root 8) 2 4 :=
  of_native_maps core5198 DegreeTwoThreeSpectrum7274.graph DegreeTwoThreeSpectrum5311.graph
    sourceMap5198 fusedMap5198 sourceMap5198_checked fusedMap5198_checked
    DegreeTwoThreeFiniteComparisons.comparison5198
#print axioms sourceMap5198_checked
#print axioms fusedMap5198_checked
#print axioms certified5198
def sourceMap5198swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,9,10,11,12,0,13,14,15,16,6,7,8] (sourceLabel 8 4 2 v)
def fusedMap5198swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5198swap_checked : acceptsGraphIso
    (source (graph core5198) (root 8) 4 2) DegreeTwoThreeSpectrum7274.graph sourceMap5198swap=true := by decide +kernel
theorem fusedMap5198swap_checked : acceptsGraphIso
    (fused (graph core5198) (root 8) 4 2) DegreeTwoThreeSpectrum5311.graph fusedMap5198swap=true := by decide +kernel
theorem certified5198swap : Certified (graph core5198) (root 8) 4 2 :=
  of_native_maps core5198 DegreeTwoThreeSpectrum7274.graph DegreeTwoThreeSpectrum5311.graph
    sourceMap5198swap fusedMap5198swap sourceMap5198swap_checked fusedMap5198swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5198
#print axioms sourceMap5198swap_checked
#print axioms fusedMap5198swap_checked
#print axioms certified5198swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
