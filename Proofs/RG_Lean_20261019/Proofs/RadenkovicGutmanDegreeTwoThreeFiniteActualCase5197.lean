/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5197 : Family 8 := level8.get ⟨223,by decide⟩
def sourceMap5197 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5197 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5197_checked : acceptsGraphIso
    (source (graph core5197) (root 8) 2 4) DegreeTwoThreeSpectrum7262.graph sourceMap5197=true := by decide +kernel
theorem fusedMap5197_checked : acceptsGraphIso
    (fused (graph core5197) (root 8) 2 4) DegreeTwoThreeSpectrum5306.graph fusedMap5197=true := by decide +kernel
theorem certified5197 : Certified (graph core5197) (root 8) 2 4 :=
  of_native_maps core5197 DegreeTwoThreeSpectrum7262.graph DegreeTwoThreeSpectrum5306.graph
    sourceMap5197 fusedMap5197 sourceMap5197_checked fusedMap5197_checked
    DegreeTwoThreeFiniteComparisons.comparison5197
#print axioms sourceMap5197_checked
#print axioms fusedMap5197_checked
#print axioms certified5197
def sourceMap5197swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,13,14,15,16,10,11,12] (sourceLabel 8 4 2 v)
def fusedMap5197swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5197swap_checked : acceptsGraphIso
    (source (graph core5197) (root 8) 4 2) DegreeTwoThreeSpectrum7262.graph sourceMap5197swap=true := by decide +kernel
theorem fusedMap5197swap_checked : acceptsGraphIso
    (fused (graph core5197) (root 8) 4 2) DegreeTwoThreeSpectrum5306.graph fusedMap5197swap=true := by decide +kernel
theorem certified5197swap : Certified (graph core5197) (root 8) 4 2 :=
  of_native_maps core5197 DegreeTwoThreeSpectrum7262.graph DegreeTwoThreeSpectrum5306.graph
    sourceMap5197swap fusedMap5197swap sourceMap5197swap_checked fusedMap5197swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5197
#print axioms sourceMap5197swap_checked
#print axioms fusedMap5197swap_checked
#print axioms certified5197swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
