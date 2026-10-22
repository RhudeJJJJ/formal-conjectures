/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5413 : Family 4 := level4.get ⟨6,by decide⟩
def sourceMap5413 : (Vertices 4 ⊕ Fin 5 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,7,8,9,10,2,3,4,5,6,0,11,12,13,14,15,16] (sourceLabel 4 4 6 v)
def fusedMap5413 : (Vertices 4 ⊕ Fin 12) → Fin 17 :=
  fun v => ![5,6,7,8,9,4,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 4 4 6 v)
theorem sourceMap5413_checked : acceptsGraphIso
    (source (graph core5413) (root 4) 4 6) DegreeTwoThreeSpectrum5936.graph sourceMap5413=true := by decide +kernel
theorem fusedMap5413_checked : acceptsGraphIso
    (fused (graph core5413) (root 4) 4 6) DegreeTwoThreeSpectrum5014.graph fusedMap5413=true := by decide +kernel
theorem certified5413 : Certified (graph core5413) (root 4) 4 6 :=
  of_native_maps core5413 DegreeTwoThreeSpectrum5936.graph DegreeTwoThreeSpectrum5014.graph
    sourceMap5413 fusedMap5413 sourceMap5413_checked fusedMap5413_checked
    DegreeTwoThreeFiniteComparisons.comparison5413
#print axioms sourceMap5413_checked
#print axioms fusedMap5413_checked
#print axioms certified5413
def sourceMap5413swap : (Vertices 4 ⊕ Fin 7 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,7,8,9,10,0,11,12,13,14,15,16,2,3,4,5,6] (sourceLabel 4 6 4 v)
def fusedMap5413swap : (Vertices 4 ⊕ Fin 12) → Fin 17 :=
  fun v => ![5,6,7,8,9,4,3,2,1,0,10,11,12,13,14,15,16] (fusedLabel 4 6 4 v)
theorem sourceMap5413swap_checked : acceptsGraphIso
    (source (graph core5413) (root 4) 6 4) DegreeTwoThreeSpectrum5936.graph sourceMap5413swap=true := by decide +kernel
theorem fusedMap5413swap_checked : acceptsGraphIso
    (fused (graph core5413) (root 4) 6 4) DegreeTwoThreeSpectrum5014.graph fusedMap5413swap=true := by decide +kernel
theorem certified5413swap : Certified (graph core5413) (root 4) 6 4 :=
  of_native_maps core5413 DegreeTwoThreeSpectrum5936.graph DegreeTwoThreeSpectrum5014.graph
    sourceMap5413swap fusedMap5413swap sourceMap5413swap_checked fusedMap5413swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5413
#print axioms sourceMap5413swap_checked
#print axioms fusedMap5413swap_checked
#print axioms certified5413swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
