/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5452 : Family 7 := level7.get ⟨103,by decide⟩
def sourceMap5452 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,5,6,7,8,9,1,2,3,4] (sourceLabel 7 0 0 v)
def fusedMap5452 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,8,9,6,7] (fusedLabel 7 0 0 v)
theorem sourceMap5452_checked : acceptsGraphIso
    (source (graph core5452) (root 7) 0 0) DegreeTwoThreeSpectrum140.graph sourceMap5452=true := by decide +kernel
theorem fusedMap5452_checked : acceptsGraphIso
    (fused (graph core5452) (root 7) 0 0) DegreeTwoThreeSpectrum144.graph fusedMap5452=true := by decide +kernel
theorem certified5452 : Certified (graph core5452) (root 7) 0 0 :=
  of_native_maps core5452 DegreeTwoThreeSpectrum140.graph DegreeTwoThreeSpectrum144.graph
    sourceMap5452 fusedMap5452 sourceMap5452_checked fusedMap5452_checked
    DegreeTwoThreeFiniteComparisons.comparison5452
#print axioms sourceMap5452_checked
#print axioms fusedMap5452_checked
#print axioms certified5452
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
