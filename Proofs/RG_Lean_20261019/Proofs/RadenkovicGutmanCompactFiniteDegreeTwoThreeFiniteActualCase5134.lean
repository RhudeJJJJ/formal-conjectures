/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5134 : Family 8 := level8.get ⟨67,by decide⟩
def sourceMap5134 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,16,13,14,15,8,9,10,11,12] (sourceLabel 8 2 4 v)
def fusedMap5134 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5134_checked : acceptsGraphIso
    (source (graph core5134) (root 8) 2 4) DegreeTwoThreeSpectrum6779.graph sourceMap5134=true := by decide +kernel
theorem fusedMap5134_checked : acceptsGraphIso
    (fused (graph core5134) (root 8) 2 4) DegreeTwoThreeSpectrum5030.graph fusedMap5134=true := by decide +kernel
theorem certified5134 : Certified (graph core5134) (root 8) 2 4 :=
  of_native_maps core5134 DegreeTwoThreeSpectrum6779.graph DegreeTwoThreeSpectrum5030.graph
    sourceMap5134 fusedMap5134 sourceMap5134_checked fusedMap5134_checked
    DegreeTwoThreeFiniteComparisons.comparison5134
#print axioms sourceMap5134_checked
#print axioms fusedMap5134_checked
#print axioms certified5134
def sourceMap5134swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,16,8,9,10,11,12,13,14,15] (sourceLabel 8 4 2 v)
def fusedMap5134swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5134swap_checked : acceptsGraphIso
    (source (graph core5134) (root 8) 4 2) DegreeTwoThreeSpectrum6779.graph sourceMap5134swap=true := by decide +kernel
theorem fusedMap5134swap_checked : acceptsGraphIso
    (fused (graph core5134) (root 8) 4 2) DegreeTwoThreeSpectrum5030.graph fusedMap5134swap=true := by decide +kernel
theorem certified5134swap : Certified (graph core5134) (root 8) 4 2 :=
  of_native_maps core5134 DegreeTwoThreeSpectrum6779.graph DegreeTwoThreeSpectrum5030.graph
    sourceMap5134swap fusedMap5134swap sourceMap5134swap_checked fusedMap5134swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5134
#print axioms sourceMap5134swap_checked
#print axioms fusedMap5134swap_checked
#print axioms certified5134swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
