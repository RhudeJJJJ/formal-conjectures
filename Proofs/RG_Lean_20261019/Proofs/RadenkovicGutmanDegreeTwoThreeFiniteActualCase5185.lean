/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5185 : Family 8 := level8.get ⟨200,by decide⟩
def sourceMap5185 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,12,9,10,11,0,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5185 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5185_checked : acceptsGraphIso
    (source (graph core5185) (root 8) 2 4) DegreeTwoThreeSpectrum7125.graph sourceMap5185=true := by decide +kernel
theorem fusedMap5185_checked : acceptsGraphIso
    (fused (graph core5185) (root 8) 2 4) DegreeTwoThreeSpectrum5165.graph fusedMap5185=true := by decide +kernel
theorem certified5185 : Certified (graph core5185) (root 8) 2 4 :=
  of_native_maps core5185 DegreeTwoThreeSpectrum7125.graph DegreeTwoThreeSpectrum5165.graph
    sourceMap5185 fusedMap5185 sourceMap5185_checked fusedMap5185_checked
    DegreeTwoThreeFiniteComparisons.comparison5185
#print axioms sourceMap5185_checked
#print axioms fusedMap5185_checked
#print axioms certified5185
def sourceMap5185swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,12,0,13,14,15,16,9,10,11] (sourceLabel 8 4 2 v)
def fusedMap5185swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5185swap_checked : acceptsGraphIso
    (source (graph core5185) (root 8) 4 2) DegreeTwoThreeSpectrum7125.graph sourceMap5185swap=true := by decide +kernel
theorem fusedMap5185swap_checked : acceptsGraphIso
    (fused (graph core5185) (root 8) 4 2) DegreeTwoThreeSpectrum5165.graph fusedMap5185swap=true := by decide +kernel
theorem certified5185swap : Certified (graph core5185) (root 8) 4 2 :=
  of_native_maps core5185 DegreeTwoThreeSpectrum7125.graph DegreeTwoThreeSpectrum5165.graph
    sourceMap5185swap fusedMap5185swap sourceMap5185swap_checked fusedMap5185swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5185
#print axioms sourceMap5185swap_checked
#print axioms fusedMap5185swap_checked
#print axioms certified5185swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
