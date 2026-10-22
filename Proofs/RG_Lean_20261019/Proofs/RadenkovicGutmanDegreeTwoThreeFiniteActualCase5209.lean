/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5209 : Family 8 := level8.get ⟨250,by decide⟩
def sourceMap5209 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,9,10,11,12,6,7,8,0,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5209 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5209_checked : acceptsGraphIso
    (source (graph core5209) (root 8) 2 4) DegreeTwoThreeSpectrum7432.graph sourceMap5209=true := by decide +kernel
theorem fusedMap5209_checked : acceptsGraphIso
    (fused (graph core5209) (root 8) 2 4) DegreeTwoThreeSpectrum5545.graph fusedMap5209=true := by decide +kernel
theorem certified5209 : Certified (graph core5209) (root 8) 2 4 :=
  of_native_maps core5209 DegreeTwoThreeSpectrum7432.graph DegreeTwoThreeSpectrum5545.graph
    sourceMap5209 fusedMap5209 sourceMap5209_checked fusedMap5209_checked
    DegreeTwoThreeFiniteComparisons.comparison5209
#print axioms sourceMap5209_checked
#print axioms fusedMap5209_checked
#print axioms certified5209
def sourceMap5209swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,9,10,11,12,0,13,14,15,16,6,7,8] (sourceLabel 8 4 2 v)
def fusedMap5209swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5209swap_checked : acceptsGraphIso
    (source (graph core5209) (root 8) 4 2) DegreeTwoThreeSpectrum7432.graph sourceMap5209swap=true := by decide +kernel
theorem fusedMap5209swap_checked : acceptsGraphIso
    (fused (graph core5209) (root 8) 4 2) DegreeTwoThreeSpectrum5545.graph fusedMap5209swap=true := by decide +kernel
theorem certified5209swap : Certified (graph core5209) (root 8) 4 2 :=
  of_native_maps core5209 DegreeTwoThreeSpectrum7432.graph DegreeTwoThreeSpectrum5545.graph
    sourceMap5209swap fusedMap5209swap sourceMap5209swap_checked fusedMap5209swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5209
#print axioms sourceMap5209swap_checked
#print axioms fusedMap5209swap_checked
#print axioms certified5209swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
