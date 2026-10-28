/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5131 : Family 8 := level8.get ⟨56,by decide⟩
def sourceMap5131 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,16,13,14,15,8,9,10,11,12] (sourceLabel 8 2 4 v)
def fusedMap5131 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5131_checked : acceptsGraphIso
    (source (graph core5131) (root 8) 2 4) DegreeTwoThreeSpectrum6578.graph sourceMap5131=true := by decide +kernel
theorem fusedMap5131_checked : acceptsGraphIso
    (fused (graph core5131) (root 8) 2 4) DegreeTwoThreeSpectrum5011.graph fusedMap5131=true := by decide +kernel
theorem certified5131 : Certified (graph core5131) (root 8) 2 4 :=
  of_native_maps core5131 DegreeTwoThreeSpectrum6578.graph DegreeTwoThreeSpectrum5011.graph
    sourceMap5131 fusedMap5131 sourceMap5131_checked fusedMap5131_checked
    DegreeTwoThreeFiniteComparisons.comparison5131
#print axioms sourceMap5131_checked
#print axioms fusedMap5131_checked
#print axioms certified5131
def sourceMap5131swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,16,8,9,10,11,12,13,14,15] (sourceLabel 8 4 2 v)
def fusedMap5131swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5131swap_checked : acceptsGraphIso
    (source (graph core5131) (root 8) 4 2) DegreeTwoThreeSpectrum6578.graph sourceMap5131swap=true := by decide +kernel
theorem fusedMap5131swap_checked : acceptsGraphIso
    (fused (graph core5131) (root 8) 4 2) DegreeTwoThreeSpectrum5011.graph fusedMap5131swap=true := by decide +kernel
theorem certified5131swap : Certified (graph core5131) (root 8) 4 2 :=
  of_native_maps core5131 DegreeTwoThreeSpectrum6578.graph DegreeTwoThreeSpectrum5011.graph
    sourceMap5131swap fusedMap5131swap sourceMap5131swap_checked fusedMap5131swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5131
#print axioms sourceMap5131swap_checked
#print axioms fusedMap5131swap_checked
#print axioms certified5131swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
