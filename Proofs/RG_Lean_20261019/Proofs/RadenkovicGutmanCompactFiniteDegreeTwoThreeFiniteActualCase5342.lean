/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5342 : Family 6 := level6.get ⟨24,by decide⟩
def sourceMap5342 : (Vertices 6 ⊕ Fin 4 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,5,6,7,8,9,10,1,2,3,4,11,12,13,14,15] (sourceLabel 6 3 4 v)
def fusedMap5342 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 3 4 v)
theorem sourceMap5342_checked : acceptsGraphIso
    (source (graph core5342) (root 6) 3 4) DegreeTwoThreeSpectrum4630.graph sourceMap5342=true := by decide +kernel
theorem fusedMap5342_checked : acceptsGraphIso
    (fused (graph core5342) (root 6) 3 4) DegreeTwoThreeSpectrum3931.graph fusedMap5342=true := by decide +kernel
theorem certified5342 : Certified (graph core5342) (root 6) 3 4 :=
  of_native_maps core5342 DegreeTwoThreeSpectrum4630.graph DegreeTwoThreeSpectrum3931.graph
    sourceMap5342 fusedMap5342 sourceMap5342_checked fusedMap5342_checked
    DegreeTwoThreeFiniteComparisons.comparison5342
#print axioms sourceMap5342_checked
#print axioms fusedMap5342_checked
#print axioms certified5342
def sourceMap5342swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 4) → Fin 16 :=
  fun v => ![0,5,6,7,8,9,10,11,12,13,14,15,1,2,3,4] (sourceLabel 6 4 3 v)
def fusedMap5342swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 4 3 v)
theorem sourceMap5342swap_checked : acceptsGraphIso
    (source (graph core5342) (root 6) 4 3) DegreeTwoThreeSpectrum4630.graph sourceMap5342swap=true := by decide +kernel
theorem fusedMap5342swap_checked : acceptsGraphIso
    (fused (graph core5342) (root 6) 4 3) DegreeTwoThreeSpectrum3931.graph fusedMap5342swap=true := by decide +kernel
theorem certified5342swap : Certified (graph core5342) (root 6) 4 3 :=
  of_native_maps core5342 DegreeTwoThreeSpectrum4630.graph DegreeTwoThreeSpectrum3931.graph
    sourceMap5342swap fusedMap5342swap sourceMap5342swap_checked fusedMap5342swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5342
#print axioms sourceMap5342swap_checked
#print axioms fusedMap5342swap_checked
#print axioms certified5342swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
