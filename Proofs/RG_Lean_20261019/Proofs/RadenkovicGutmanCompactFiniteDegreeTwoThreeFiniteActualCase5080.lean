/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5080 : Family 6 := level6.get ⟨39,by decide⟩
def sourceMap5080 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,5,6,7,8,9,10,2,3,4,0,11,12,13,14] (sourceLabel 6 2 4 v)
def fusedMap5080 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14] (fusedLabel 6 2 4 v)
theorem sourceMap5080_checked : acceptsGraphIso
    (source (graph core5080) (root 6) 2 4) DegreeTwoThreeSpectrum3641.graph sourceMap5080=true := by decide +kernel
theorem fusedMap5080_checked : acceptsGraphIso
    (fused (graph core5080) (root 6) 2 4) DegreeTwoThreeSpectrum2459.graph fusedMap5080=true := by decide +kernel
theorem certified5080 : Certified (graph core5080) (root 6) 2 4 :=
  of_native_maps core5080 DegreeTwoThreeSpectrum3641.graph DegreeTwoThreeSpectrum2459.graph
    sourceMap5080 fusedMap5080 sourceMap5080_checked fusedMap5080_checked
    DegreeTwoThreeFiniteComparisons.comparison5080
#print axioms sourceMap5080_checked
#print axioms fusedMap5080_checked
#print axioms certified5080
def sourceMap5080swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,5,6,7,8,9,10,0,11,12,13,14,2,3,4] (sourceLabel 6 4 2 v)
def fusedMap5080swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14] (fusedLabel 6 4 2 v)
theorem sourceMap5080swap_checked : acceptsGraphIso
    (source (graph core5080) (root 6) 4 2) DegreeTwoThreeSpectrum3641.graph sourceMap5080swap=true := by decide +kernel
theorem fusedMap5080swap_checked : acceptsGraphIso
    (fused (graph core5080) (root 6) 4 2) DegreeTwoThreeSpectrum2459.graph fusedMap5080swap=true := by decide +kernel
theorem certified5080swap : Certified (graph core5080) (root 6) 4 2 :=
  of_native_maps core5080 DegreeTwoThreeSpectrum3641.graph DegreeTwoThreeSpectrum2459.graph
    sourceMap5080swap fusedMap5080swap sourceMap5080swap_checked fusedMap5080swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5080
#print axioms sourceMap5080swap_checked
#print axioms fusedMap5080swap_checked
#print axioms certified5080swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
