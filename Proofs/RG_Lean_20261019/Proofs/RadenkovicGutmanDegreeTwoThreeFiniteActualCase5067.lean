/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5067 : Family 6 := level6.get ⟨9,by decide⟩
def sourceMap5067 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,9,6,7,8,10,11,12,13,14] (sourceLabel 6 2 4 v)
def fusedMap5067 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 2 4 v)
theorem sourceMap5067_checked : acceptsGraphIso
    (source (graph core5067) (root 6) 2 4) DegreeTwoThreeSpectrum2603.graph sourceMap5067=true := by decide +kernel
theorem fusedMap5067_checked : acceptsGraphIso
    (fused (graph core5067) (root 6) 2 4) DegreeTwoThreeSpectrum2338.graph fusedMap5067=true := by decide +kernel
theorem certified5067 : Certified (graph core5067) (root 6) 2 4 :=
  of_native_maps core5067 DegreeTwoThreeSpectrum2603.graph DegreeTwoThreeSpectrum2338.graph
    sourceMap5067 fusedMap5067 sourceMap5067_checked fusedMap5067_checked
    DegreeTwoThreeFiniteComparisons.comparison5067
#print axioms sourceMap5067_checked
#print axioms fusedMap5067_checked
#print axioms certified5067
def sourceMap5067swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,9,10,11,12,13,14,6,7,8] (sourceLabel 6 4 2 v)
def fusedMap5067swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 4 2 v)
theorem sourceMap5067swap_checked : acceptsGraphIso
    (source (graph core5067) (root 6) 4 2) DegreeTwoThreeSpectrum2603.graph sourceMap5067swap=true := by decide +kernel
theorem fusedMap5067swap_checked : acceptsGraphIso
    (fused (graph core5067) (root 6) 4 2) DegreeTwoThreeSpectrum2338.graph fusedMap5067swap=true := by decide +kernel
theorem certified5067swap : Certified (graph core5067) (root 6) 4 2 :=
  of_native_maps core5067 DegreeTwoThreeSpectrum2603.graph DegreeTwoThreeSpectrum2338.graph
    sourceMap5067swap fusedMap5067swap sourceMap5067swap_checked fusedMap5067swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5067
#print axioms sourceMap5067swap_checked
#print axioms fusedMap5067swap_checked
#print axioms certified5067swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
