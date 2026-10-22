/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5306 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap5306 : (Vertices 2 ⊕ Fin 3 ⊕ Fin 8) → Fin 14 :=
  fun v => ![2,6,7,3,4,5,1,0,8,9,10,11,12,13] (sourceLabel 2 2 7 v)
def fusedMap5306 : (Vertices 2 ⊕ Fin 11) → Fin 14 :=
  fun v => ![5,6,7,4,3,2,1,0,8,9,10,11,12,13] (fusedLabel 2 2 7 v)
theorem sourceMap5306_checked : acceptsGraphIso
    (source (graph core5306) (root 2) 2 7) DegreeTwoThreeSpectrum1724.graph sourceMap5306=true := by decide +kernel
theorem fusedMap5306_checked : acceptsGraphIso
    (fused (graph core5306) (root 2) 2 7) DegreeTwoThreeSpectrum1715.graph fusedMap5306=true := by decide +kernel
theorem certified5306 : Certified (graph core5306) (root 2) 2 7 :=
  of_native_maps core5306 DegreeTwoThreeSpectrum1724.graph DegreeTwoThreeSpectrum1715.graph
    sourceMap5306 fusedMap5306 sourceMap5306_checked fusedMap5306_checked
    DegreeTwoThreeFiniteComparisons.comparison5306
#print axioms sourceMap5306_checked
#print axioms fusedMap5306_checked
#print axioms certified5306
def sourceMap5306swap : (Vertices 2 ⊕ Fin 8 ⊕ Fin 3) → Fin 14 :=
  fun v => ![2,6,7,1,0,8,9,10,11,12,13,3,4,5] (sourceLabel 2 7 2 v)
def fusedMap5306swap : (Vertices 2 ⊕ Fin 11) → Fin 14 :=
  fun v => ![5,6,7,4,3,2,1,0,8,9,10,11,12,13] (fusedLabel 2 7 2 v)
theorem sourceMap5306swap_checked : acceptsGraphIso
    (source (graph core5306) (root 2) 7 2) DegreeTwoThreeSpectrum1724.graph sourceMap5306swap=true := by decide +kernel
theorem fusedMap5306swap_checked : acceptsGraphIso
    (fused (graph core5306) (root 2) 7 2) DegreeTwoThreeSpectrum1715.graph fusedMap5306swap=true := by decide +kernel
theorem certified5306swap : Certified (graph core5306) (root 2) 7 2 :=
  of_native_maps core5306 DegreeTwoThreeSpectrum1724.graph DegreeTwoThreeSpectrum1715.graph
    sourceMap5306swap fusedMap5306swap sourceMap5306swap_checked fusedMap5306swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5306
#print axioms sourceMap5306swap_checked
#print axioms fusedMap5306swap_checked
#print axioms certified5306swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
