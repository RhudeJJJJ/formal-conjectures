/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3094 : Family 6 := level6.get ⟨25,by decide⟩
def sourceMap3094 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (sourceLabel 6 0 5 v)
def fusedMap3094 : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 0 5 v)
theorem sourceMap3094_checked : acceptsGraphIso
    (source (graph core3094) (root 6) 0 5) DegreeTwoThreeSpectrum1777.graph sourceMap3094=true := by decide +kernel
theorem fusedMap3094_checked : acceptsGraphIso
    (fused (graph core3094) (root 6) 0 5) DegreeTwoThreeSpectrum1779.graph fusedMap3094=true := by decide +kernel
theorem certified3094 : Certified (graph core3094) (root 6) 0 5 :=
  of_native_maps core3094 DegreeTwoThreeSpectrum1777.graph DegreeTwoThreeSpectrum1779.graph
    sourceMap3094 fusedMap3094 sourceMap3094_checked fusedMap3094_checked
    DegreeTwoThreeFiniteComparisons.comparison3094
#print axioms sourceMap3094_checked
#print axioms fusedMap3094_checked
#print axioms certified3094
def sourceMap3094swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,12,13,8] (sourceLabel 6 5 0 v)
def fusedMap3094swap : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 5 0 v)
theorem sourceMap3094swap_checked : acceptsGraphIso
    (source (graph core3094) (root 6) 5 0) DegreeTwoThreeSpectrum1777.graph sourceMap3094swap=true := by decide +kernel
theorem fusedMap3094swap_checked : acceptsGraphIso
    (fused (graph core3094) (root 6) 5 0) DegreeTwoThreeSpectrum1779.graph fusedMap3094swap=true := by decide +kernel
theorem certified3094swap : Certified (graph core3094) (root 6) 5 0 :=
  of_native_maps core3094 DegreeTwoThreeSpectrum1777.graph DegreeTwoThreeSpectrum1779.graph
    sourceMap3094swap fusedMap3094swap sourceMap3094swap_checked fusedMap3094swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3094
#print axioms sourceMap3094swap_checked
#print axioms fusedMap3094swap_checked
#print axioms certified3094swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
