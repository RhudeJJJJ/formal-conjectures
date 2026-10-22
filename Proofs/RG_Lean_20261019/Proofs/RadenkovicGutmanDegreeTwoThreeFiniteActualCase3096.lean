/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3096 : Family 6 := level6.get ⟨30,by decide⟩
def sourceMap3096 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (sourceLabel 6 0 5 v)
def fusedMap3096 : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 0 5 v)
theorem sourceMap3096_checked : acceptsGraphIso
    (source (graph core3096) (root 6) 0 5) DegreeTwoThreeSpectrum1821.graph sourceMap3096=true := by decide +kernel
theorem fusedMap3096_checked : acceptsGraphIso
    (fused (graph core3096) (root 6) 0 5) DegreeTwoThreeSpectrum1823.graph fusedMap3096=true := by decide +kernel
theorem certified3096 : Certified (graph core3096) (root 6) 0 5 :=
  of_native_maps core3096 DegreeTwoThreeSpectrum1821.graph DegreeTwoThreeSpectrum1823.graph
    sourceMap3096 fusedMap3096 sourceMap3096_checked fusedMap3096_checked
    DegreeTwoThreeFiniteComparisons.comparison3096
#print axioms sourceMap3096_checked
#print axioms fusedMap3096_checked
#print axioms certified3096
def sourceMap3096swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 1) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,12,13,8] (sourceLabel 6 5 0 v)
def fusedMap3096swap : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 5 0 v)
theorem sourceMap3096swap_checked : acceptsGraphIso
    (source (graph core3096) (root 6) 5 0) DegreeTwoThreeSpectrum1821.graph sourceMap3096swap=true := by decide +kernel
theorem fusedMap3096swap_checked : acceptsGraphIso
    (fused (graph core3096) (root 6) 5 0) DegreeTwoThreeSpectrum1823.graph fusedMap3096swap=true := by decide +kernel
theorem certified3096swap : Certified (graph core3096) (root 6) 5 0 :=
  of_native_maps core3096 DegreeTwoThreeSpectrum1821.graph DegreeTwoThreeSpectrum1823.graph
    sourceMap3096swap fusedMap3096swap sourceMap3096swap_checked fusedMap3096swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3096
#print axioms sourceMap3096swap_checked
#print axioms fusedMap3096swap_checked
#print axioms certified3096swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
