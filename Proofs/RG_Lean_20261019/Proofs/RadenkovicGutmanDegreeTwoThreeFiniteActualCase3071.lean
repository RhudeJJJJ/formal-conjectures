/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3071 : Family 10 := level10.get ⟨1801,by decide⟩
def sourceMap3071 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3071 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,12,1,0,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3071_checked : acceptsGraphIso
    (source (graph core3071) (root 10) 0 4) DegreeTwoThreeSpectrum7057.graph sourceMap3071=true := by decide +kernel
theorem fusedMap3071_checked : acceptsGraphIso
    (fused (graph core3071) (root 10) 0 4) DegreeTwoThreeSpectrum7058.graph fusedMap3071=true := by decide +kernel
theorem certified3071 : Certified (graph core3071) (root 10) 0 4 :=
  of_native_maps core3071 DegreeTwoThreeSpectrum7057.graph DegreeTwoThreeSpectrum7058.graph
    sourceMap3071 fusedMap3071 sourceMap3071_checked fusedMap3071_checked
    DegreeTwoThreeFiniteComparisons.comparison3071
#print axioms sourceMap3071_checked
#print axioms fusedMap3071_checked
#print axioms certified3071
def sourceMap3071swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3071swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,12,1,0,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3071swap_checked : acceptsGraphIso
    (source (graph core3071) (root 10) 4 0) DegreeTwoThreeSpectrum7057.graph sourceMap3071swap=true := by decide +kernel
theorem fusedMap3071swap_checked : acceptsGraphIso
    (fused (graph core3071) (root 10) 4 0) DegreeTwoThreeSpectrum7058.graph fusedMap3071swap=true := by decide +kernel
theorem certified3071swap : Certified (graph core3071) (root 10) 4 0 :=
  of_native_maps core3071 DegreeTwoThreeSpectrum7057.graph DegreeTwoThreeSpectrum7058.graph
    sourceMap3071swap fusedMap3071swap sourceMap3071swap_checked fusedMap3071swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3071
#print axioms sourceMap3071swap_checked
#print axioms fusedMap3071swap_checked
#print axioms certified3071swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
