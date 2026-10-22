/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3062 : Family 10 := level10.get ⟨1738,by decide⟩
def sourceMap3062 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3062 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3062_checked : acceptsGraphIso
    (source (graph core3062) (root 10) 0 4) DegreeTwoThreeSpectrum7379.graph sourceMap3062=true := by decide +kernel
theorem fusedMap3062_checked : acceptsGraphIso
    (fused (graph core3062) (root 10) 0 4) DegreeTwoThreeSpectrum6581.graph fusedMap3062=true := by decide +kernel
theorem certified3062 : Certified (graph core3062) (root 10) 0 4 :=
  of_native_maps core3062 DegreeTwoThreeSpectrum7379.graph DegreeTwoThreeSpectrum6581.graph
    sourceMap3062 fusedMap3062 sourceMap3062_checked fusedMap3062_checked
    DegreeTwoThreeFiniteComparisons.comparison3062
#print axioms sourceMap3062_checked
#print axioms fusedMap3062_checked
#print axioms certified3062
def sourceMap3062swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3062swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3062swap_checked : acceptsGraphIso
    (source (graph core3062) (root 10) 4 0) DegreeTwoThreeSpectrum7379.graph sourceMap3062swap=true := by decide +kernel
theorem fusedMap3062swap_checked : acceptsGraphIso
    (fused (graph core3062) (root 10) 4 0) DegreeTwoThreeSpectrum6581.graph fusedMap3062swap=true := by decide +kernel
theorem certified3062swap : Certified (graph core3062) (root 10) 4 0 :=
  of_native_maps core3062 DegreeTwoThreeSpectrum7379.graph DegreeTwoThreeSpectrum6581.graph
    sourceMap3062swap fusedMap3062swap sourceMap3062swap_checked fusedMap3062swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3062
#print axioms sourceMap3062swap_checked
#print axioms fusedMap3062swap_checked
#print axioms certified3062swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
