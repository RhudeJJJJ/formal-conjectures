/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons63
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3184 : Family 8 := level8.get ⟨147,by decide⟩
def sourceMap3184 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3184 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3184_checked : acceptsGraphIso
    (source (graph core3184) (root 8) 0 5) DegreeTwoThreeSpectrum4477.graph sourceMap3184=true := by decide +kernel
theorem fusedMap3184_checked : acceptsGraphIso
    (fused (graph core3184) (root 8) 0 5) DegreeTwoThreeSpectrum4009.graph fusedMap3184=true := by decide +kernel
theorem certified3184 : Certified (graph core3184) (root 8) 0 5 :=
  of_native_maps core3184 DegreeTwoThreeSpectrum4477.graph DegreeTwoThreeSpectrum4009.graph
    sourceMap3184 fusedMap3184 sourceMap3184_checked fusedMap3184_checked
    DegreeTwoThreeFiniteComparisons.comparison3184
#print axioms sourceMap3184_checked
#print axioms fusedMap3184_checked
#print axioms certified3184
def sourceMap3184swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3184swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3184swap_checked : acceptsGraphIso
    (source (graph core3184) (root 8) 5 0) DegreeTwoThreeSpectrum4477.graph sourceMap3184swap=true := by decide +kernel
theorem fusedMap3184swap_checked : acceptsGraphIso
    (fused (graph core3184) (root 8) 5 0) DegreeTwoThreeSpectrum4009.graph fusedMap3184swap=true := by decide +kernel
theorem certified3184swap : Certified (graph core3184) (root 8) 5 0 :=
  of_native_maps core3184 DegreeTwoThreeSpectrum4477.graph DegreeTwoThreeSpectrum4009.graph
    sourceMap3184swap fusedMap3184swap sourceMap3184swap_checked fusedMap3184swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3184
#print axioms sourceMap3184swap_checked
#print axioms fusedMap3184swap_checked
#print axioms certified3184swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
