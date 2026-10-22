/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3517 : Family 7 := level7.get ⟨55,by decide⟩
def sourceMap3517 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (sourceLabel 7 0 6 v)
def fusedMap3517 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 0 6 v)
theorem sourceMap3517_checked : acceptsGraphIso
    (source (graph core3517) (root 7) 0 6) DegreeTwoThreeSpectrum4084.graph sourceMap3517=true := by decide +kernel
theorem fusedMap3517_checked : acceptsGraphIso
    (fused (graph core3517) (root 7) 0 6) DegreeTwoThreeSpectrum4086.graph fusedMap3517=true := by decide +kernel
theorem certified3517 : Certified (graph core3517) (root 7) 0 6 :=
  of_native_maps core3517 DegreeTwoThreeSpectrum4084.graph DegreeTwoThreeSpectrum4086.graph
    sourceMap3517 fusedMap3517 sourceMap3517_checked fusedMap3517_checked
    DegreeTwoThreeFiniteComparisons.comparison3517
#print axioms sourceMap3517_checked
#print axioms fusedMap3517_checked
#print axioms certified3517
def sourceMap3517swap : (Vertices 7 ⊕ Fin 7 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,15,9] (sourceLabel 7 6 0 v)
def fusedMap3517swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 6 0 v)
theorem sourceMap3517swap_checked : acceptsGraphIso
    (source (graph core3517) (root 7) 6 0) DegreeTwoThreeSpectrum4084.graph sourceMap3517swap=true := by decide +kernel
theorem fusedMap3517swap_checked : acceptsGraphIso
    (fused (graph core3517) (root 7) 6 0) DegreeTwoThreeSpectrum4086.graph fusedMap3517swap=true := by decide +kernel
theorem certified3517swap : Certified (graph core3517) (root 7) 6 0 :=
  of_native_maps core3517 DegreeTwoThreeSpectrum4084.graph DegreeTwoThreeSpectrum4086.graph
    sourceMap3517swap fusedMap3517swap sourceMap3517swap_checked fusedMap3517swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3517
#print axioms sourceMap3517swap_checked
#print axioms fusedMap3517swap_checked
#print axioms certified3517swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
