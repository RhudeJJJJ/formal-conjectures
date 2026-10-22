/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3866 : Family 8 := level8.get ⟨135,by decide⟩
def sourceMap3866 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,10,8,9,11,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3866 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3866_checked : acceptsGraphIso
    (source (graph core3866) (root 8) 1 4) DegreeTwoThreeSpectrum4410.graph sourceMap3866=true := by decide +kernel
theorem fusedMap3866_checked : acceptsGraphIso
    (fused (graph core3866) (root 8) 1 4) DegreeTwoThreeSpectrum3984.graph fusedMap3866=true := by decide +kernel
theorem certified3866 : Certified (graph core3866) (root 8) 1 4 :=
  of_native_maps core3866 DegreeTwoThreeSpectrum4410.graph DegreeTwoThreeSpectrum3984.graph
    sourceMap3866 fusedMap3866 sourceMap3866_checked fusedMap3866_checked
    DegreeTwoThreeFiniteComparisons.comparison3866
#print axioms sourceMap3866_checked
#print axioms fusedMap3866_checked
#print axioms certified3866
def sourceMap3866swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,10,11,12,13,14,15,8,9] (sourceLabel 8 4 1 v)
def fusedMap3866swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3866swap_checked : acceptsGraphIso
    (source (graph core3866) (root 8) 4 1) DegreeTwoThreeSpectrum4410.graph sourceMap3866swap=true := by decide +kernel
theorem fusedMap3866swap_checked : acceptsGraphIso
    (fused (graph core3866) (root 8) 4 1) DegreeTwoThreeSpectrum3984.graph fusedMap3866swap=true := by decide +kernel
theorem certified3866swap : Certified (graph core3866) (root 8) 4 1 :=
  of_native_maps core3866 DegreeTwoThreeSpectrum4410.graph DegreeTwoThreeSpectrum3984.graph
    sourceMap3866swap fusedMap3866swap sourceMap3866swap_checked fusedMap3866swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3866
#print axioms sourceMap3866swap_checked
#print axioms fusedMap3866swap_checked
#print axioms certified3866swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
