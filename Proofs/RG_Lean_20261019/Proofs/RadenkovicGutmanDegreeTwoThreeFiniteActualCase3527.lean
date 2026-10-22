/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3527 : Family 7 := level7.get ⟨77,by decide⟩
def sourceMap3527 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (sourceLabel 7 0 6 v)
def fusedMap3527 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 0 6 v)
theorem sourceMap3527_checked : acceptsGraphIso
    (source (graph core3527) (root 7) 0 6) DegreeTwoThreeSpectrum4336.graph sourceMap3527=true := by decide +kernel
theorem fusedMap3527_checked : acceptsGraphIso
    (fused (graph core3527) (root 7) 0 6) DegreeTwoThreeSpectrum3941.graph fusedMap3527=true := by decide +kernel
theorem certified3527 : Certified (graph core3527) (root 7) 0 6 :=
  of_native_maps core3527 DegreeTwoThreeSpectrum4336.graph DegreeTwoThreeSpectrum3941.graph
    sourceMap3527 fusedMap3527 sourceMap3527_checked fusedMap3527_checked
    DegreeTwoThreeFiniteComparisons.comparison3527
#print axioms sourceMap3527_checked
#print axioms fusedMap3527_checked
#print axioms certified3527
def sourceMap3527swap : (Vertices 7 ⊕ Fin 7 ⊕ Fin 1) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,10] (sourceLabel 7 6 0 v)
def fusedMap3527swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 6 0 v)
theorem sourceMap3527swap_checked : acceptsGraphIso
    (source (graph core3527) (root 7) 6 0) DegreeTwoThreeSpectrum4336.graph sourceMap3527swap=true := by decide +kernel
theorem fusedMap3527swap_checked : acceptsGraphIso
    (fused (graph core3527) (root 7) 6 0) DegreeTwoThreeSpectrum3941.graph fusedMap3527swap=true := by decide +kernel
theorem certified3527swap : Certified (graph core3527) (root 7) 6 0 :=
  of_native_maps core3527 DegreeTwoThreeSpectrum4336.graph DegreeTwoThreeSpectrum3941.graph
    sourceMap3527swap fusedMap3527swap sourceMap3527swap_checked fusedMap3527swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3527
#print axioms sourceMap3527swap_checked
#print axioms fusedMap3527swap_checked
#print axioms certified3527swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
