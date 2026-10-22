/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons63
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3158 : Family 8 := level8.get ⟨77,by decide⟩
def sourceMap3158 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3158 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3158_checked : acceptsGraphIso
    (source (graph core3158) (root 8) 0 5) DegreeTwoThreeSpectrum4088.graph sourceMap3158=true := by decide +kernel
theorem fusedMap3158_checked : acceptsGraphIso
    (fused (graph core3158) (root 8) 0 5) DegreeTwoThreeSpectrum4089.graph fusedMap3158=true := by decide +kernel
theorem certified3158 : Certified (graph core3158) (root 8) 0 5 :=
  of_native_maps core3158 DegreeTwoThreeSpectrum4088.graph DegreeTwoThreeSpectrum4089.graph
    sourceMap3158 fusedMap3158 sourceMap3158_checked fusedMap3158_checked
    DegreeTwoThreeFiniteComparisons.comparison3158
#print axioms sourceMap3158_checked
#print axioms fusedMap3158_checked
#print axioms certified3158
def sourceMap3158swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,15,9] (sourceLabel 8 5 0 v)
def fusedMap3158swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3158swap_checked : acceptsGraphIso
    (source (graph core3158) (root 8) 5 0) DegreeTwoThreeSpectrum4088.graph sourceMap3158swap=true := by decide +kernel
theorem fusedMap3158swap_checked : acceptsGraphIso
    (fused (graph core3158) (root 8) 5 0) DegreeTwoThreeSpectrum4089.graph fusedMap3158swap=true := by decide +kernel
theorem certified3158swap : Certified (graph core3158) (root 8) 5 0 :=
  of_native_maps core3158 DegreeTwoThreeSpectrum4088.graph DegreeTwoThreeSpectrum4089.graph
    sourceMap3158swap fusedMap3158swap sourceMap3158swap_checked fusedMap3158swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3158
#print axioms sourceMap3158swap_checked
#print axioms fusedMap3158swap_checked
#print axioms certified3158swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
