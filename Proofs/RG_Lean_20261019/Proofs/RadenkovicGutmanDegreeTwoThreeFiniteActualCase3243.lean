/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3243 : Family 9 := level9.get ⟨41,by decide⟩
def sourceMap3243 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,10,11,12,13,14,15,16,7,8,9,1,2,3,4,5,6] (sourceLabel 9 0 5 v)
def fusedMap3243 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,15,16,8,9,10,11,12,13,14] (fusedLabel 9 0 5 v)
theorem sourceMap3243_checked : acceptsGraphIso
    (source (graph core3243) (root 9) 0 5) DegreeTwoThreeSpectrum5126.graph sourceMap3243=true := by decide +kernel
theorem fusedMap3243_checked : acceptsGraphIso
    (fused (graph core3243) (root 9) 0 5) DegreeTwoThreeSpectrum5133.graph fusedMap3243=true := by decide +kernel
theorem certified3243 : Certified (graph core3243) (root 9) 0 5 :=
  of_native_maps core3243 DegreeTwoThreeSpectrum5126.graph DegreeTwoThreeSpectrum5133.graph
    sourceMap3243 fusedMap3243 sourceMap3243_checked fusedMap3243_checked
    DegreeTwoThreeFiniteComparisons.comparison3243
#print axioms sourceMap3243_checked
#print axioms fusedMap3243_checked
#print axioms certified3243
def sourceMap3243swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,10,11,12,13,14,15,16,7,8,1,2,3,4,5,6,9] (sourceLabel 9 5 0 v)
def fusedMap3243swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,15,16,8,9,10,11,12,13,14] (fusedLabel 9 5 0 v)
theorem sourceMap3243swap_checked : acceptsGraphIso
    (source (graph core3243) (root 9) 5 0) DegreeTwoThreeSpectrum5126.graph sourceMap3243swap=true := by decide +kernel
theorem fusedMap3243swap_checked : acceptsGraphIso
    (fused (graph core3243) (root 9) 5 0) DegreeTwoThreeSpectrum5133.graph fusedMap3243swap=true := by decide +kernel
theorem certified3243swap : Certified (graph core3243) (root 9) 5 0 :=
  of_native_maps core3243 DegreeTwoThreeSpectrum5126.graph DegreeTwoThreeSpectrum5133.graph
    sourceMap3243swap fusedMap3243swap sourceMap3243swap_checked fusedMap3243swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3243
#print axioms sourceMap3243swap_checked
#print axioms fusedMap3243swap_checked
#print axioms certified3243swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
