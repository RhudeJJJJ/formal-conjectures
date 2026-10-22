/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3401 : Family 9 := level9.get ⟨497,by decide⟩
def sourceMap3401 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3401 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3401_checked : acceptsGraphIso
    (source (graph core3401) (root 9) 0 5) DegreeTwoThreeSpectrum6893.graph sourceMap3401=true := by decide +kernel
theorem fusedMap3401_checked : acceptsGraphIso
    (fused (graph core3401) (root 9) 0 5) DegreeTwoThreeSpectrum5680.graph fusedMap3401=true := by decide +kernel
theorem certified3401 : Certified (graph core3401) (root 9) 0 5 :=
  of_native_maps core3401 DegreeTwoThreeSpectrum6893.graph DegreeTwoThreeSpectrum5680.graph
    sourceMap3401 fusedMap3401 sourceMap3401_checked fusedMap3401_checked
    DegreeTwoThreeFiniteComparisons.comparison3401
#print axioms sourceMap3401_checked
#print axioms fusedMap3401_checked
#print axioms certified3401
def sourceMap3401swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3401swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3401swap_checked : acceptsGraphIso
    (source (graph core3401) (root 9) 5 0) DegreeTwoThreeSpectrum6893.graph sourceMap3401swap=true := by decide +kernel
theorem fusedMap3401swap_checked : acceptsGraphIso
    (fused (graph core3401) (root 9) 5 0) DegreeTwoThreeSpectrum5680.graph fusedMap3401swap=true := by decide +kernel
theorem certified3401swap : Certified (graph core3401) (root 9) 5 0 :=
  of_native_maps core3401 DegreeTwoThreeSpectrum6893.graph DegreeTwoThreeSpectrum5680.graph
    sourceMap3401swap fusedMap3401swap sourceMap3401swap_checked fusedMap3401swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3401
#print axioms sourceMap3401swap_checked
#print axioms fusedMap3401swap_checked
#print axioms certified3401swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
