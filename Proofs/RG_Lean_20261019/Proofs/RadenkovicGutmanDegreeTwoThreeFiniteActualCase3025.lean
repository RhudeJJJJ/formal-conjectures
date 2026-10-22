/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3025 : Family 10 := level10.get ⟨1628,by decide⟩
def sourceMap3025 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3025 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3025_checked : acceptsGraphIso
    (source (graph core3025) (root 10) 0 4) DegreeTwoThreeSpectrum7184.graph sourceMap3025=true := by decide +kernel
theorem fusedMap3025_checked : acceptsGraphIso
    (fused (graph core3025) (root 10) 0 4) DegreeTwoThreeSpectrum6191.graph fusedMap3025=true := by decide +kernel
theorem certified3025 : Certified (graph core3025) (root 10) 0 4 :=
  of_native_maps core3025 DegreeTwoThreeSpectrum7184.graph DegreeTwoThreeSpectrum6191.graph
    sourceMap3025 fusedMap3025 sourceMap3025_checked fusedMap3025_checked
    DegreeTwoThreeFiniteComparisons.comparison3025
#print axioms sourceMap3025_checked
#print axioms fusedMap3025_checked
#print axioms certified3025
def sourceMap3025swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3025swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3025swap_checked : acceptsGraphIso
    (source (graph core3025) (root 10) 4 0) DegreeTwoThreeSpectrum7184.graph sourceMap3025swap=true := by decide +kernel
theorem fusedMap3025swap_checked : acceptsGraphIso
    (fused (graph core3025) (root 10) 4 0) DegreeTwoThreeSpectrum6191.graph fusedMap3025swap=true := by decide +kernel
theorem certified3025swap : Certified (graph core3025) (root 10) 4 0 :=
  of_native_maps core3025 DegreeTwoThreeSpectrum7184.graph DegreeTwoThreeSpectrum6191.graph
    sourceMap3025swap fusedMap3025swap sourceMap3025swap_checked fusedMap3025swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3025
#print axioms sourceMap3025swap_checked
#print axioms fusedMap3025swap_checked
#print axioms certified3025swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
