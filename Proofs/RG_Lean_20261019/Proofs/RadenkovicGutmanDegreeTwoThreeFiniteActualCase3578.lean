/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3578 : Family 8 := level8.get ⟨135,by decide⟩
def sourceMap3578 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3578 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3578_checked : acceptsGraphIso
    (source (graph core3578) (root 8) 0 6) DegreeTwoThreeSpectrum5433.graph sourceMap3578=true := by decide +kernel
theorem fusedMap3578_checked : acceptsGraphIso
    (fused (graph core3578) (root 8) 0 6) DegreeTwoThreeSpectrum5435.graph fusedMap3578=true := by decide +kernel
theorem certified3578 : Certified (graph core3578) (root 8) 0 6 :=
  of_native_maps core3578 DegreeTwoThreeSpectrum5433.graph DegreeTwoThreeSpectrum5435.graph
    sourceMap3578 fusedMap3578 sourceMap3578_checked fusedMap3578_checked
    DegreeTwoThreeFiniteComparisons.comparison3578
#print axioms sourceMap3578_checked
#print axioms fusedMap3578_checked
#print axioms certified3578
def sourceMap3578swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3578swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3578swap_checked : acceptsGraphIso
    (source (graph core3578) (root 8) 6 0) DegreeTwoThreeSpectrum5433.graph sourceMap3578swap=true := by decide +kernel
theorem fusedMap3578swap_checked : acceptsGraphIso
    (fused (graph core3578) (root 8) 6 0) DegreeTwoThreeSpectrum5435.graph fusedMap3578swap=true := by decide +kernel
theorem certified3578swap : Certified (graph core3578) (root 8) 6 0 :=
  of_native_maps core3578 DegreeTwoThreeSpectrum5433.graph DegreeTwoThreeSpectrum5435.graph
    sourceMap3578swap fusedMap3578swap sourceMap3578swap_checked fusedMap3578swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3578
#print axioms sourceMap3578swap_checked
#print axioms fusedMap3578swap_checked
#print axioms certified3578swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
