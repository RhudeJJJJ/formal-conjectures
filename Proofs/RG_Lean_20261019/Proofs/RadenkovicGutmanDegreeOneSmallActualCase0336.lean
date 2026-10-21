/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0336 : Family 6 := level6.get ⟨8,by decide⟩
def sourceMap0336 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 3) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9] (sourceLabel 6 1 2 v)
def fusedMap0336 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 1 2 v)
theorem sourceMap0336_checked : acceptsGraphIso
    (source (graph core0336) (root 6) 1 2) DegreeOneSmallSpectrum476.graph sourceMap0336=true := by decide +kernel
theorem fusedMap0336_checked : acceptsGraphIso
    (fused (graph core0336) (root 6) 1 2) DegreeOneSmallSpectrum372.graph fusedMap0336=true := by decide +kernel
theorem certified0336 : Certified (graph core0336) (root 6) 1 2 :=
  of_native_maps core0336 DegreeOneSmallSpectrum476.graph DegreeOneSmallSpectrum372.graph
    sourceMap0336 fusedMap0336 sourceMap0336_checked fusedMap0336_checked
    DegreeOneSmallComparisons.comparison0336
#print axioms sourceMap0336_checked
#print axioms fusedMap0336_checked
#print axioms certified0336
def sourceMap0336swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11] (sourceLabel 6 2 1 v)
def fusedMap0336swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 2 1 v)
theorem sourceMap0336swap_checked : acceptsGraphIso
    (source (graph core0336) (root 6) 2 1) DegreeOneSmallSpectrum476.graph sourceMap0336swap=true := by decide +kernel
theorem fusedMap0336swap_checked : acceptsGraphIso
    (fused (graph core0336) (root 6) 2 1) DegreeOneSmallSpectrum372.graph fusedMap0336swap=true := by decide +kernel
theorem certified0336swap : Certified (graph core0336) (root 6) 2 1 :=
  of_native_maps core0336 DegreeOneSmallSpectrum476.graph DegreeOneSmallSpectrum372.graph
    sourceMap0336swap fusedMap0336swap sourceMap0336swap_checked fusedMap0336swap_checked
    DegreeOneSmallComparisons.comparison0336
#print axioms sourceMap0336swap_checked
#print axioms fusedMap0336swap_checked
#print axioms certified0336swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
