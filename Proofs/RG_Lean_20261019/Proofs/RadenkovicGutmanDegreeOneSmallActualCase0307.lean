/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0307 : Family 6 := level6.get ⟨4,by decide⟩
def sourceMap0307 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,12,7,8,9,10,11] (sourceLabel 6 0 4 v)
def fusedMap0307 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap0307_checked : acceptsGraphIso
    (source (graph core0307) (root 6) 0 4) DegreeOneSmallSpectrum976.graph sourceMap0307=true := by decide +kernel
theorem fusedMap0307_checked : acceptsGraphIso
    (fused (graph core0307) (root 6) 0 4) DegreeOneSmallSpectrum859.graph fusedMap0307=true := by decide +kernel
theorem certified0307 : Certified (graph core0307) (root 6) 0 4 :=
  of_native_maps core0307 DegreeOneSmallSpectrum976.graph DegreeOneSmallSpectrum859.graph
    sourceMap0307 fusedMap0307 sourceMap0307_checked fusedMap0307_checked
    DegreeOneSmallComparisons.comparison0307
#print axioms sourceMap0307_checked
#print axioms fusedMap0307_checked
#print axioms certified0307
def sourceMap0307swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 6 4 0 v)
def fusedMap0307swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap0307swap_checked : acceptsGraphIso
    (source (graph core0307) (root 6) 4 0) DegreeOneSmallSpectrum976.graph sourceMap0307swap=true := by decide +kernel
theorem fusedMap0307swap_checked : acceptsGraphIso
    (fused (graph core0307) (root 6) 4 0) DegreeOneSmallSpectrum859.graph fusedMap0307swap=true := by decide +kernel
theorem certified0307swap : Certified (graph core0307) (root 6) 4 0 :=
  of_native_maps core0307 DegreeOneSmallSpectrum976.graph DegreeOneSmallSpectrum859.graph
    sourceMap0307swap fusedMap0307swap sourceMap0307swap_checked fusedMap0307swap_checked
    DegreeOneSmallComparisons.comparison0307
#print axioms sourceMap0307swap_checked
#print axioms fusedMap0307swap_checked
#print axioms certified0307swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
