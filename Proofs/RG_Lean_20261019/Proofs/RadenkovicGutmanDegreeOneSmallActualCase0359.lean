/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0359 : Family 6 := level6.get ⟨12,by decide⟩
def sourceMap0359 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,10,7,8,9] (sourceLabel 6 0 2 v)
def fusedMap0359 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 0 2 v)
theorem sourceMap0359_checked : acceptsGraphIso
    (source (graph core0359) (root 6) 0 2) DegreeOneSmallSpectrum211.graph sourceMap0359=true := by decide +kernel
theorem fusedMap0359_checked : acceptsGraphIso
    (fused (graph core0359) (root 6) 0 2) DegreeOneSmallSpectrum212.graph fusedMap0359=true := by decide +kernel
theorem certified0359 : Certified (graph core0359) (root 6) 0 2 :=
  of_native_maps core0359 DegreeOneSmallSpectrum211.graph DegreeOneSmallSpectrum212.graph
    sourceMap0359 fusedMap0359 sourceMap0359_checked fusedMap0359_checked
    DegreeOneSmallComparisons.comparison0359
#print axioms sourceMap0359_checked
#print axioms fusedMap0359_checked
#print axioms certified0359
def sourceMap0359swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (sourceLabel 6 2 0 v)
def fusedMap0359swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 2 0 v)
theorem sourceMap0359swap_checked : acceptsGraphIso
    (source (graph core0359) (root 6) 2 0) DegreeOneSmallSpectrum211.graph sourceMap0359swap=true := by decide +kernel
theorem fusedMap0359swap_checked : acceptsGraphIso
    (fused (graph core0359) (root 6) 2 0) DegreeOneSmallSpectrum212.graph fusedMap0359swap=true := by decide +kernel
theorem certified0359swap : Certified (graph core0359) (root 6) 2 0 :=
  of_native_maps core0359 DegreeOneSmallSpectrum211.graph DegreeOneSmallSpectrum212.graph
    sourceMap0359swap fusedMap0359swap sourceMap0359swap_checked fusedMap0359swap_checked
    DegreeOneSmallComparisons.comparison0359
#print axioms sourceMap0359swap_checked
#print axioms fusedMap0359swap_checked
#print axioms certified0359swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
