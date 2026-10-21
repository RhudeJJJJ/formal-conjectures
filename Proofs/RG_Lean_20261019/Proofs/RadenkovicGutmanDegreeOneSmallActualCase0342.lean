/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0342 : Family 6 := level6.get ⟨10,by decide⟩
def sourceMap0342 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,11,7,8,9,10] (sourceLabel 6 0 3 v)
def fusedMap0342 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 0 3 v)
theorem sourceMap0342_checked : acceptsGraphIso
    (source (graph core0342) (root 6) 0 3) DegreeOneSmallSpectrum518.graph sourceMap0342=true := by decide +kernel
theorem fusedMap0342_checked : acceptsGraphIso
    (fused (graph core0342) (root 6) 0 3) DegreeOneSmallSpectrum379.graph fusedMap0342=true := by decide +kernel
theorem certified0342 : Certified (graph core0342) (root 6) 0 3 :=
  of_native_maps core0342 DegreeOneSmallSpectrum518.graph DegreeOneSmallSpectrum379.graph
    sourceMap0342 fusedMap0342 sourceMap0342_checked fusedMap0342_checked
    DegreeOneSmallComparisons.comparison0342
#print axioms sourceMap0342_checked
#print axioms fusedMap0342_checked
#print axioms certified0342
def sourceMap0342swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 6 3 0 v)
def fusedMap0342swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 3 0 v)
theorem sourceMap0342swap_checked : acceptsGraphIso
    (source (graph core0342) (root 6) 3 0) DegreeOneSmallSpectrum518.graph sourceMap0342swap=true := by decide +kernel
theorem fusedMap0342swap_checked : acceptsGraphIso
    (fused (graph core0342) (root 6) 3 0) DegreeOneSmallSpectrum379.graph fusedMap0342swap=true := by decide +kernel
theorem certified0342swap : Certified (graph core0342) (root 6) 3 0 :=
  of_native_maps core0342 DegreeOneSmallSpectrum518.graph DegreeOneSmallSpectrum379.graph
    sourceMap0342swap fusedMap0342swap sourceMap0342swap_checked fusedMap0342swap_checked
    DegreeOneSmallComparisons.comparison0342
#print axioms sourceMap0342swap_checked
#print axioms fusedMap0342swap_checked
#print axioms certified0342swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
