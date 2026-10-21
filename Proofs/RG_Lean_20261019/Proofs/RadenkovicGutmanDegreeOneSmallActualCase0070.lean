/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0070 : Family 3 := level3.get ⟨0,by decide⟩
def sourceMap0070 : (Vertices 3 ⊕ Fin 3 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 3 2 3 v)
def fusedMap0070 : (Vertices 3 ⊕ Fin 7) → Fin 11 :=
  fun v => ![2,3,4,5,1,0,6,7,8,9,10] (fusedLabel 3 2 3 v)
theorem sourceMap0070_checked : acceptsGraphIso
    (source (graph core0070) (root 3) 2 3) DegreeOneSmallSpectrum218.graph sourceMap0070=true := by decide +kernel
theorem fusedMap0070_checked : acceptsGraphIso
    (fused (graph core0070) (root 3) 2 3) DegreeOneSmallSpectrum168.graph fusedMap0070=true := by decide +kernel
theorem certified0070 : Certified (graph core0070) (root 3) 2 3 :=
  of_native_maps core0070 DegreeOneSmallSpectrum218.graph DegreeOneSmallSpectrum168.graph
    sourceMap0070 fusedMap0070 sourceMap0070_checked fusedMap0070_checked
    DegreeOneSmallComparisons.comparison0070
#print axioms sourceMap0070_checked
#print axioms fusedMap0070_checked
#print axioms certified0070
def sourceMap0070swap : (Vertices 3 ⊕ Fin 4 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,7,8,9,10,4,5,6] (sourceLabel 3 3 2 v)
def fusedMap0070swap : (Vertices 3 ⊕ Fin 7) → Fin 11 :=
  fun v => ![2,3,4,5,1,0,6,7,8,9,10] (fusedLabel 3 3 2 v)
theorem sourceMap0070swap_checked : acceptsGraphIso
    (source (graph core0070) (root 3) 3 2) DegreeOneSmallSpectrum218.graph sourceMap0070swap=true := by decide +kernel
theorem fusedMap0070swap_checked : acceptsGraphIso
    (fused (graph core0070) (root 3) 3 2) DegreeOneSmallSpectrum168.graph fusedMap0070swap=true := by decide +kernel
theorem certified0070swap : Certified (graph core0070) (root 3) 3 2 :=
  of_native_maps core0070 DegreeOneSmallSpectrum218.graph DegreeOneSmallSpectrum168.graph
    sourceMap0070swap fusedMap0070swap sourceMap0070swap_checked fusedMap0070swap_checked
    DegreeOneSmallComparisons.comparison0070
#print axioms sourceMap0070swap_checked
#print axioms fusedMap0070swap_checked
#print axioms certified0070swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
