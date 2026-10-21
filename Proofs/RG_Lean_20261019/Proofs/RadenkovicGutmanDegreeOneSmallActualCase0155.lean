/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0155 : Family 4 := level4.get ⟨4,by decide⟩
def sourceMap0155 : (Vertices 4 ⊕ Fin 3 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,7,8,9,10,1,2,3,4,5,6] (sourceLabel 4 2 2 v)
def fusedMap0155 : (Vertices 4 ⊕ Fin 6) → Fin 11 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10] (fusedLabel 4 2 2 v)
theorem sourceMap0155_checked : acceptsGraphIso
    (source (graph core0155) (root 4) 2 2) DegreeOneSmallSpectrum346.graph sourceMap0155=true := by decide +kernel
theorem fusedMap0155_checked : acceptsGraphIso
    (fused (graph core0155) (root 4) 2 2) DegreeOneSmallSpectrum175.graph fusedMap0155=true := by decide +kernel
theorem certified0155 : Certified (graph core0155) (root 4) 2 2 :=
  of_native_maps core0155 DegreeOneSmallSpectrum346.graph DegreeOneSmallSpectrum175.graph
    sourceMap0155 fusedMap0155 sourceMap0155_checked fusedMap0155_checked
    DegreeOneSmallComparisons.comparison0155
#print axioms sourceMap0155_checked
#print axioms fusedMap0155_checked
#print axioms certified0155
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
