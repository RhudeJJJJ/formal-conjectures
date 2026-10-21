/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0798 : Family 8 := level8.get ⟨17,by decide⟩
def sourceMap0798 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,3,4,5,6] (sourceLabel 8 1 1 v)
def fusedMap0798 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0798_checked : acceptsGraphIso
    (source (graph core0798) (root 8) 1 1) DegreeOneSmallSpectrum1339.graph sourceMap0798=true := by decide +kernel
theorem fusedMap0798_checked : acceptsGraphIso
    (fused (graph core0798) (root 8) 1 1) DegreeOneSmallSpectrum935.graph fusedMap0798=true := by decide +kernel
theorem certified0798 : Certified (graph core0798) (root 8) 1 1 :=
  of_native_maps core0798 DegreeOneSmallSpectrum1339.graph DegreeOneSmallSpectrum935.graph
    sourceMap0798 fusedMap0798 sourceMap0798_checked fusedMap0798_checked
    DegreeOneSmallComparisons.comparison0798
#print axioms sourceMap0798_checked
#print axioms fusedMap0798_checked
#print axioms certified0798
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
