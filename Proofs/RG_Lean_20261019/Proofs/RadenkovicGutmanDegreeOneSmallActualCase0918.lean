/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0918 : Family 8 := level8.get ⟨61,by decide⟩
def sourceMap0918 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 8 1 1 v)
def fusedMap0918 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0918_checked : acceptsGraphIso
    (source (graph core0918) (root 8) 1 1) DegreeOneSmallSpectrum1336.graph sourceMap0918=true := by decide +kernel
theorem fusedMap0918_checked : acceptsGraphIso
    (fused (graph core0918) (root 8) 1 1) DegreeOneSmallSpectrum923.graph fusedMap0918=true := by decide +kernel
theorem certified0918 : Certified (graph core0918) (root 8) 1 1 :=
  of_native_maps core0918 DegreeOneSmallSpectrum1336.graph DegreeOneSmallSpectrum923.graph
    sourceMap0918 fusedMap0918 sourceMap0918_checked fusedMap0918_checked
    DegreeOneSmallComparisons.comparison0918
#print axioms sourceMap0918_checked
#print axioms fusedMap0918_checked
#print axioms certified0918
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
