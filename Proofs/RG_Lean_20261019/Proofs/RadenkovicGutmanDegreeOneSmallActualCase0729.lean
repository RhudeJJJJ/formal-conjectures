/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0729 : Family 7 := level7.get ⟨100,by decide⟩
def sourceMap0729 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9] (sourceLabel 7 0 0 v)
def fusedMap0729 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 7 0 0 v)
theorem sourceMap0729_checked : acceptsGraphIso
    (source (graph core0729) (root 7) 0 0) SmallGeFourSpectrum025.graph sourceMap0729=true := by decide +kernel
theorem fusedMap0729_checked : acceptsGraphIso
    (fused (graph core0729) (root 7) 0 0) SmallGeFourSpectrum026.graph fusedMap0729=true := by decide +kernel
theorem certified0729 : Certified (graph core0729) (root 7) 0 0 :=
  of_native_maps core0729 SmallGeFourSpectrum025.graph SmallGeFourSpectrum026.graph
    sourceMap0729 fusedMap0729 sourceMap0729_checked fusedMap0729_checked
    DegreeOneSmallComparisons.comparison0729
#print axioms sourceMap0729_checked
#print axioms fusedMap0729_checked
#print axioms certified0729
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
