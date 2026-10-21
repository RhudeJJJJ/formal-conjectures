/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0663 : Family 7 := level7.get ⟨54,by decide⟩
def sourceMap0663 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,7,8,9,4,5,6,2,3] (sourceLabel 7 0 0 v)
def fusedMap0663 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![1,0,4,5,6,7,8,9,2,3] (fusedLabel 7 0 0 v)
theorem sourceMap0663_checked : acceptsGraphIso
    (source (graph core0663) (root 7) 0 0) SmallGeFourSpectrum017.graph sourceMap0663=true := by decide +kernel
theorem fusedMap0663_checked : acceptsGraphIso
    (fused (graph core0663) (root 7) 0 0) SmallGeFourSpectrum023.graph fusedMap0663=true := by decide +kernel
theorem certified0663 : Certified (graph core0663) (root 7) 0 0 :=
  of_native_maps core0663 SmallGeFourSpectrum017.graph SmallGeFourSpectrum023.graph
    sourceMap0663 fusedMap0663 sourceMap0663_checked fusedMap0663_checked
    DegreeOneSmallComparisons.comparison0663
#print axioms sourceMap0663_checked
#print axioms fusedMap0663_checked
#print axioms certified0663
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
