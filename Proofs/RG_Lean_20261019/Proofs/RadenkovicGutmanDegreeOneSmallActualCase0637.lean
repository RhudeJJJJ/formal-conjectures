/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0637 : Family 7 := level7.get ⟨45,by decide⟩
def sourceMap0637 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (sourceLabel 7 1 1 v)
def fusedMap0637 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap0637_checked : acceptsGraphIso
    (source (graph core0637) (root 7) 1 1) DegreeOneSmallSpectrum792.graph sourceMap0637=true := by decide +kernel
theorem fusedMap0637_checked : acceptsGraphIso
    (fused (graph core0637) (root 7) 1 1) DegreeOneSmallSpectrum540.graph fusedMap0637=true := by decide +kernel
theorem certified0637 : Certified (graph core0637) (root 7) 1 1 :=
  of_native_maps core0637 DegreeOneSmallSpectrum792.graph DegreeOneSmallSpectrum540.graph
    sourceMap0637 fusedMap0637 sourceMap0637_checked fusedMap0637_checked
    DegreeOneSmallComparisons.comparison0637
#print axioms sourceMap0637_checked
#print axioms fusedMap0637_checked
#print axioms certified0637
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
