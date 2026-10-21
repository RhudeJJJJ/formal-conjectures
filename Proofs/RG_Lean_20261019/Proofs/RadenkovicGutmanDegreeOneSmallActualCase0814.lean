/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0814 : Family 8 := level8.get ⟨22,by decide⟩
def sourceMap0814 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,3,4,5,6] (sourceLabel 8 1 1 v)
def fusedMap0814 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0814_checked : acceptsGraphIso
    (source (graph core0814) (root 8) 1 1) DegreeOneSmallSpectrum1346.graph sourceMap0814=true := by decide +kernel
theorem fusedMap0814_checked : acceptsGraphIso
    (fused (graph core0814) (root 8) 1 1) DegreeOneSmallSpectrum961.graph fusedMap0814=true := by decide +kernel
theorem certified0814 : Certified (graph core0814) (root 8) 1 1 :=
  of_native_maps core0814 DegreeOneSmallSpectrum1346.graph DegreeOneSmallSpectrum961.graph
    sourceMap0814 fusedMap0814 sourceMap0814_checked fusedMap0814_checked
    DegreeOneSmallComparisons.comparison0814
#print axioms sourceMap0814_checked
#print axioms fusedMap0814_checked
#print axioms certified0814
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
