/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0374 : Family 6 := level6.get ⟨14,by decide⟩
def sourceMap0374 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,7,8,9,10,11,12,1,2,3,4,5,6] (sourceLabel 6 2 2 v)
def fusedMap0374 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 2 2 v)
theorem sourceMap0374_checked : acceptsGraphIso
    (source (graph core0374) (root 6) 2 2) DegreeOneSmallSpectrum1460.graph sourceMap0374=true := by decide +kernel
theorem fusedMap0374_checked : acceptsGraphIso
    (fused (graph core0374) (root 6) 2 2) DegreeOneSmallSpectrum951.graph fusedMap0374=true := by decide +kernel
theorem certified0374 : Certified (graph core0374) (root 6) 2 2 :=
  of_native_maps core0374 DegreeOneSmallSpectrum1460.graph DegreeOneSmallSpectrum951.graph
    sourceMap0374 fusedMap0374 sourceMap0374_checked fusedMap0374_checked
    DegreeOneSmallComparisons.comparison0374
#print axioms sourceMap0374_checked
#print axioms fusedMap0374_checked
#print axioms certified0374
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
