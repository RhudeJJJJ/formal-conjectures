/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0374 : Family 9 := level9.get ⟨609,by decide⟩
def sourceMap0374 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0374 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0374_checked : acceptsGraphIso
    (source (graph core0374) (root 9) 0 0) DegreeOneSmallSpectrum740.graph sourceMap0374=true := by decide +kernel
theorem fusedMap0374_checked : acceptsGraphIso
    (fused (graph core0374) (root 9) 0 0) DegreeOneSmallSpectrum739.graph fusedMap0374=true := by decide +kernel
theorem certified0374 : Certified (graph core0374) (root 9) 0 0 :=
  of_native_maps core0374 DegreeOneSmallSpectrum740.graph DegreeOneSmallSpectrum739.graph
    sourceMap0374 fusedMap0374 sourceMap0374_checked fusedMap0374_checked
    DegreeTwoThreeFiniteComparisons.comparison0374
#print axioms sourceMap0374_checked
#print axioms fusedMap0374_checked
#print axioms certified0374
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
