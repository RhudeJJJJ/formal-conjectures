/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0894 : Family 8 := level8.get ⟨53,by decide⟩
def sourceMap0894 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (sourceLabel 8 1 1 v)
def fusedMap0894 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0894_checked : acceptsGraphIso
    (source (graph core0894) (root 8) 1 1) DegreeOneSmallSpectrum1307.graph sourceMap0894=true := by decide +kernel
theorem fusedMap0894_checked : acceptsGraphIso
    (fused (graph core0894) (root 8) 1 1) DegreeOneSmallSpectrum909.graph fusedMap0894=true := by decide +kernel
theorem certified0894 : Certified (graph core0894) (root 8) 1 1 :=
  of_native_maps core0894 DegreeOneSmallSpectrum1307.graph DegreeOneSmallSpectrum909.graph
    sourceMap0894 fusedMap0894 sourceMap0894_checked fusedMap0894_checked
    DegreeOneSmallComparisons.comparison0894
#print axioms sourceMap0894_checked
#print axioms fusedMap0894_checked
#print axioms certified0894
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
