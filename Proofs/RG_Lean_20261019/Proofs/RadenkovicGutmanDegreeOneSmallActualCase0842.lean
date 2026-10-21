/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0842 : Family 8 := level8.get ⟨34,by decide⟩
def sourceMap0842 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (sourceLabel 8 1 1 v)
def fusedMap0842 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0842_checked : acceptsGraphIso
    (source (graph core0842) (root 8) 1 1) DegreeOneSmallSpectrum1002.graph sourceMap0842=true := by decide +kernel
theorem fusedMap0842_checked : acceptsGraphIso
    (fused (graph core0842) (root 8) 1 1) DegreeOneSmallSpectrum862.graph fusedMap0842=true := by decide +kernel
theorem certified0842 : Certified (graph core0842) (root 8) 1 1 :=
  of_native_maps core0842 DegreeOneSmallSpectrum1002.graph DegreeOneSmallSpectrum862.graph
    sourceMap0842 fusedMap0842 sourceMap0842_checked fusedMap0842_checked
    DegreeOneSmallComparisons.comparison0842
#print axioms sourceMap0842_checked
#print axioms fusedMap0842_checked
#print axioms certified0842
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
