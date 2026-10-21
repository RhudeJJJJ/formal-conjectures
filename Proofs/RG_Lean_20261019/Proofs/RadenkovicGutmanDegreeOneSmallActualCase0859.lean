/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0859 : Family 8 := level8.get ⟨40,by decide⟩
def sourceMap0859 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10] (sourceLabel 8 0 0 v)
def fusedMap0859 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0859_checked : acceptsGraphIso
    (source (graph core0859) (root 8) 0 0) DegreeOneSmallSpectrum287.graph sourceMap0859=true := by decide +kernel
theorem fusedMap0859_checked : acceptsGraphIso
    (fused (graph core0859) (root 8) 0 0) DegreeOneSmallSpectrum177.graph fusedMap0859=true := by decide +kernel
theorem certified0859 : Certified (graph core0859) (root 8) 0 0 :=
  of_native_maps core0859 DegreeOneSmallSpectrum287.graph DegreeOneSmallSpectrum177.graph
    sourceMap0859 fusedMap0859 sourceMap0859_checked fusedMap0859_checked
    DegreeOneSmallComparisons.comparison0859
#print axioms sourceMap0859_checked
#print axioms fusedMap0859_checked
#print axioms certified0859
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
