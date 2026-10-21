/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0899 : Family 8 := level8.get ⟨55,by decide⟩
def sourceMap0899 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,6,7,8,9,10,5,3,4] (sourceLabel 8 0 0 v)
def fusedMap0899 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap0899_checked : acceptsGraphIso
    (source (graph core0899) (root 8) 0 0) DegreeOneSmallSpectrum295.graph sourceMap0899=true := by decide +kernel
theorem fusedMap0899_checked : acceptsGraphIso
    (fused (graph core0899) (root 8) 0 0) DegreeOneSmallSpectrum201.graph fusedMap0899=true := by decide +kernel
theorem certified0899 : Certified (graph core0899) (root 8) 0 0 :=
  of_native_maps core0899 DegreeOneSmallSpectrum295.graph DegreeOneSmallSpectrum201.graph
    sourceMap0899 fusedMap0899 sourceMap0899_checked fusedMap0899_checked
    DegreeOneSmallComparisons.comparison0899
#print axioms sourceMap0899_checked
#print axioms fusedMap0899_checked
#print axioms certified0899
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
