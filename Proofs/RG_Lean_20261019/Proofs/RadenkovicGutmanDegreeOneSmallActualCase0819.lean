/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0819 : Family 8 := level8.get ⟨25,by decide⟩
def sourceMap0819 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,7,8,9,10,5,6,3,4] (sourceLabel 8 0 0 v)
def fusedMap0819 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![2,1,0,5,6,7,8,9,10,3,4] (fusedLabel 8 0 0 v)
theorem sourceMap0819_checked : acceptsGraphIso
    (source (graph core0819) (root 8) 0 0) DegreeOneSmallSpectrum183.graph sourceMap0819=true := by decide +kernel
theorem fusedMap0819_checked : acceptsGraphIso
    (fused (graph core0819) (root 8) 0 0) DegreeOneSmallSpectrum228.graph fusedMap0819=true := by decide +kernel
theorem certified0819 : Certified (graph core0819) (root 8) 0 0 :=
  of_native_maps core0819 DegreeOneSmallSpectrum183.graph DegreeOneSmallSpectrum228.graph
    sourceMap0819 fusedMap0819 sourceMap0819_checked fusedMap0819_checked
    DegreeOneSmallComparisons.comparison0819
#print axioms sourceMap0819_checked
#print axioms fusedMap0819_checked
#print axioms certified0819
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
