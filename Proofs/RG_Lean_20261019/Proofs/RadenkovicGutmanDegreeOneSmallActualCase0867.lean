/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0867 : Family 8 := level8.get ⟨42,by decide⟩
def sourceMap0867 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,6,7,8,9,10,5,3,4] (sourceLabel 8 0 0 v)
def fusedMap0867 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap0867_checked : acceptsGraphIso
    (source (graph core0867) (root 8) 0 0) DegreeOneSmallSpectrum292.graph sourceMap0867=true := by decide +kernel
theorem fusedMap0867_checked : acceptsGraphIso
    (fused (graph core0867) (root 8) 0 0) DegreeOneSmallSpectrum181.graph fusedMap0867=true := by decide +kernel
theorem certified0867 : Certified (graph core0867) (root 8) 0 0 :=
  of_native_maps core0867 DegreeOneSmallSpectrum292.graph DegreeOneSmallSpectrum181.graph
    sourceMap0867 fusedMap0867 sourceMap0867_checked fusedMap0867_checked
    DegreeOneSmallComparisons.comparison0867
#print axioms sourceMap0867_checked
#print axioms fusedMap0867_checked
#print axioms certified0867
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
