/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0999 : Family 8 := level8.get ⟨100,by decide⟩
def sourceMap0999 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10] (sourceLabel 8 0 0 v)
def fusedMap0999 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0999_checked : acceptsGraphIso
    (source (graph core0999) (root 8) 0 0) DegreeOneSmallSpectrum251.graph sourceMap0999=true := by decide +kernel
theorem fusedMap0999_checked : acceptsGraphIso
    (fused (graph core0999) (root 8) 0 0) DegreeOneSmallSpectrum253.graph fusedMap0999=true := by decide +kernel
theorem certified0999 : Certified (graph core0999) (root 8) 0 0 :=
  of_native_maps core0999 DegreeOneSmallSpectrum251.graph DegreeOneSmallSpectrum253.graph
    sourceMap0999 fusedMap0999 sourceMap0999_checked fusedMap0999_checked
    DegreeOneSmallComparisons.comparison0999
#print axioms sourceMap0999_checked
#print axioms fusedMap0999_checked
#print axioms certified0999
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
