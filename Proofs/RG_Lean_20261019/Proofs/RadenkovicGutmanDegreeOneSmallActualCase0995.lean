/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0995 : Family 8 := level8.get ⟨99,by decide⟩
def sourceMap0995 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10] (sourceLabel 8 0 0 v)
def fusedMap0995 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0995_checked : acceptsGraphIso
    (source (graph core0995) (root 8) 0 0) DegreeOneSmallSpectrum247.graph sourceMap0995=true := by decide +kernel
theorem fusedMap0995_checked : acceptsGraphIso
    (fused (graph core0995) (root 8) 0 0) DegreeOneSmallSpectrum249.graph fusedMap0995=true := by decide +kernel
theorem certified0995 : Certified (graph core0995) (root 8) 0 0 :=
  of_native_maps core0995 DegreeOneSmallSpectrum247.graph DegreeOneSmallSpectrum249.graph
    sourceMap0995 fusedMap0995 sourceMap0995_checked fusedMap0995_checked
    DegreeOneSmallComparisons.comparison0995
#print axioms sourceMap0995_checked
#print axioms fusedMap0995_checked
#print axioms certified0995
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
