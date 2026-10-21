/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0281 : Family 6 := level6.get ⟨1,by decide⟩
def sourceMap0281 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 2) → Fin 11 :=
  fun v => ![6,5,0,1,2,3,4,7,8,9,10] (sourceLabel 6 1 1 v)
def fusedMap0281 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (fusedLabel 6 1 1 v)
theorem sourceMap0281_checked : acceptsGraphIso
    (source (graph core0281) (root 6) 1 1) DegreeOneSmallSpectrum190.graph sourceMap0281=true := by decide +kernel
theorem fusedMap0281_checked : acceptsGraphIso
    (fused (graph core0281) (root 6) 1 1) DegreeOneSmallSpectrum164.graph fusedMap0281=true := by decide +kernel
theorem certified0281 : Certified (graph core0281) (root 6) 1 1 :=
  of_native_maps core0281 DegreeOneSmallSpectrum190.graph DegreeOneSmallSpectrum164.graph
    sourceMap0281 fusedMap0281 sourceMap0281_checked fusedMap0281_checked
    DegreeOneSmallComparisons.comparison0281
#print axioms sourceMap0281_checked
#print axioms fusedMap0281_checked
#print axioms certified0281
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
