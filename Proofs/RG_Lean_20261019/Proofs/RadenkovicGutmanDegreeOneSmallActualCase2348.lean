/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2348 : Family 10 := level10.get ⟨1070,by decide⟩
def sourceMap2348 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,5,0,1,2,3,4,9,10,11,12,7,8] (sourceLabel 10 0 0 v)
def fusedMap2348 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,12,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap2348_checked : acceptsGraphIso
    (source (graph core2348) (root 10) 0 0) DegreeOneSmallSpectrum1670.graph sourceMap2348=true := by decide +kernel
theorem fusedMap2348_checked : acceptsGraphIso
    (fused (graph core2348) (root 10) 0 0) DegreeOneSmallSpectrum1693.graph fusedMap2348=true := by decide +kernel
theorem certified2348 : Certified (graph core2348) (root 10) 0 0 :=
  of_native_maps core2348 DegreeOneSmallSpectrum1670.graph DegreeOneSmallSpectrum1693.graph
    sourceMap2348 fusedMap2348 sourceMap2348_checked fusedMap2348_checked
    DegreeOneSmallComparisons.comparison2348
#print axioms sourceMap2348_checked
#print axioms fusedMap2348_checked
#print axioms certified2348
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
