/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2346 : Family 10 := level10.get ⟨1067,by decide⟩
def sourceMap2346 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap2346 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,12,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap2346_checked : acceptsGraphIso
    (source (graph core2346) (root 10) 0 0) DegreeOneSmallSpectrum1693.graph sourceMap2346=true := by decide +kernel
theorem fusedMap2346_checked : acceptsGraphIso
    (fused (graph core2346) (root 10) 0 0) DegreeOneSmallSpectrum1691.graph fusedMap2346=true := by decide +kernel
theorem certified2346 : Certified (graph core2346) (root 10) 0 0 :=
  of_native_maps core2346 DegreeOneSmallSpectrum1693.graph DegreeOneSmallSpectrum1691.graph
    sourceMap2346 fusedMap2346 sourceMap2346_checked fusedMap2346_checked
    DegreeOneSmallComparisons.comparison2346
#print axioms sourceMap2346_checked
#print axioms fusedMap2346_checked
#print axioms certified2346
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
