/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2294 : Family 10 := level10.get ⟨927,by decide⟩
def sourceMap2294 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,9,10,11,12,1,2,3,4,5,7,8] (sourceLabel 10 0 0 v)
def fusedMap2294 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,9,10,11,12,1,2,3,4,5,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap2294_checked : acceptsGraphIso
    (source (graph core2294) (root 10) 0 0) DegreeOneSmallSpectrum1039.graph sourceMap2294=true := by decide +kernel
theorem fusedMap2294_checked : acceptsGraphIso
    (fused (graph core2294) (root 10) 0 0) DegreeOneSmallSpectrum1038.graph fusedMap2294=true := by decide +kernel
theorem certified2294 : Certified (graph core2294) (root 10) 0 0 :=
  of_native_maps core2294 DegreeOneSmallSpectrum1039.graph DegreeOneSmallSpectrum1038.graph
    sourceMap2294 fusedMap2294 sourceMap2294_checked fusedMap2294_checked
    DegreeOneSmallComparisons.comparison2294
#print axioms sourceMap2294_checked
#print axioms fusedMap2294_checked
#print axioms certified2294
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
