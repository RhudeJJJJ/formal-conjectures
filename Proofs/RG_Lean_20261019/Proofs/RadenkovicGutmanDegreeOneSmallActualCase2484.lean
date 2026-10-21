/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2484 : Family 10 := level10.get ⟨1736,by decide⟩
def sourceMap2484 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,12,2,3] (sourceLabel 10 0 0 v)
def fusedMap2484 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2484_checked : acceptsGraphIso
    (source (graph core2484) (root 10) 0 0) DegreeOneSmallSpectrum2019.graph sourceMap2484=true := by decide +kernel
theorem fusedMap2484_checked : acceptsGraphIso
    (fused (graph core2484) (root 10) 0 0) DegreeOneSmallSpectrum1932.graph fusedMap2484=true := by decide +kernel
theorem certified2484 : Certified (graph core2484) (root 10) 0 0 :=
  of_native_maps core2484 DegreeOneSmallSpectrum2019.graph DegreeOneSmallSpectrum1932.graph
    sourceMap2484 fusedMap2484 sourceMap2484_checked fusedMap2484_checked
    DegreeOneSmallComparisons.comparison2484
#print axioms sourceMap2484_checked
#print axioms fusedMap2484_checked
#print axioms certified2484
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
