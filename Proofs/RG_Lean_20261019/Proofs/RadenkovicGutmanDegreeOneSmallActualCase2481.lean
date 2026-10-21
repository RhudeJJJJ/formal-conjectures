/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2481 : Family 10 := level10.get ⟨1699,by decide⟩
def sourceMap2481 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,12,2,3] (sourceLabel 10 0 0 v)
def fusedMap2481 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2481_checked : acceptsGraphIso
    (source (graph core2481) (root 10) 0 0) DegreeOneSmallSpectrum2016.graph sourceMap2481=true := by decide +kernel
theorem fusedMap2481_checked : acceptsGraphIso
    (fused (graph core2481) (root 10) 0 0) DegreeOneSmallSpectrum1885.graph fusedMap2481=true := by decide +kernel
theorem certified2481 : Certified (graph core2481) (root 10) 0 0 :=
  of_native_maps core2481 DegreeOneSmallSpectrum2016.graph DegreeOneSmallSpectrum1885.graph
    sourceMap2481 fusedMap2481 sourceMap2481_checked fusedMap2481_checked
    DegreeOneSmallComparisons.comparison2481
#print axioms sourceMap2481_checked
#print axioms fusedMap2481_checked
#print axioms certified2481
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
