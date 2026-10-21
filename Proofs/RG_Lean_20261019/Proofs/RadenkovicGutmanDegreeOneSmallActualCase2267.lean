/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2267 : Family 10 := level10.get ⟨853,by decide⟩
def sourceMap2267 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap2267 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2267_checked : acceptsGraphIso
    (source (graph core2267) (root 10) 0 0) DegreeOneSmallSpectrum1836.graph sourceMap2267=true := by decide +kernel
theorem fusedMap2267_checked : acceptsGraphIso
    (fused (graph core2267) (root 10) 0 0) DegreeOneSmallSpectrum1477.graph fusedMap2267=true := by decide +kernel
theorem certified2267 : Certified (graph core2267) (root 10) 0 0 :=
  of_native_maps core2267 DegreeOneSmallSpectrum1836.graph DegreeOneSmallSpectrum1477.graph
    sourceMap2267 fusedMap2267 sourceMap2267_checked fusedMap2267_checked
    DegreeOneSmallComparisons.comparison2267
#print axioms sourceMap2267_checked
#print axioms fusedMap2267_checked
#print axioms certified2267
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
