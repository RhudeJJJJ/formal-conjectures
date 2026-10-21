/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2096 : Family 10 := level10.get ⟨512,by decide⟩
def sourceMap2096 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (sourceLabel 10 0 0 v)
def fusedMap2096 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2096_checked : acceptsGraphIso
    (source (graph core2096) (root 10) 0 0) DegreeOneSmallSpectrum1590.graph sourceMap2096=true := by decide +kernel
theorem fusedMap2096_checked : acceptsGraphIso
    (fused (graph core2096) (root 10) 0 0) DegreeOneSmallSpectrum1006.graph fusedMap2096=true := by decide +kernel
theorem certified2096 : Certified (graph core2096) (root 10) 0 0 :=
  of_native_maps core2096 DegreeOneSmallSpectrum1590.graph DegreeOneSmallSpectrum1006.graph
    sourceMap2096 fusedMap2096 sourceMap2096_checked fusedMap2096_checked
    DegreeOneSmallComparisons.comparison2096
#print axioms sourceMap2096_checked
#print axioms fusedMap2096_checked
#print axioms certified2096
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
