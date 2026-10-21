/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2479 : Family 10 := level10.get ⟨1630,by decide⟩
def sourceMap2479 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,12,2,3] (sourceLabel 10 0 0 v)
def fusedMap2479 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2479_checked : acceptsGraphIso
    (source (graph core2479) (root 10) 0 0) DegreeOneSmallSpectrum2014.graph sourceMap2479=true := by decide +kernel
theorem fusedMap2479_checked : acceptsGraphIso
    (fused (graph core2479) (root 10) 0 0) DegreeOneSmallSpectrum1734.graph fusedMap2479=true := by decide +kernel
theorem certified2479 : Certified (graph core2479) (root 10) 0 0 :=
  of_native_maps core2479 DegreeOneSmallSpectrum2014.graph DegreeOneSmallSpectrum1734.graph
    sourceMap2479 fusedMap2479 sourceMap2479_checked fusedMap2479_checked
    DegreeOneSmallComparisons.comparison2479
#print axioms sourceMap2479_checked
#print axioms fusedMap2479_checked
#print axioms certified2479
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
