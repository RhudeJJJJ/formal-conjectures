/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2477 : Family 10 := level10.get ⟨1625,by decide⟩
def sourceMap2477 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,12,2,3] (sourceLabel 10 0 0 v)
def fusedMap2477 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2477_checked : acceptsGraphIso
    (source (graph core2477) (root 10) 0 0) DegreeOneSmallSpectrum2012.graph sourceMap2477=true := by decide +kernel
theorem fusedMap2477_checked : acceptsGraphIso
    (fused (graph core2477) (root 10) 0 0) DegreeOneSmallSpectrum1723.graph fusedMap2477=true := by decide +kernel
theorem certified2477 : Certified (graph core2477) (root 10) 0 0 :=
  of_native_maps core2477 DegreeOneSmallSpectrum2012.graph DegreeOneSmallSpectrum1723.graph
    sourceMap2477 fusedMap2477 sourceMap2477_checked fusedMap2477_checked
    DegreeOneSmallComparisons.comparison2477
#print axioms sourceMap2477_checked
#print axioms fusedMap2477_checked
#print axioms certified2477
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
