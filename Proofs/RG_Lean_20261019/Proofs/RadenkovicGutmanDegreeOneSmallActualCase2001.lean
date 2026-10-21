/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2001 : Family 10 := level10.get ⟨333,by decide⟩
def sourceMap2001 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap2001 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2001_checked : acceptsGraphIso
    (source (graph core2001) (root 10) 0 0) DegreeOneSmallSpectrum1206.graph sourceMap2001=true := by decide +kernel
theorem fusedMap2001_checked : acceptsGraphIso
    (fused (graph core2001) (root 10) 0 0) DegreeOneSmallSpectrum1434.graph fusedMap2001=true := by decide +kernel
theorem certified2001 : Certified (graph core2001) (root 10) 0 0 :=
  of_native_maps core2001 DegreeOneSmallSpectrum1206.graph DegreeOneSmallSpectrum1434.graph
    sourceMap2001 fusedMap2001 sourceMap2001_checked fusedMap2001_checked
    DegreeOneSmallComparisons.comparison2001
#print axioms sourceMap2001_checked
#print axioms fusedMap2001_checked
#print axioms certified2001
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
