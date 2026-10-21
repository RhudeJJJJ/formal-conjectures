/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2005 : Family 10 := level10.get ⟨338,by decide⟩
def sourceMap2005 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap2005 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2005_checked : acceptsGraphIso
    (source (graph core2005) (root 10) 0 0) DegreeOneSmallSpectrum1130.graph sourceMap2005=true := by decide +kernel
theorem fusedMap2005_checked : acceptsGraphIso
    (fused (graph core2005) (root 10) 0 0) DegreeOneSmallSpectrum1432.graph fusedMap2005=true := by decide +kernel
theorem certified2005 : Certified (graph core2005) (root 10) 0 0 :=
  of_native_maps core2005 DegreeOneSmallSpectrum1130.graph DegreeOneSmallSpectrum1432.graph
    sourceMap2005 fusedMap2005 sourceMap2005_checked fusedMap2005_checked
    DegreeOneSmallComparisons.comparison2005
#print axioms sourceMap2005_checked
#print axioms fusedMap2005_checked
#print axioms certified2005
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
