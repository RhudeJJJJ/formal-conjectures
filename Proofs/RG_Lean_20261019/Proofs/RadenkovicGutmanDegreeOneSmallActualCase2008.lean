/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2008 : Family 10 := level10.get ⟨344,by decide⟩
def sourceMap2008 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (sourceLabel 10 0 0 v)
def fusedMap2008 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2008_checked : acceptsGraphIso
    (source (graph core2008) (root 10) 0 0) DegreeOneSmallSpectrum1199.graph sourceMap2008=true := by decide +kernel
theorem fusedMap2008_checked : acceptsGraphIso
    (fused (graph core2008) (root 10) 0 0) DegreeOneSmallSpectrum1454.graph fusedMap2008=true := by decide +kernel
theorem certified2008 : Certified (graph core2008) (root 10) 0 0 :=
  of_native_maps core2008 DegreeOneSmallSpectrum1199.graph DegreeOneSmallSpectrum1454.graph
    sourceMap2008 fusedMap2008 sourceMap2008_checked fusedMap2008_checked
    DegreeOneSmallComparisons.comparison2008
#print axioms sourceMap2008_checked
#print axioms fusedMap2008_checked
#print axioms certified2008
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
