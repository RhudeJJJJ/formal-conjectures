/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2014 : Family 10 := level10.get ⟨355,by decide⟩
def sourceMap2014 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,6,0,1,2,3,4,5,7,8,9,11,12] (sourceLabel 10 0 0 v)
def fusedMap2014 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2014_checked : acceptsGraphIso
    (source (graph core2014) (root 10) 0 0) DegreeOneSmallSpectrum1442.graph sourceMap2014=true := by decide +kernel
theorem fusedMap2014_checked : acceptsGraphIso
    (fused (graph core2014) (root 10) 0 0) DegreeOneSmallSpectrum1439.graph fusedMap2014=true := by decide +kernel
theorem certified2014 : Certified (graph core2014) (root 10) 0 0 :=
  of_native_maps core2014 DegreeOneSmallSpectrum1442.graph DegreeOneSmallSpectrum1439.graph
    sourceMap2014 fusedMap2014 sourceMap2014_checked fusedMap2014_checked
    DegreeOneSmallComparisons.comparison2014
#print axioms sourceMap2014_checked
#print axioms fusedMap2014_checked
#print axioms certified2014
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
