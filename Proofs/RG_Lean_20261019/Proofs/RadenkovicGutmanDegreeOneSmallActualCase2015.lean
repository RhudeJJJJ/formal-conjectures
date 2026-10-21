/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2015 : Family 10 := level10.get ⟨356,by decide⟩
def sourceMap2015 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (sourceLabel 10 0 0 v)
def fusedMap2015 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2015_checked : acceptsGraphIso
    (source (graph core2015) (root 10) 0 0) DegreeOneSmallSpectrum1086.graph sourceMap2015=true := by decide +kernel
theorem fusedMap2015_checked : acceptsGraphIso
    (fused (graph core2015) (root 10) 0 0) DegreeOneSmallSpectrum1442.graph fusedMap2015=true := by decide +kernel
theorem certified2015 : Certified (graph core2015) (root 10) 0 0 :=
  of_native_maps core2015 DegreeOneSmallSpectrum1086.graph DegreeOneSmallSpectrum1442.graph
    sourceMap2015 fusedMap2015 sourceMap2015_checked fusedMap2015_checked
    DegreeOneSmallComparisons.comparison2015
#print axioms sourceMap2015_checked
#print axioms fusedMap2015_checked
#print axioms certified2015
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
