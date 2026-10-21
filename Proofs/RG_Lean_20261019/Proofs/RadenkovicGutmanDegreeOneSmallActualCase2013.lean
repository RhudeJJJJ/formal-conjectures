/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2013 : Family 10 := level10.get ⟨351,by decide⟩
def sourceMap2013 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,7,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap2013 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,12,10,11,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2013_checked : acceptsGraphIso
    (source (graph core2013) (root 10) 0 0) DegreeOneSmallSpectrum1122.graph sourceMap2013=true := by decide +kernel
theorem fusedMap2013_checked : acceptsGraphIso
    (fused (graph core2013) (root 10) 0 0) DegreeOneSmallSpectrum1449.graph fusedMap2013=true := by decide +kernel
theorem certified2013 : Certified (graph core2013) (root 10) 0 0 :=
  of_native_maps core2013 DegreeOneSmallSpectrum1122.graph DegreeOneSmallSpectrum1449.graph
    sourceMap2013 fusedMap2013 sourceMap2013_checked fusedMap2013_checked
    DegreeOneSmallComparisons.comparison2013
#print axioms sourceMap2013_checked
#print axioms fusedMap2013_checked
#print axioms certified2013
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
