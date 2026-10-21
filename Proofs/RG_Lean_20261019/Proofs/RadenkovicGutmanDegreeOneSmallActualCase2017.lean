/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2017 : Family 10 := level10.get ⟨359,by decide⟩
def sourceMap2017 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (sourceLabel 10 0 0 v)
def fusedMap2017 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2017_checked : acceptsGraphIso
    (source (graph core2017) (root 10) 0 0) DegreeOneSmallSpectrum1116.graph sourceMap2017=true := by decide +kernel
theorem fusedMap2017_checked : acceptsGraphIso
    (fused (graph core2017) (root 10) 0 0) DegreeOneSmallSpectrum1448.graph fusedMap2017=true := by decide +kernel
theorem certified2017 : Certified (graph core2017) (root 10) 0 0 :=
  of_native_maps core2017 DegreeOneSmallSpectrum1116.graph DegreeOneSmallSpectrum1448.graph
    sourceMap2017 fusedMap2017 sourceMap2017_checked fusedMap2017_checked
    DegreeOneSmallComparisons.comparison2017
#print axioms sourceMap2017_checked
#print axioms fusedMap2017_checked
#print axioms certified2017
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
