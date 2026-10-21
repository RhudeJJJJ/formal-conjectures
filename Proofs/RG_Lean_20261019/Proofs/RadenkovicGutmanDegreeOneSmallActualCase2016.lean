/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2016 : Family 10 := level10.get ⟨357,by decide⟩
def sourceMap2016 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (sourceLabel 10 0 0 v)
def fusedMap2016 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2016_checked : acceptsGraphIso
    (source (graph core2016) (root 10) 0 0) DegreeOneSmallSpectrum1093.graph sourceMap2016=true := by decide +kernel
theorem fusedMap2016_checked : acceptsGraphIso
    (fused (graph core2016) (root 10) 0 0) DegreeOneSmallSpectrum1445.graph fusedMap2016=true := by decide +kernel
theorem certified2016 : Certified (graph core2016) (root 10) 0 0 :=
  of_native_maps core2016 DegreeOneSmallSpectrum1093.graph DegreeOneSmallSpectrum1445.graph
    sourceMap2016 fusedMap2016 sourceMap2016_checked fusedMap2016_checked
    DegreeOneSmallComparisons.comparison2016
#print axioms sourceMap2016_checked
#print axioms fusedMap2016_checked
#print axioms certified2016
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
