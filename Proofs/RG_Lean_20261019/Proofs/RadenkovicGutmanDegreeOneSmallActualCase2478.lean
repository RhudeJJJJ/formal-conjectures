/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2478 : Family 10 := level10.get ⟨1626,by decide⟩
def sourceMap2478 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,12,2,3] (sourceLabel 10 0 0 v)
def fusedMap2478 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2478_checked : acceptsGraphIso
    (source (graph core2478) (root 10) 0 0) DegreeOneSmallSpectrum2013.graph sourceMap2478=true := by decide +kernel
theorem fusedMap2478_checked : acceptsGraphIso
    (fused (graph core2478) (root 10) 0 0) DegreeOneSmallSpectrum1724.graph fusedMap2478=true := by decide +kernel
theorem certified2478 : Certified (graph core2478) (root 10) 0 0 :=
  of_native_maps core2478 DegreeOneSmallSpectrum2013.graph DegreeOneSmallSpectrum1724.graph
    sourceMap2478 fusedMap2478 sourceMap2478_checked fusedMap2478_checked
    DegreeOneSmallComparisons.comparison2478
#print axioms sourceMap2478_checked
#print axioms fusedMap2478_checked
#print axioms certified2478
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
