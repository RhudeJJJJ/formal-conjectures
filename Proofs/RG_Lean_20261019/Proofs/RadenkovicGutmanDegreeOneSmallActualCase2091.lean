/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2091 : Family 10 := level10.get ⟨505,by decide⟩
def sourceMap2091 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap2091 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2091_checked : acceptsGraphIso
    (source (graph core2091) (root 10) 0 0) DegreeOneSmallSpectrum1580.graph sourceMap2091=true := by decide +kernel
theorem fusedMap2091_checked : acceptsGraphIso
    (fused (graph core2091) (root 10) 0 0) DegreeOneSmallSpectrum991.graph fusedMap2091=true := by decide +kernel
theorem certified2091 : Certified (graph core2091) (root 10) 0 0 :=
  of_native_maps core2091 DegreeOneSmallSpectrum1580.graph DegreeOneSmallSpectrum991.graph
    sourceMap2091 fusedMap2091 sourceMap2091_checked fusedMap2091_checked
    DegreeOneSmallComparisons.comparison2091
#print axioms sourceMap2091_checked
#print axioms fusedMap2091_checked
#print axioms certified2091
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
