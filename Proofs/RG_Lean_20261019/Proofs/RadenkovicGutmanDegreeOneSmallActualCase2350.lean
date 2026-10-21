/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2350 : Family 10 := level10.get ⟨1073,by decide⟩
def sourceMap2350 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,5,0,1,2,3,4,9,10,11,12,7,8] (sourceLabel 10 0 0 v)
def fusedMap2350 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,9,10,11,12,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap2350_checked : acceptsGraphIso
    (source (graph core2350) (root 10) 0 0) DegreeOneSmallSpectrum1673.graph sourceMap2350=true := by decide +kernel
theorem fusedMap2350_checked : acceptsGraphIso
    (fused (graph core2350) (root 10) 0 0) DegreeOneSmallSpectrum1695.graph fusedMap2350=true := by decide +kernel
theorem certified2350 : Certified (graph core2350) (root 10) 0 0 :=
  of_native_maps core2350 DegreeOneSmallSpectrum1673.graph DegreeOneSmallSpectrum1695.graph
    sourceMap2350 fusedMap2350 sourceMap2350_checked fusedMap2350_checked
    DegreeOneSmallComparisons.comparison2350
#print axioms sourceMap2350_checked
#print axioms fusedMap2350_checked
#print axioms certified2350
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
