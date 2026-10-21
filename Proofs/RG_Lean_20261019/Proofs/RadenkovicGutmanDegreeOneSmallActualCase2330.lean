/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2330 : Family 10 := level10.get ⟨1034,by decide⟩
def sourceMap2330 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap2330 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2330_checked : acceptsGraphIso
    (source (graph core2330) (root 10) 0 0) DegreeOneSmallSpectrum1611.graph sourceMap2330=true := by decide +kernel
theorem fusedMap2330_checked : acceptsGraphIso
    (fused (graph core2330) (root 10) 0 0) DegreeOneSmallSpectrum1616.graph fusedMap2330=true := by decide +kernel
theorem certified2330 : Certified (graph core2330) (root 10) 0 0 :=
  of_native_maps core2330 DegreeOneSmallSpectrum1611.graph DegreeOneSmallSpectrum1616.graph
    sourceMap2330 fusedMap2330 sourceMap2330_checked fusedMap2330_checked
    DegreeOneSmallComparisons.comparison2330
#print axioms sourceMap2330_checked
#print axioms fusedMap2330_checked
#print axioms certified2330
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
