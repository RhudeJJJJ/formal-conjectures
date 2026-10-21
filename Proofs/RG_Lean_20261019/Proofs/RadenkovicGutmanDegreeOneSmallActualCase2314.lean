/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2314 : Family 10 := level10.get ⟨1001,by decide⟩
def sourceMap2314 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap2314 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2314_checked : acceptsGraphIso
    (source (graph core2314) (root 10) 0 0) DegreeOneSmallSpectrum1541.graph sourceMap2314=true := by decide +kernel
theorem fusedMap2314_checked : acceptsGraphIso
    (fused (graph core2314) (root 10) 0 0) DegreeOneSmallSpectrum1545.graph fusedMap2314=true := by decide +kernel
theorem certified2314 : Certified (graph core2314) (root 10) 0 0 :=
  of_native_maps core2314 DegreeOneSmallSpectrum1541.graph DegreeOneSmallSpectrum1545.graph
    sourceMap2314 fusedMap2314 sourceMap2314_checked fusedMap2314_checked
    DegreeOneSmallComparisons.comparison2314
#print axioms sourceMap2314_checked
#print axioms fusedMap2314_checked
#print axioms certified2314
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
