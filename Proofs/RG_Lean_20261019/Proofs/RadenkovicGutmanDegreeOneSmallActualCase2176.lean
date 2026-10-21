/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2176 : Family 10 := level10.get ⟨656,by decide⟩
def sourceMap2176 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,5,0,1,2,3,4,6,7,8,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap2176 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,5,0,1,2,3,4,9,10,11,12,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap2176_checked : acceptsGraphIso
    (source (graph core2176) (root 10) 0 0) DegreeOneSmallSpectrum1277.graph sourceMap2176=true := by decide +kernel
theorem fusedMap2176_checked : acceptsGraphIso
    (fused (graph core2176) (root 10) 0 0) DegreeOneSmallSpectrum1274.graph fusedMap2176=true := by decide +kernel
theorem certified2176 : Certified (graph core2176) (root 10) 0 0 :=
  of_native_maps core2176 DegreeOneSmallSpectrum1277.graph DegreeOneSmallSpectrum1274.graph
    sourceMap2176 fusedMap2176 sourceMap2176_checked fusedMap2176_checked
    DegreeOneSmallComparisons.comparison2176
#print axioms sourceMap2176_checked
#print axioms fusedMap2176_checked
#print axioms certified2176
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
