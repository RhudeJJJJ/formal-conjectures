/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2454 : Family 10 := level10.get ⟨1441,by decide⟩
def sourceMap2454 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,10,11,12,4,5,6,7,8,9,2,3] (sourceLabel 10 0 0 v)
def fusedMap2454 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,12,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap2454_checked : acceptsGraphIso
    (source (graph core2454) (root 10) 0 0) DegreeOneSmallSpectrum1734.graph sourceMap2454=true := by decide +kernel
theorem fusedMap2454_checked : acceptsGraphIso
    (fused (graph core2454) (root 10) 0 0) DegreeOneSmallSpectrum1985.graph fusedMap2454=true := by decide +kernel
theorem certified2454 : Certified (graph core2454) (root 10) 0 0 :=
  of_native_maps core2454 DegreeOneSmallSpectrum1734.graph DegreeOneSmallSpectrum1985.graph
    sourceMap2454 fusedMap2454 sourceMap2454_checked fusedMap2454_checked
    DegreeOneSmallComparisons.comparison2454
#print axioms sourceMap2454_checked
#print axioms fusedMap2454_checked
#print axioms certified2454
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
