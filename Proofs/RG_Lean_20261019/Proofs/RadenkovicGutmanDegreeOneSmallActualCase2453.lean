/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2453 : Family 10 := level10.get ⟨1437,by decide⟩
def sourceMap2453 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,10,11,12,4,5,6,7,8,9,2,3] (sourceLabel 10 0 0 v)
def fusedMap2453 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,12,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap2453_checked : acceptsGraphIso
    (source (graph core2453) (root 10) 0 0) DegreeOneSmallSpectrum1724.graph sourceMap2453=true := by decide +kernel
theorem fusedMap2453_checked : acceptsGraphIso
    (fused (graph core2453) (root 10) 0 0) DegreeOneSmallSpectrum1984.graph fusedMap2453=true := by decide +kernel
theorem certified2453 : Certified (graph core2453) (root 10) 0 0 :=
  of_native_maps core2453 DegreeOneSmallSpectrum1724.graph DegreeOneSmallSpectrum1984.graph
    sourceMap2453 fusedMap2453 sourceMap2453_checked fusedMap2453_checked
    DegreeOneSmallComparisons.comparison2453
#print axioms sourceMap2453_checked
#print axioms fusedMap2453_checked
#print axioms certified2453
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
